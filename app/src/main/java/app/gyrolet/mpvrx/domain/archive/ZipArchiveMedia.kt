/*
 * SPDX-License-Identifier: AGPL-3.0-or-later
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 */

package app.gyrolet.mpvrx.domain.archive

import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.media.MediaMetadataRetriever
import android.net.Uri
import android.os.Build
import android.os.Environment
import android.os.ParcelFileDescriptor
import android.os.Process
import android.provider.DocumentsContract
import android.provider.MediaStore
import android.provider.OpenableColumns
import android.system.ErrnoException
import android.system.Os
import android.system.OsConstants
import android.text.format.Formatter
import app.gyrolet.mpvrx.domain.browser.FileSystemItem
import app.gyrolet.mpvrx.domain.browser.PathComponent
import app.gyrolet.mpvrx.domain.media.model.Video
import app.gyrolet.mpvrx.domain.media.model.VideoFolder
import app.gyrolet.mpvrx.ui.player.resolveLocalPath
import app.gyrolet.mpvrx.utils.storage.FileTypeUtils
import java.io.File
import java.io.FileNotFoundException
import java.io.IOException
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import java.util.zip.ZipEntry
import java.util.zip.ZipFile
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.ensureActive
import kotlinx.coroutines.withContext

object ZipArchiveMedia {
  private const val BROWSER_SCHEME = "mpvrx-zip"
  private const val BROWSER_AUTHORITY = "local"
  private const val PLAYBACK_SCHEME = "archive"
  private const val MAX_ENTRIES = 100_000
  private const val MAX_CACHED_ENTRY_METADATA = 512
  private const val EXTERNAL_STORAGE_AUTHORITY = "com.android.externalstorage.documents"
  private const val DOWNLOADS_AUTHORITY = "com.android.providers.downloads.documents"
  private const val MEDIA_AUTHORITY = "com.android.providers.media.documents"

  data class Location(
    val archivePath: String,
    val directory: String,
  ) {
    /**
     * The entry path when this location was parsed from a playback URI: `parsePlaybackLocation()`
     * reuses [directory] for it, and [archivePath] for the archive.
     */
    val entryPath: String get() = directory
  }

  /** Duration and geometry of one archive entry, read out of the archive without extracting it. */
  data class EntryMetadata(
    val durationMs: Long,
    val width: Int,
    val height: Int,
    val fps: Float,
  )

  /**
   * Cache identity for an archive entry.
   *
   * The entry has no file on disk to key by, so [key] is the playback URI, and the archive's own
   * size and modification time invalidate the entry when the archive is replaced.
   */
  data class EntryCacheStamp(
    val key: String,
    val archiveSize: Long,
    val archiveModifiedSeconds: Long,
  )

  /** Playable contents of an archive, as stored by a read-only ZIP playlist. */
  data class PlaylistContent(
    val source: String,
    val name: String,
    val videos: List<Video>,
  )

  /**
   * A playable URI for one archive entry, plus the provider descriptor when the archive itself had
   * to be opened as a stream.
   */
  data class OpenedPlayback(
    val uri: String,
    val descriptor: ParcelFileDescriptor? = null,
  )

  private data class FolderStats(
    var videoCount: Int = 0,
    var totalSize: Long = 0L,
    var hasSubfolders: Boolean = false,
  )

  private data class ArchiveStats(
    var videoCount: Int = 0,
    var totalSize: Long = 0L,
    var hasSubfolders: Boolean = false,
  )

  private data class StatsKey(
    val path: String,
    val modified: Long,
    val length: Long,
    val includeAudio: Boolean,
  )

  private val statsCache = ConcurrentHashMap<StatsKey, ArchiveStats>()

  /** Memoizes entry metadata for the session, so a folder is only ever read once per entry. */
  private val entryMetadataCache = ConcurrentHashMap<String, EntryMetadata>()

  fun isZipFile(file: File): Boolean = file.isFile && file.extension.equals("zip", ignoreCase = true)

  /**
   * Resolves a picked ZIP to its real, readable location on storage.
   *
   * Archives are kept read-only in place: nothing is copied into app storage and no entry is
   * extracted to cache, so a 20 GB archive costs nothing beyond the file the user already has.
   *
   * A `content://` URI needs more than [resolveLocalPath] alone: the Downloads provider hands out
   * `msf:<id>` document IDs, which carry no path at all, so picking an archive that lives in
   * Downloads used to fail with "Cannot open ZIP archive". Those are resolved from the descriptor
   * the provider opens for us as a last resort. Returns null only when no readable filesystem path
   * exists (for example a cloud provider that streams on demand).
   */
  suspend fun resolveZipPath(
    context: Context,
    uri: Uri,
  ): String? =
    withContext(Dispatchers.IO) {
      try {
        resolveArchiveFile(context, uri)?.absolutePath
      } catch (cancelled: CancellationException) {
        throw cancelled
      } catch (_: Exception) {
        null
      }
    }

  /**
   * Candidates are tried in order and the first one that opens as a real ZIP wins, so a provider
   * that reports a path the app cannot actually read simply falls through to the next strategy.
   */
  private fun resolveArchiveFile(
    context: Context,
    uri: Uri,
  ): File? {
    val candidates = mutableListOf<File>()
    when (uri.scheme?.lowercase(Locale.ROOT)) {
      "file" -> uri.path?.let { candidates += File(it) }
      "content" -> {
        runCatching { uri.resolveLocalPath(context) }.getOrNull()?.let { candidates += File(it) }
        resolveDescriptorPath(context, uri)?.let { candidates += it }
      }
    }
    return candidates.firstOrNull { file -> file.isAbsolute && isZipFile(file) && isReadableZipArchive(file) }
  }

  /**
   * Runs [block] against a retriever whose data source streams the archive entry straight out of
   * the ZIP, so metadata and frames can be read without materializing the entry anywhere.
   *
   * Returns null when the entry cannot be opened or read.
   */
  internal suspend fun <T> withEntryRetriever(
    uri: Uri,
    block: (MediaMetadataRetriever) -> T,
  ): T? =
    withContext(Dispatchers.IO) {
      val location = parsePlaybackLocation(uri.toString()) ?: return@withContext null
      val archive = File(location.archivePath)
      if (!isZipFile(archive) || !archive.canRead()) return@withContext null

      val source =
        runCatching { ZipEntryMediaDataSource(archive, location.entryPath) }.getOrNull()
          ?: return@withContext null
      val retriever = MediaMetadataRetriever()
      try {
        retriever.setDataSource(source)
        runCatching { block(retriever) }.getOrNull()
      } catch (cancelled: CancellationException) {
        throw cancelled
      } catch (_: Exception) {
        null
      } finally {
        runCatching {
          if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) retriever.close() else retriever.release()
        }
        source.close()
      }
    }

  /** Cache identity for [uri], or null when it is not an archive entry. */
  fun entryCacheStamp(uri: Uri): EntryCacheStamp? =
    parsePlaybackLocation(uri.toString())?.let { location ->
      val archive = File(location.archivePath)
      EntryCacheStamp(
        key = uri.toString(),
        archiveSize = archive.length(),
        archiveModifiedSeconds = archive.lastModified() / 1000L,
      )
    }

  /**
   * Reads an entry's duration, resolution and frame rate by streaming it out of the archive.
   *
   * Nothing is written to disk, but a pass costs roughly one read of the entry, so results are
   * memoized for the session (and persisted by the callers' metadata cache).
   */
  suspend fun entryMetadata(
    stamp: EntryCacheStamp,
    uri: Uri,
  ): EntryMetadata? {
    val cacheKey = "${stamp.archiveModifiedSeconds}\u0000${stamp.archiveSize}\u0000${stamp.key}"
    entryMetadataCache[cacheKey]?.let { cached -> return cached }

    val metadata =
      withEntryRetriever(uri) { retriever ->
        EntryMetadata(
          durationMs =
            retriever
              .extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)
              ?.toLongOrNull()
              ?.coerceAtLeast(0L)
              ?: 0L,
          width =
            retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)?.toIntOrNull() ?: 0,
          height =
            retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)?.toIntOrNull() ?: 0,
          fps =
            retriever
              .extractMetadata(MediaMetadataRetriever.METADATA_KEY_CAPTURE_FRAMERATE)
              ?.toFloatOrNull()
              ?: 0f,
        )
      }

    if (metadata != null && metadata.durationMs > 0L) rememberEntryMetadata(cacheKey, metadata)
    return metadata
  }

  private fun rememberEntryMetadata(
    cacheKey: String,
    metadata: EntryMetadata,
  ) {
    if (entryMetadataCache.size >= MAX_CACHED_ENTRY_METADATA) {
      entryMetadataCache.keys.firstOrNull()?.let { oldest -> entryMetadataCache.remove(oldest) }
    }
    entryMetadataCache[cacheKey] = metadata
  }

  /**
   * Reads the real path back out of an open file descriptor.
   *
   * A document provider always opens the underlying file for us, so `/proc/self/fd` reveals where
   * it actually lives even when the document ID itself does not contain a path (Downloads'
   * `msf:<id>`). The descriptor is closed again immediately: nothing is copied and no cache is
   * written.
   */
  private fun resolveDescriptorPath(
    context: Context,
    uri: Uri,
  ): File? =
    runCatching {
      context.contentResolver.openFileDescriptor(uri, "r")?.use { descriptor ->
        Os
          .readlink("/proc/self/fd/${descriptor.fd}")
          ?.removeSuffix(" (deleted)")
          ?.takeIf { path -> path.startsWith('/') }
          ?.let { path -> File(path) }
      }
    }.getOrNull()

  /** Reads (and caches) the playable contents of an archive without extracting any entry. */
  /**
   * Reads the playable contents of an archive so it can be stored as a read-only playlist.
   *
   * Nothing is copied or extracted: [resolveZipPath] hands back the file the user already has, and
   * the playlist only remembers that path together with the entry names inside it.
   */
  suspend fun playlistContent(context: Context, uri: Uri): PlaylistContent = withContext(Dispatchers.IO) {
    val source = resolveZipPath(context, uri) ?: throw IOException("Cannot open a seekable ZIP source")
    readArchive(context, source) { archive ->
      require(archive.size() <= MAX_ENTRIES) { "ZIP archive has too many entries" }
    }
    val videos = allMedia(context, browserPath(source), includeAudio = true).getOrThrow()
      .distinctBy { it.path }
    currentCoroutineContext().ensureActive()
    require(videos.isNotEmpty()) { "ZIP archive contains no playable media" }
    PlaylistContent(source, archiveDisplayName(context, uri, File(source).takeIf { it.isAbsolute }), videos)
  }

  /**
   * Opens the archive for reading, straight off disk when the source is a path and straight from a
   * provider descriptor when it is a `content://` URI.
   */
  private fun <T> readArchive(context: Context, source: String, block: (ZipFile) -> T): T {
    if (source.startsWith("content://")) {
      return openDescriptor(context, Uri.parse(source)).use { descriptor ->
        ZipFile("/proc/self/fd/${descriptor.fd}").use(block)
      }
    }
    return ZipFile(source).use(block)
  }

  private fun openDescriptor(context: Context, uri: Uri): ParcelFileDescriptor {
    val descriptor =
      context.contentResolver.openFileDescriptor(uri, "r") ?: throw IOException("ZIP source is unavailable")
    try {
      Os.lseek(descriptor.fileDescriptor, 0L, OsConstants.SEEK_SET)
      return descriptor
    } catch (error: Exception) {
      descriptor.close()
      throw IOException("ZIP source must support seekable access", error)
    }
  }

  /** Turns a stored archive entry URI back into something mpv can play, without extracting it. */
  fun openPlayback(context: Context, value: String): OpenedPlayback {
    val location = parsePlaybackLocation(value) ?: throw IOException("Invalid ZIP entry")
    if (!location.archivePath.startsWith("content://")) {
      val file = File(location.archivePath)
      if (!file.isFile || !file.canRead()) throw IOException("ZIP source is unavailable")
      return OpenedPlayback(playbackUri(location.archivePath, location.entryPath))
    }
    val descriptor = openDescriptor(context, Uri.parse(location.archivePath))
    return try {
      OpenedPlayback(playbackUri("/proc/self/fd/${descriptor.fd}", location.entryPath), descriptor)
    } catch (error: Exception) {
      descriptor.close()
      throw error
    }
  }

  /** The archive an entry URI lives in, for playlist items backed by a ZIP. */
  fun sourceOf(value: String): String? = parsePlaybackLocation(value)?.archivePath

  /** The entry path inside the archive, without the `archive://` envelope. */
  fun entryPathOf(value: String): String? = parsePlaybackLocation(value)?.entryPath

  fun sourceAvailable(context: Context, source: String): Boolean = runCatching {
    if (source.startsWith("content://")) {
      openDescriptor(context, Uri.parse(source)).use { true }
    } else {
      File(source).let { it.isFile && it.canRead() }
    }
  }.getOrDefault(false)

  fun sourceDeleted(context: Context, source: String): Boolean {
    val mountedStates = setOf(Environment.MEDIA_MOUNTED, Environment.MEDIA_MOUNTED_READ_ONLY)
    if (!source.startsWith("content://")) {
      val file = File(source)
      val appOwned = file.absolutePath.startsWith(context.filesDir.absolutePath + File.separator)
      if (!appOwned && Environment.getExternalStorageState(file) !in mountedStates) return false
      return try {
        Os.stat(file.absolutePath)
        false
      } catch (error: ErrnoException) {
        error.errno == OsConstants.ENOENT
      }
    }

    val uri = Uri.parse(source)
    if (uri.authority == EXTERNAL_STORAGE_AUTHORITY) {
      val documentId = runCatching { DocumentsContract.getDocumentId(uri) }.getOrNull()
      val volumeId = documentId?.substringBefore(':')
      val relativePath = documentId?.substringAfter(':', "")?.let { normalizeEntryPath(it) }
      if (!relativePath.isNullOrBlank() && volumeId != null) {
        val volume = storageVolume(volumeId)
        if (volume != null) {
          val file = File(volume, relativePath)
          val ancestor = generateSequence(file.parentFile) { it.parentFile }.firstOrNull { it.exists() }
          if (ancestor?.canRead() == true && sourceDeleted(context, file.absolutePath)) return true
        }
      }
    }

    val readGranted =
      context.checkUriPermission(
        uri,
        Process.myPid(),
        Process.myUid(),
        Intent.FLAG_GRANT_READ_URI_PERMISSION,
      ) == PackageManager.PERMISSION_GRANTED
    if (!readGranted) return false

    val volumeFile = when {
      uri.authority == EXTERNAL_STORAGE_AUTHORITY -> {
        val documentId = runCatching { DocumentsContract.getDocumentId(uri) }.getOrNull() ?: return false
        storageVolume(documentId.substringBefore(':')) ?: return false
      }
      uri.authority == DOWNLOADS_AUTHORITY || uri.authority == MEDIA_AUTHORITY ->
        Environment.getExternalStorageDirectory()
      else -> return false
    }
    if (Environment.getExternalStorageState(volumeFile) !in mountedStates) return false
    return try {
      context.contentResolver.query(uri, arrayOf(DocumentsContract.Document.COLUMN_DOCUMENT_ID), null, null, null)
        ?.use { !it.moveToFirst() } ?: false
    } catch (_: FileNotFoundException) {
      true
    } catch (_: Exception) {
      false
    }
  }

  /** Maps a MediaStore volume id onto the directory it is mounted at, when that id is sane. */
  private fun storageVolume(volumeId: String): File? =
    when {
      volumeId == "primary" -> Environment.getExternalStorageDirectory()
      volumeId.matches(Regex("[A-Za-z0-9-]+")) -> File("/storage/$volumeId")
      else -> null
    }

  /**
   * Drops the cache folders older versions used for extracted archives, keeping whatever the entry
   * that is currently playing still needs.
   */
  fun clearLegacyCache(context: Context, activeUri: String? = null) {
    val activeSource = activeUri?.let { sourceOf(it) }
    val roots = listOf(context.cacheDir, context.filesDir) + context.externalCacheDirs.filterNotNull()
    for (root in roots.distinct()) {
      for (name in listOf("zip_archives", "zip_entries", "imported_zip_archives")) {
        val directory = File(root, name)
        if (activeSource?.startsWith(directory.absolutePath + File.separator) == true) continue
        if (directory.exists() && directory.canonicalFile.parentFile == root.canonicalFile) {
          directory.deleteRecursively()
        }
      }
    }
  }

  /** A display name for the archive, preferring what the provider reports over the file name. */
  private fun archiveDisplayName(
    context: Context,
    uri: Uri,
    localFile: File?,
  ): String {
    val providerName = runCatching {
      context.contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)?.use { cursor ->
        val nameColumn = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
        if (nameColumn >= 0 && cursor.moveToFirst()) cursor.getString(nameColumn) else null
      }
    }.getOrNull()
    val safeName =
      (providerName ?: localFile?.name)
        ?.substringAfterLast('/')
        ?.substringAfterLast('\\')
        ?.trim()
        ?.replace(Regex("[\\u0000-\\u001f\\u007f]"), "_")
        ?.take(120)
        ?.takeIf { it.isNotEmpty() && it != "." && it != ".." }
        ?: "archive"
    return if (safeName.endsWith(".zip", ignoreCase = true)) safeName else "$safeName.zip"
  }

  private fun inspectArchive(
    archive: File,
    includeAudio: Boolean,
  ): ArchiveStats =
    statsCache.getOrPut(StatsKey(archive.absolutePath, archive.lastModified(), archive.length(), includeAudio)) {
      ZipFile(archive).use { zip ->
        val stats = ArchiveStats()
        val entries = zip.entries()
        var entryCount = 0
        while (entries.hasMoreElements()) {
          if (++entryCount > MAX_ENTRIES) throw IOException("ZIP archive has too many entries")
          val entry = entries.nextElement()
          val path = normalizedEntryName(entry) ?: continue
          if (path.contains('/')) stats.hasSubfolders = true
          if (!entry.isDirectory && isPlayable(path, includeAudio)) {
            stats.videoCount++
            stats.totalSize += entry.size.coerceAtLeast(0L)
          }
        }
        stats
      }
    }

  /**
   * Builds a browsable folder for an archive the user added, reporting scan progress as the
   * entries are read. Returns null when the archive is missing or unreadable.
   */
  suspend fun registerArchive(
    archivePath: String,
    includeAudio: Boolean,
    onProgress: (scanned: Int, total: Int) -> Unit = { _, _ -> },
  ): VideoFolder? =
    withContext(Dispatchers.IO) {
      val archive = File(archivePath)
      if (!isZipFile(archive) || !archive.canRead()) return@withContext null

      try {
        ZipFile(archive).use { zip ->
          val total = zip.size().coerceAtLeast(0)
          val stats = ArchiveStats()
          val entries = zip.entries()
          var scanned = 0
          while (entries.hasMoreElements()) {
            currentCoroutineContext().ensureActive()
            scanned++
            if (scanned == total || scanned % 128 == 0) onProgress(scanned, total)
            val entry = entries.nextElement()
            val path = normalizedEntryName(entry) ?: continue
            if (path.contains('/')) stats.hasSubfolders = true
            if (!entry.isDirectory && isPlayable(path, includeAudio)) {
              stats.videoCount++
              stats.totalSize += entry.size.coerceAtLeast(0L)
            }
          }
          val bucketId = browserPath(archive.absolutePath)
          VideoFolder(
            bucketId = bucketId,
            name = archive.name,
            path = bucketId,
            videoCount = stats.videoCount,
            totalSize = stats.totalSize.takeIf { it > 0L } ?: archive.length(),
            totalDuration = 0L,
            lastModified = archive.lastModified() / 1000L,
          )
        }
      } catch (cancelled: CancellationException) {
        throw cancelled
      } catch (_: Exception) {
        null
      }
    }

  /** Folders for archives the user has added, so they stay available after a restart. */
  fun persistedFolders(
    archivePaths: Collection<String>,
    includeAudio: Boolean,
  ): List<VideoFolder> =
    archivePaths.mapNotNull { path ->
      val archive = File(path)
      if (!isZipFile(archive) || !archive.canRead()) return@mapNotNull null
      val stats = runCatching { inspectArchive(archive, includeAudio) }.getOrNull() ?: return@mapNotNull null
      val bucketId = browserPath(archive.absolutePath)
      VideoFolder(
        bucketId = bucketId,
        name = archive.name,
        path = bucketId,
        videoCount = stats.videoCount,
        totalSize = stats.totalSize.takeIf { it > 0L } ?: archive.length(),
        totalDuration = 0L,
        lastModified = archive.lastModified() / 1000L,
      )
    }

  private fun isReadableZipArchive(file: File): Boolean =
    file.isFile &&
      file.canRead() &&
      runCatching {
        ZipFile(file).use { archive -> archive.size() <= MAX_ENTRIES }
      }.getOrDefault(false)

  fun browserPath(
    archivePath: String,
    directory: String = "",
  ): String {
    val normalizedDirectory = normalizeEntryPath(directory).orEmpty()
    return Uri.Builder()
      .scheme(BROWSER_SCHEME)
      .authority(BROWSER_AUTHORITY)
      .appendQueryParameter("archive", File(archivePath).absolutePath)
      .appendQueryParameter("directory", normalizedDirectory)
      .build()
      .toString()
  }

  fun parseBrowserPath(value: String): Location? = runCatching {
    val uri = Uri.parse(value)
    if (!uri.scheme.equals(BROWSER_SCHEME, ignoreCase = true) || uri.authority != BROWSER_AUTHORITY) {
      return@runCatching null
    }
    val archivePath = uri.getQueryParameter("archive")?.takeIf { File(it).isAbsolute } ?: return@runCatching null
    val directory = normalizeEntryPath(uri.getQueryParameter("directory").orEmpty()) ?: return@runCatching null
    Location(File(archivePath).absolutePath, directory)
  }.getOrNull()

  fun isBrowserPath(value: String): Boolean = parseBrowserPath(value) != null

  fun isArchiveRoot(value: String): Boolean = parseBrowserPath(value)?.directory?.isEmpty() == true

  fun isPlaybackUri(value: String): Boolean = parsePlaybackLocation(value) != null

  private fun parsePlaybackLocation(value: String): Location? {
    val prefix = "$PLAYBACK_SCHEME://"
    if (!value.startsWith(prefix, ignoreCase = true)) return null
    val encodedLocation = value.substring(prefix.length)
    val separator = encodedLocation.indexOf('|')
    if (separator <= 0 || separator == encodedLocation.lastIndex) return null

    val archivePath = runCatching { Uri.decode(encodedLocation.substring(0, separator)) }.getOrNull() ?: return null
    if (!File(archivePath).isAbsolute) return null
    val entryPath = normalizeEntryPath(encodedLocation.substring(separator + 1))?.takeIf(String::isNotEmpty) ?: return null
    return Location(File(archivePath).absolutePath, entryPath)
  }

  fun displayPath(value: String): String? = parseBrowserPath(value)?.let { location ->
    buildString {
      append(location.archivePath)
      if (location.directory.isNotEmpty()) append("!/").append(location.directory)
    }
  }

  fun breadcrumbs(value: String): List<PathComponent> {
    val location = parseBrowserPath(value) ?: return emptyList()
    val archiveName = File(location.archivePath).name
    return buildList {
      add(PathComponent(archiveName, browserPath(location.archivePath)))
      var directory = ""
      location.directory.split('/').filter(String::isNotEmpty).forEach { segment ->
        directory = if (directory.isEmpty()) segment else "$directory/$segment"
        add(PathComponent(segment, browserPath(location.archivePath, directory)))
      }
    }
  }

  fun playbackUri(
    archivePath: String,
    entryPath: String,
  ): String {
    val entry = normalizeEntryPath(entryPath) ?: error("Unsafe ZIP entry path")
    require(entry.isNotEmpty()) { "ZIP entry path is empty" }
    val escapedArchivePath = File(archivePath).absolutePath
      .replace("%", "%25")
      .replace("|", "%7C")
    return "$PLAYBACK_SCHEME://$escapedArchivePath|$entry"
  }

  fun archiveFoldersIn(
    directory: File,
    includeAudio: Boolean,
  ): List<FileSystemItem.Folder> =
    directory.listFiles()
      ?.asSequence()
      ?.filter(::isZipFile)
      ?.map { archive -> archiveFolder(archive, includeAudio) }
      ?.toList()
      .orEmpty()

  @Suppress("DEPRECATION")
  fun mediaStoreFolders(
    context: Context,
    includeAudio: Boolean,
  ): List<VideoFolder> = runCatching {
    val result = linkedMapOf<String, VideoFolder>()
    context.contentResolver.query(
      MediaStore.Files.getContentUri("external"),
      arrayOf(MediaStore.MediaColumns.DATA),
      "${MediaStore.MediaColumns.DISPLAY_NAME} LIKE ?",
      arrayOf("%.zip"),
      null,
    )?.use { cursor ->
      val dataIndex = cursor.getColumnIndex(MediaStore.MediaColumns.DATA)
      while (cursor.moveToNext()) {
        val archive = dataIndex.takeIf { it >= 0 }?.let(cursor::getString)?.let(::File) ?: continue
        if (!isZipFile(archive) || !archive.canRead()) continue
        val folder = archiveFolder(archive, includeAudio)
        if (folder.videoCount <= 0) continue
        result[archive.absolutePath.lowercase(Locale.ROOT)] = VideoFolder(
          bucketId = folder.path,
          name = folder.name,
          path = folder.path,
          videoCount = folder.videoCount,
          totalSize = folder.totalSize,
          totalDuration = 0L,
          lastModified = folder.lastModified / 1000L,
        )
      }
    }
    result.values.toList()
  }.getOrDefault(emptyList())

  fun allMedia(
    context: Context,
    virtualPath: String,
    includeAudio: Boolean,
  ): Result<List<Video>> = runCatching {
    val location = parseBrowserPath(virtualPath) ?: throw IOException("Invalid ZIP folder")
    val archiveFile = File(location.archivePath)
    if (!isZipFile(archiveFile) || !archiveFile.canRead()) throw IOException("Cannot read ZIP archive")
    val prefix = location.directory.takeIf(String::isNotEmpty)?.plus('/') ?: ""
    ZipFile(archiveFile).use { zip ->
      buildList {
        val entries = zip.entries()
        var entryCount = 0
        while (entries.hasMoreElements()) {
          if (++entryCount > MAX_ENTRIES) throw IOException("ZIP archive has too many entries")
          val entry = entries.nextElement()
          val fullPath = normalizedEntryName(entry) ?: continue
          if (entry.isDirectory || !fullPath.startsWith(prefix) || !isPlayable(fullPath, includeAudio)) continue
          add(videoItem(context, archiveFile, entry, fullPath, virtualPath).video)
        }
      }
    }
  }

  fun scan(
    context: Context,
    virtualPath: String,
    includeAudio: Boolean,
  ): Result<List<FileSystemItem>> = runCatching {
    val location = parseBrowserPath(virtualPath) ?: throw IOException("Invalid ZIP folder")
    val archiveFile = File(location.archivePath)
    if (!isZipFile(archiveFile) || !archiveFile.canRead()) throw IOException("Cannot read ZIP archive")

    ZipFile(archiveFile).use { zip ->
      val prefix = location.directory.takeIf(String::isNotEmpty)?.plus('/') ?: ""
      val folders = linkedMapOf<String, FolderStats>()
      val videos = linkedMapOf<String, FileSystemItem.VideoFile>()
      val entries = zip.entries()
      var entryCount = 0

      while (entries.hasMoreElements()) {
        if (++entryCount > MAX_ENTRIES) throw IOException("ZIP archive has too many entries")
        val entry = entries.nextElement()
        val fullPath = normalizedEntryName(entry) ?: continue
        if (!fullPath.startsWith(prefix) || fullPath == location.directory) continue
        val relativePath = fullPath.removePrefix(prefix)
        if (relativePath.isEmpty()) continue

        val separator = relativePath.indexOf('/')
        if (separator >= 0) {
          val childName = relativePath.substring(0, separator)
          if (childName.isEmpty()) continue
          val remainder = relativePath.substring(separator + 1)
          val stats = folders.getOrPut(childName, ::FolderStats)
          if (remainder.trimEnd('/').contains('/')) stats.hasSubfolders = true
          if (!entry.isDirectory && isPlayable(fullPath, includeAudio)) {
            stats.videoCount++
            stats.totalSize += entry.size.coerceAtLeast(0L)
          }
          continue
        }

        if (!entry.isDirectory && isPlayable(fullPath, includeAudio)) {
          videos.putIfAbsent(fullPath, videoItem(context, archiveFile, entry, fullPath, virtualPath))
        }
      }

      buildList {
        folders.forEach { (name, stats) ->
          val childDirectory = if (location.directory.isEmpty()) name else "${location.directory}/$name"
          add(
            FileSystemItem.Folder(
              name = name,
              path = browserPath(location.archivePath, childDirectory),
              lastModified = archiveFile.lastModified(),
              videoCount = stats.videoCount,
              totalSize = stats.totalSize,
              hasSubfolders = stats.hasSubfolders,
            ),
          )
        }
        addAll(videos.values)
      }
    }
  }

  private fun archiveFolder(
    archive: File,
    includeAudio: Boolean,
  ): FileSystemItem.Folder {
    val stats = runCatching { inspectArchive(archive, includeAudio) }.getOrNull()
    return FileSystemItem.Folder(
      name = archive.name,
      path = browserPath(archive.absolutePath),
      lastModified = archive.lastModified(),
      videoCount = stats?.videoCount ?: 0,
      totalSize = stats?.totalSize ?: archive.length(),
      hasSubfolders = stats?.hasSubfolders == true,
    )
  }

  private fun videoItem(
    context: Context,
    archive: File,
    entry: ZipEntry,
    entryPath: String,
    bucketId: String,
  ): FileSystemItem.VideoFile {
    val displayName = entryPath.substringAfterLast('/')
    val extension = displayName.substringAfterLast('.', "").lowercase(Locale.ROOT)
    val size = entry.size.coerceAtLeast(0L)
    val uri = Uri.parse(playbackUri(archive.absolutePath, entryPath))
    val modifiedMillis = entry.time.takeIf { it >= 0L } ?: archive.lastModified()
    val isAudio = extension in FileTypeUtils.AUDIO_EXTENSIONS
    val video = Video(
      id = "$bucketId\u0000$entryPath".hashCode().toLong(),
      title = displayName.substringBeforeLast('.', displayName),
      displayName = displayName,
      path = uri.toString(),
      uri = uri,
      duration = 0L,
      durationFormatted = "",
      size = size,
      sizeFormatted = if (size > 0L) Formatter.formatFileSize(context, size) else "",
      dateModified = modifiedMillis / 1000L,
      dateAdded = archive.lastModified() / 1000L,
      mimeType = FileTypeUtils.getMimeTypeFromExtension(extension),
      bucketId = bucketId,
      bucketDisplayName = File(archive.absolutePath).name,
      width = 0,
      height = 0,
      fps = 0f,
      resolution = "--",
      isAudio = isAudio,
    )
    return FileSystemItem.VideoFile(displayName, uri.toString(), modifiedMillis, video)
  }

  /** Finds an entry by the normalized path used in playback URIs. */
  internal fun findEntry(
    archive: ZipFile,
    entryPath: String,
  ): ZipEntry? {
    val entries = archive.entries()
    while (entries.hasMoreElements()) {
      val entry = entries.nextElement()
      if (normalizedEntryName(entry) == entryPath) return entry
    }
    return null
  }

  private fun normalizedEntryName(entry: ZipEntry): String? {
    val normalized = normalizeEntryPath(entry.name) ?: return null
    if (normalized.isEmpty()) return null
    val segments = normalized.split('/')
    if (segments.firstOrNull().equals("__MACOSX", ignoreCase = true) || segments.lastOrNull() == ".DS_Store") return null
    return normalized
  }

  private fun normalizeEntryPath(value: String): String? {
    val segments = value.replace('\\', '/').trim('/').split('/').filter { it.isNotEmpty() && it != "." }
    if (segments.any { it == ".." }) return null
    return segments.joinToString("/")
  }

  private fun isPlayable(
    path: String,
    includeAudio: Boolean,
  ): Boolean {
    val extension = path.substringAfterLast('.', "").lowercase(Locale.ROOT)
    return extension in FileTypeUtils.VIDEO_EXTENSIONS || includeAudio && extension in FileTypeUtils.AUDIO_EXTENSIONS
  }
}
