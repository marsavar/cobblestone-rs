//! Blocking `std::io` streaming and random access APIs.

use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::task::Poll;

use aes_gcm::Aes128Gcm;

use crate::raw::{self, CHUNK_SIZE, ChunkCipher, ENC_CHUNK_SIZE, TAG_SIZE};
use crate::stream;
use crate::{Error, HEADER_SIZE, Key};

fn unwrap_ready<T>(p: Poll<T>) -> T {
    match p {
        Poll::Ready(v) => v,
        Poll::Pending => unreachable!("blocking I/O never returns Pending"),
    }
}

/// Encrypts plaintext written to it, and writes the ciphertext to an inner
/// writer.
///
/// [`finish`](Self::finish) must be called to write the final chunk: dropping
/// the writer without calling it produces a truncated ciphertext, which will
/// fail to decrypt.
///
/// Ciphertext is written in chunks of 16 KiB plus overhead, so wrapping the
/// inner writer in a [`BufWriter`](std::io::BufWriter) is usually unnecessary.
///
/// # Examples
///
/// ```
/// use std::io::Write;
///
/// let key = cobblestone::Key::generate();
/// let mut w = cobblestone::EncryptWriter::new(&key, b"file.txt", Vec::new());
/// w.write_all(b"hello ")?;
/// w.write_all(b"world")?;
/// let ciphertext = w.finish()?;
/// assert_eq!(cobblestone::decrypt(&key, b"file.txt", &ciphertext)?, b"hello world");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct EncryptWriter<W> {
    inner: W,
    state: stream::EncryptWrite,
}

impl<W: Write> EncryptWriter<W> {
    /// Creates a new writer. The ciphertext header is written to `inner` on
    /// the first write, flush, or [`finish`](Self::finish).
    ///
    /// The context may be empty, and must match on decryption.
    ///
    /// # Panics
    ///
    /// Panics if the operating system's random number generator fails, which
    /// doesn't happen on supported platforms.
    pub fn new(key: &Key, context: &[u8], inner: W) -> Self {
        let (header, enc) = crate::new_header(key, context);
        EncryptWriter {
            inner,
            state: stream::EncryptWrite::new(header, enc),
        }
    }

    /// Writes the final chunk, and returns the inner writer.
    ///
    /// This does not flush the inner writer.
    ///
    /// # Errors
    ///
    /// Returns any error from writing to `inner`, or an error if a previous
    /// write failed, in which case the ciphertext is incomplete.
    pub fn finish(mut self) -> io::Result<W> {
        let inner = &mut self.inner;
        unwrap_ready(self.state.poll_finish(|b| Poll::Ready(inner.write(b))))?;
        Ok(self.inner)
    }

    /// Returns a reference to the inner writer.
    pub fn get_ref(&self) -> &W {
        &self.inner
    }
}

impl<W: fmt::Debug> fmt::Debug for EncryptWriter<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncryptWriter")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<W: Write> Write for EncryptWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let inner = &mut self.inner;
        unwrap_ready(self.state.poll_write(buf, |b| Poll::Ready(inner.write(b))))
    }

    /// Writes out any completed chunks and flushes the inner writer.
    ///
    /// Plaintext of an incomplete chunk stays buffered: since all chunks but
    /// the final one must be full, it can't be written out until the chunk is
    /// complete or [`finish`](Self::finish) is called.
    fn flush(&mut self) -> io::Result<()> {
        let inner = &mut self.inner;
        unwrap_ready(
            self.state
                .poll_flush_pending(|b| Poll::Ready(inner.write(b))),
        )?;
        self.inner.flush()
    }
}

/// Reads plaintext from an inner reader, and produces the ciphertext.
///
/// # Examples
///
/// ```
/// use std::io::Read;
///
/// let key = cobblestone::Key::generate();
/// let mut r = cobblestone::EncryptReader::new(&key, b"", &b"hello world"[..]);
/// let mut ciphertext = Vec::new();
/// r.read_to_end(&mut ciphertext)?;
/// assert_eq!(cobblestone::decrypt(&key, b"", &ciphertext)?, b"hello world");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct EncryptReader<R> {
    inner: R,
    state: stream::EncryptRead,
}

impl<R: Read> EncryptReader<R> {
    /// Creates a new reader that encrypts the plaintext read from `inner`.
    ///
    /// The context may be empty, and must match on decryption.
    ///
    /// # Panics
    ///
    /// Panics if the operating system's random number generator fails, which
    /// doesn't happen on supported platforms.
    pub fn new(key: &Key, context: &[u8], inner: R) -> Self {
        let (header, enc) = crate::new_header(key, context);
        EncryptReader {
            inner,
            state: stream::EncryptRead::new(header, enc),
        }
    }

    /// Returns a reference to the inner reader.
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Returns the inner reader.
    ///
    /// Plaintext already read from `inner` but not yet returned as ciphertext
    /// is lost.
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: fmt::Debug> fmt::Debug for EncryptReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncryptReader")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<R: Read> Read for EncryptReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let inner = &mut self.inner;
        unwrap_ready(self.state.poll_read(buf, |b| Poll::Ready(inner.read(b))))
    }
}

/// Reads ciphertext from an inner reader, and produces the plaintext.
///
/// The header is read and the key commitment is checked on the first read,
/// before any chunk is decrypted. Plaintext is only returned after the chunk
/// containing it is authenticated, but if the ciphertext is invalid, a prefix
/// of the message may be returned before an error. Once an error is returned,
/// all subsequent reads fail. The end of the message (`Ok(0)`) is only
/// reported after the whole ciphertext is authenticated, so truncation is
/// always detected.
///
/// Errors caused by the ciphertext wrap an [`Error`], which can be recovered
/// with [`io::Error::downcast`](https://doc.rust-lang.org/std/io/struct.Error.html#method.downcast).
///
/// # Examples
///
/// ```
/// use std::io::Read;
///
/// let key = cobblestone::Key::generate();
/// let ciphertext = cobblestone::encrypt(&key, b"", b"hello world")?;
///
/// let mut r = cobblestone::DecryptReader::new(&key, b"", &ciphertext[..]);
/// let mut plaintext = String::new();
/// r.read_to_string(&mut plaintext)?;
/// assert_eq!(plaintext, "hello world");
///
/// // A truncated ciphertext fails to decrypt.
/// let truncated = &ciphertext[..ciphertext.len() - 1];
/// let mut r = cobblestone::DecryptReader::new(&key, b"", truncated);
/// let err = r.read_to_end(&mut Vec::new()).unwrap_err();
/// let err = err.downcast::<cobblestone::Error>().unwrap();
/// assert_eq!(err, cobblestone::Error::DecryptionFailed { chunk: 0 });
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct DecryptReader<R> {
    inner: R,
    state: stream::DecryptRead,
}

impl<R: Read> DecryptReader<R> {
    /// Creates a new reader that decrypts the ciphertext read from `inner`.
    ///
    /// The header is read and checked on the first read, so all errors,
    /// including [`Error::InvalidCommitment`], are returned by reads.
    pub fn new(key: &Key, context: &[u8], inner: R) -> Self {
        DecryptReader {
            inner,
            state: stream::DecryptRead::new(key, context),
        }
    }

    /// Returns a reference to the inner reader.
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Returns the inner reader.
    ///
    /// Ciphertext already read from `inner` but not yet returned as plaintext
    /// is lost.
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: fmt::Debug> fmt::Debug for DecryptReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecryptReader")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<R: Read> Read for DecryptReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let inner = &mut self.inner;
        unwrap_ready(self.state.poll_read(buf, |b| Poll::Ready(inner.read(b))))
    }
}

/// Decrypts any range of a seekable ciphertext.
///
/// Use [`read_exact_at`](Self::read_exact_at) to read a range at a given
/// offset. Only the chunks covering the range are read and authenticated. The
/// decryptor also implements [`Read`] and [`Seek`] over the plaintext, for
/// code that expects a seekable reader. The message length is authenticated
/// when the decryptor is created, so ranges near the end are safe to read.
///
/// A read fails if any chunk it covers fails to authenticate, but other ranges
/// may still be readable.
///
/// # Examples
///
/// ```
/// use std::io::Cursor;
///
/// let key = cobblestone::Key::generate();
/// let message: Vec<u8> = (0..100_000u32).map(|i| i as u8).collect();
/// let ciphertext = cobblestone::encrypt(&key, b"", &message)?;
///
/// // In practice, this would usually be a File.
/// let mut r = cobblestone::RandomAccessDecryptor::new(&key, b"", Cursor::new(ciphertext))?;
/// assert_eq!(r.plaintext_len(), 100_000);
///
/// // Read 10 bytes at offset 50,000. Only the chunk holding them is decrypted.
/// let mut buf = [0; 10];
/// r.read_exact_at(&mut buf, 50_000)?;
/// assert_eq!(buf, message[50_000..50_010]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct RandomAccessDecryptor<R> {
    inner: R,
    cipher: ChunkCipher<Aes128Gcm>,
    /// The size of the raw ciphertext, after the header.
    body_size: u64,
    plaintext_len: u64,
    pos: u64,
    /// The most recently decrypted chunk.
    cache: Box<[u8]>,
    cache_len: usize,
    cache_index: Option<u64>,
}

impl<R: Read + Seek> RandomAccessDecryptor<R> {
    /// Creates a new decryptor.
    ///
    /// This reads the header and checks the key commitment, determines the
    /// ciphertext size by seeking to the end of `inner`, and authenticates the
    /// message length by decrypting the final chunk. The ciphertext must start
    /// at offset zero of `inner`.
    ///
    /// # Errors
    ///
    /// Returns an error wrapping:
    ///
    /// - [`Error::Truncated`] if the ciphertext is shorter than the header.
    /// - [`Error::InvalidCommitment`] if the ciphertext was not encrypted with
    ///   this key and context, or its header was modified.
    /// - [`Error::InvalidSize`] if no message encrypts to the ciphertext size.
    /// - [`Error::DecryptionFailed`] if the final chunk fails to authenticate,
    ///   for example because the ciphertext was truncated or extended.
    ///
    /// or any error from reading or seeking `inner`.
    pub fn new(key: &Key, context: &[u8], mut inner: R) -> io::Result<Self> {
        let size = inner.seek(SeekFrom::End(0))?;
        if size < HEADER_SIZE as u64 {
            return Err(Error::Truncated.into());
        }
        let mut header = [0; HEADER_SIZE];
        inner.seek(SeekFrom::Start(0))?;
        inner.read_exact(&mut header)?;
        let cipher = crate::open_header(key, context, &header)?;
        let body_size = size - HEADER_SIZE as u64;
        let chunks = raw::encrypted_chunk_count(body_size)?;
        let mut d = RandomAccessDecryptor {
            inner,
            cipher,
            body_size,
            plaintext_len: body_size - chunks * TAG_SIZE as u64,
            pos: 0,
            cache: vec![0; ENC_CHUNK_SIZE].into_boxed_slice(),
            cache_len: 0,
            cache_index: None,
        };
        d.load_chunk(chunks - 1)?;
        Ok(d)
    }

    /// Returns the length of the plaintext, in bytes.
    #[must_use]
    pub fn plaintext_len(&self) -> u64 {
        self.plaintext_len
    }

    /// Returns a reference to the inner reader.
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Returns the inner reader. Its position is unspecified.
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Reads exactly `buf.len()` bytes of plaintext starting at `offset`.
    ///
    /// Only the chunks covering the range are read and authenticated. The
    /// position used by [`Read`] and [`Seek`] is not changed.
    ///
    /// # Errors
    ///
    /// Returns an error of kind [`io::ErrorKind::UnexpectedEof`] if the range
    /// extends past the end of the plaintext, without reading anything.
    /// Otherwise returns an error wrapping:
    ///
    /// - [`Error::DecryptionFailed`] if a chunk in the range fails to
    ///   authenticate.
    /// - [`Error::Truncated`] if `inner` has become shorter since the
    ///   decryptor was created.
    ///
    /// or any error from reading or seeking `inner`.
    pub fn read_exact_at(&mut self, buf: &mut [u8], offset: u64) -> io::Result<()> {
        let end = offset.checked_add(buf.len() as u64);
        if end.is_none_or(|end| end > self.plaintext_len) {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "range extends past the end of the plaintext",
            ));
        }
        let saved = self.pos;
        self.pos = offset;
        let result = self.read_exact(buf);
        self.pos = saved;
        result
    }

    fn load_chunk(&mut self, index: u64) -> io::Result<()> {
        if self.cache_index == Some(index) {
            return Ok(());
        }
        self.cache_index = None;
        let offset = index * ENC_CHUNK_SIZE as u64;
        let len = (self.body_size - offset).min(ENC_CHUNK_SIZE as u64) as usize;
        self.inner
            .seek(SeekFrom::Start(HEADER_SIZE as u64 + offset))?;
        self.inner.read_exact(&mut self.cache[..len]).map_err(|e| {
            if e.kind() == io::ErrorKind::UnexpectedEof {
                Error::Truncated.into()
            } else {
                e
            }
        })?;
        self.cache_len = self.cipher.open(index, &mut self.cache[..len])?;
        self.cache_index = Some(index);
        Ok(())
    }
}

impl<R: fmt::Debug> fmt::Debug for RandomAccessDecryptor<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RandomAccessDecryptor")
            .field("inner", &self.inner)
            .field("plaintext_len", &self.plaintext_len)
            .field("pos", &self.pos)
            .finish_non_exhaustive()
    }
}

impl<R: Read + Seek> Read for RandomAccessDecryptor<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.pos >= self.plaintext_len || buf.is_empty() {
            return Ok(0);
        }
        let index = self.pos / CHUNK_SIZE as u64;
        self.load_chunk(index)?;
        let start = (self.pos % CHUNK_SIZE as u64) as usize;
        let n = (self.cache_len - start).min(buf.len());
        buf[..n].copy_from_slice(&self.cache[start..start + n]);
        self.pos += n as u64;
        Ok(n)
    }
}

impl<R: Read + Seek> Seek for RandomAccessDecryptor<R> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let new = match pos {
            SeekFrom::Start(n) => Some(n),
            SeekFrom::End(n) => self.plaintext_len.checked_add_signed(n),
            SeekFrom::Current(n) => self.pos.checked_add_signed(n),
        };
        let Some(new) = new else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid seek to a negative or overflowing position",
            ));
        };
        self.pos = new;
        Ok(new)
    }

    fn stream_position(&mut self) -> io::Result<u64> {
        Ok(self.pos)
    }
}
