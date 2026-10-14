//! Async streaming APIs for [tokio](https://docs.rs/tokio).
//!
//! These behave like their blocking counterparts in the crate root.
//!
//! # Examples
//!
//! ```
//! use cobblestone::tokio::{AsyncDecryptReader, AsyncEncryptWriter};
//! use tokio::io::{AsyncReadExt, AsyncWriteExt};
//!
//! # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
//! let key = cobblestone::Key::generate();
//!
//! let mut w = AsyncEncryptWriter::new(&key, b"file.txt", Vec::new());
//! w.write_all(b"hello world").await?;
//! w.shutdown().await?; // Writes the final chunk.
//! let ciphertext = w.into_inner();
//!
//! let mut r = AsyncDecryptReader::new(&key, b"file.txt", &ciphertext[..]);
//! let mut plaintext = Vec::new();
//! r.read_to_end(&mut plaintext).await?;
//! assert_eq!(plaintext, b"hello world");
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! # }).unwrap();
//! ```

use std::io;
use std::pin::Pin;
use std::task::{Context, Poll, ready};

use ::tokio::io::{AsyncRead, AsyncWrite, ReadBuf};
use pin_project_lite::pin_project;

use crate::Key;
use crate::stream;

fn poll_read_slice<R: AsyncRead>(
    inner: Pin<&mut R>,
    cx: &mut Context<'_>,
    buf: &mut [u8],
) -> Poll<io::Result<usize>> {
    let mut rb = ReadBuf::new(buf);
    ready!(inner.poll_read(cx, &mut rb))?;
    Poll::Ready(Ok(rb.filled().len()))
}

/// Runs a slice-based read into a [`ReadBuf`].
fn read_into(
    buf: &mut ReadBuf<'_>,
    f: impl FnOnce(&mut [u8]) -> Poll<io::Result<usize>>,
) -> Poll<io::Result<()>> {
    let n = ready!(f(buf.initialize_unfilled()))?;
    buf.advance(n);
    Poll::Ready(Ok(()))
}

pin_project! {
    /// Encrypts plaintext written to it, and writes the ciphertext to an inner
    /// writer.
    ///
    /// [`shutdown`](::tokio::io::AsyncWriteExt::shutdown) must be called to
    /// write the final chunk; it then shuts down the inner writer. Dropping
    /// the writer without shutting it down produces a truncated ciphertext,
    /// which will fail to decrypt.
    pub struct AsyncEncryptWriter<W> {
        #[pin]
        inner: W,
        state: stream::EncryptWrite,
    }
}

impl<W: AsyncWrite> AsyncEncryptWriter<W> {
    /// Creates a new writer. The header is written to `inner` on the first
    /// write, flush, or shutdown.
    ///
    /// The context may be empty, and must match on decryption.
    ///
    /// # Panics
    ///
    /// Panics if the operating system's random number generator fails, which
    /// doesn't happen on supported platforms.
    pub fn new(key: &Key, context: &[u8], inner: W) -> Self {
        let (header, enc) = crate::new_header(key, context);
        AsyncEncryptWriter {
            inner,
            state: stream::EncryptWrite::new(header, enc),
        }
    }

    /// Returns a reference to the inner writer.
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    /// Returns the inner writer.
    pub fn into_inner(self) -> W {
        self.inner
    }
}

impl<W: AsyncWrite> AsyncWrite for AsyncEncryptWriter<W> {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        let mut this = self.project();
        this.state
            .poll_write(buf, |b| this.inner.as_mut().poll_write(cx, b))
    }

    /// Writes out any completed chunks and flushes the inner writer.
    ///
    /// Plaintext of an incomplete chunk stays buffered until the chunk is
    /// complete or the writer is shut down.
    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let mut this = self.project();
        ready!(
            this.state
                .poll_flush_pending(|b| this.inner.as_mut().poll_write(cx, b))
        )?;
        this.inner.poll_flush(cx)
    }

    /// Writes the final chunk, then shuts down the inner writer.
    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let mut this = self.project();
        ready!(
            this.state
                .poll_finish(|b| this.inner.as_mut().poll_write(cx, b))
        )?;
        this.inner.poll_shutdown(cx)
    }
}

pin_project! {
    /// Reads plaintext from an inner reader, and produces the ciphertext.
    pub struct AsyncEncryptReader<R> {
        #[pin]
        inner: R,
        state: stream::EncryptRead,
    }
}

impl<R: AsyncRead> AsyncEncryptReader<R> {
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
        AsyncEncryptReader {
            inner,
            state: stream::EncryptRead::new(header, enc),
        }
    }

    /// Returns the inner reader.
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: AsyncRead> AsyncRead for AsyncEncryptReader<R> {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let mut this = self.project();
        read_into(buf, |dst| {
            this.state
                .poll_read(dst, |b| poll_read_slice(this.inner.as_mut(), cx, b))
        })
    }
}

pin_project! {
    /// Reads ciphertext from an inner reader, and produces the plaintext.
    ///
    /// The header is read and the key commitment is checked on the first read,
    /// before any chunk is decrypted. Otherwise, this behaves like
    /// [`DecryptReader`](crate::DecryptReader): plaintext is only returned
    /// after it's authenticated, errors are sticky, and the end of the message
    /// is only reported after the whole ciphertext is authenticated.
    pub struct AsyncDecryptReader<R> {
        #[pin]
        inner: R,
        state: stream::DecryptRead,
    }
}

impl<R: AsyncRead> AsyncDecryptReader<R> {
    /// Creates a new reader that decrypts the ciphertext read from `inner`.
    ///
    /// The header is read and checked on the first read, so all errors,
    /// including [`InvalidCommitment`](crate::Error::InvalidCommitment), are
    /// returned by reads.
    pub fn new(key: &Key, context: &[u8], inner: R) -> Self {
        AsyncDecryptReader {
            inner,
            state: stream::DecryptRead::new(key, context),
        }
    }

    /// Returns the inner reader.
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: AsyncRead> AsyncRead for AsyncDecryptReader<R> {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let mut this = self.project();
        read_into(buf, |dst| {
            this.state
                .poll_read(dst, |b| poll_read_slice(this.inner.as_mut(), cx, b))
        })
    }
}
