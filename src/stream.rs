//! Streaming state machines shared by the blocking and async wrappers.
//!
//! Each state machine performs I/O through a poll-style closure, so that the
//! blocking wrappers can drive them with `Poll::Ready(inner.read(buf))` and the
//! async wrappers with the inner stream's `poll_read`/`poll_write`. All state is
//! kept across `Poll::Pending` and retryable errors, so a call may be retried.

use std::io;
use std::task::{Poll, ready};

use zeroize::Zeroizing;

use crate::buffer::{DecryptBuffer, EncryptBuffer};
use crate::key::sealed::{Variant, VariantRef};
use crate::primitives::AesGcm;
use crate::raw::{Decryptor, ENC_CHUNK_SIZE, Encryptor};
use crate::{Error, HEADER_SIZE};

/// Reads into `buf[*filled..]` until it's full or the source reaches EOF.
/// Returns whether EOF was reached.
fn poll_fill(
    buf: &mut [u8],
    filled: &mut usize,
    mut read: impl FnMut(&mut [u8]) -> Poll<io::Result<usize>>,
) -> Poll<io::Result<bool>> {
    while *filled < buf.len() {
        match ready!(read(&mut buf[*filled..])) {
            Ok(0) => return Poll::Ready(Ok(true)),
            Ok(n) => *filled += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Poll::Ready(Err(e)),
        }
    }
    Poll::Ready(Ok(false))
}

/// Copies as much of `src` as fits into `dst`.
fn copy_out(src: &[u8], dst: &mut [u8]) -> usize {
    let n = src.len().min(dst.len());
    dst[..n].copy_from_slice(&src[..n]);
    n
}

/// Writes out the pending ciphertext.
fn poll_drain(
    state: &mut EncryptBuffer<AesGcm>,
    buf: &[u8],
    mut write: impl FnMut(&[u8]) -> Poll<io::Result<usize>>,
) -> Poll<io::Result<()>> {
    while !state.is_drained() {
        match ready!(write(state.pending(buf))) {
            Ok(0) => return Poll::Ready(Err(io::ErrorKind::WriteZero.into())),
            Ok(n) => state.advance(n),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Poll::Ready(Err(e)),
        }
    }
    Poll::Ready(Ok(()))
}

fn new_encrypt_buffer(
    header: [u8; HEADER_SIZE],
    enc: Encryptor<AesGcm>,
) -> (EncryptBuffer<AesGcm>, Zeroizing<Box<[u8]>>) {
    let mut buf = Zeroizing::new(vec![0; ENC_CHUNK_SIZE].into_boxed_slice());
    let state = EncryptBuffer::new(enc, &mut buf, &header);
    (state, buf)
}

/// Pull-based encryption: plaintext is read from a source and ciphertext is
/// produced.
pub(crate) struct EncryptRead {
    state: EncryptBuffer<AesGcm>,
    /// Holds plaintext, so it's wiped on drop.
    buf: Zeroizing<Box<[u8]>>,
    eof: bool,
    /// Sealing a chunk can fail only once the message is too large, which is
    /// then permanent.
    failed: Option<Error>,
}

impl EncryptRead {
    pub(crate) fn new(header: [u8; HEADER_SIZE], enc: Encryptor<AesGcm>) -> Self {
        let (state, buf) = new_encrypt_buffer(header, enc);
        EncryptRead {
            state,
            buf,
            eof: false,
            failed: None,
        }
    }

    pub(crate) fn poll_read(
        &mut self,
        dst: &mut [u8],
        mut read: impl FnMut(&mut [u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<usize>> {
        loop {
            if !self.state.is_drained() {
                let n = copy_out(self.state.pending(&self.buf), dst);
                self.state.advance(n);
                return Poll::Ready(Ok(n));
            }
            if let Some(err) = &self.failed {
                return Poll::Ready(Err(err.clone().into()));
            }
            if self.eof || dst.is_empty() {
                return Poll::Ready(Ok(0));
            }
            let result = match ready!(read(self.state.space(&mut self.buf))) {
                Ok(0) => {
                    self.eof = true;
                    self.state.seal(&mut self.buf, true)
                }
                Ok(n) => self.state.filled(&mut self.buf, n),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => Ok(()),
                Err(e) => return Poll::Ready(Err(e)),
            };
            if let Err(err) = result {
                self.failed = Some(err.clone());
                return Poll::Ready(Err(err.into()));
            }
        }
    }
}

/// Push-based encryption: plaintext is written and ciphertext is written to a
/// sink.
pub(crate) struct EncryptWrite {
    state: EncryptBuffer<AesGcm>,
    /// Holds plaintext, so it's wiped on drop.
    buf: Zeroizing<Box<[u8]>>,
    finished: bool,
    failed: bool,
}

impl EncryptWrite {
    pub(crate) fn new(header: [u8; HEADER_SIZE], enc: Encryptor<AesGcm>) -> Self {
        let (state, buf) = new_encrypt_buffer(header, enc);
        EncryptWrite {
            state,
            buf,
            finished: false,
            failed: false,
        }
    }

    fn check(&self) -> io::Result<()> {
        if self.failed {
            return Err(io::Error::other("a previous write failed"));
        }
        if self.finished {
            return Err(io::Error::other("the encryption writer is finished"));
        }
        Ok(())
    }

    /// Writes out any pending ciphertext. If writing fails, the writer is
    /// poisoned unless the error is retryable, since the plaintext was
    /// already accepted.
    pub(crate) fn poll_flush_pending(
        &mut self,
        write: impl FnMut(&[u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<()>> {
        let res = ready!(poll_drain(&mut self.state, &self.buf, write));
        if let Err(e) = &res
            && e.kind() != io::ErrorKind::WouldBlock
        {
            self.failed = true;
        }
        Poll::Ready(res)
    }

    pub(crate) fn poll_write(
        &mut self,
        data: &[u8],
        write: impl FnMut(&[u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<usize>> {
        self.check()?;
        ready!(self.poll_flush_pending(write))?;
        let n = self
            .state
            .absorb(&mut self.buf, data)
            .inspect_err(|_| self.failed = true)?;
        Poll::Ready(Ok(n))
    }

    /// Encrypts and writes out the final chunk. Once this returns
    /// `Ready(Ok(()))`, the ciphertext is complete.
    pub(crate) fn poll_finish(
        &mut self,
        mut write: impl FnMut(&[u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<()>> {
        if !self.finished {
            if self.failed {
                return Poll::Ready(Err(io::Error::other("a previous write failed")));
            }
            ready!(self.poll_flush_pending(&mut write))?;
            self.state
                .seal(&mut self.buf, true)
                .inspect_err(|_| self.failed = true)?;
            self.finished = true;
        }
        self.poll_flush_pending(write)
    }

    /// Returns true once the final chunk has been written out in full.
    #[cfg(feature = "tokio")]
    pub(crate) fn is_complete(&self) -> bool {
        self.finished && self.state.is_drained()
    }
}

// The Header variant is short-lived, so its smaller size doesn't matter.
#[allow(clippy::large_enum_variant)]
enum DecryptPhase {
    /// The header hasn't been fully read yet.
    Header {
        key: Variant,
        context: Vec<u8>,
    },
    Body(DecryptBuffer<AesGcm>),
}

/// Pull-based decryption: ciphertext is read from a source and authenticated
/// plaintext is produced, one chunk at a time.
pub(crate) struct DecryptRead {
    phase: DecryptPhase,
    /// Holds plaintext, so it's wiped on drop.
    buf: Zeroizing<Box<[u8]>>,
    /// The amount of the header read into `buf` so far.
    filled: usize,
    header_failed: Option<Error>,
}

impl DecryptRead {
    pub(crate) fn new(key: VariantRef<'_>, context: &[u8]) -> Self {
        DecryptRead {
            phase: DecryptPhase::Header {
                key: key.into_owned(),
                context: context.to_vec(),
            },
            buf: Zeroizing::new(vec![0; ENC_CHUNK_SIZE].into_boxed_slice()),
            filled: 0,
            header_failed: None,
        }
    }

    /// Reads and checks the header, if that hasn't been done yet.
    pub(crate) fn poll_header(
        &mut self,
        read: impl FnMut(&mut [u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<()>> {
        if let Some(err) = &self.header_failed {
            return Poll::Ready(Err(err.clone().into()));
        }
        let DecryptPhase::Header { key, context } = &self.phase else {
            return Poll::Ready(Ok(()));
        };
        let eof = ready!(poll_fill(
            &mut self.buf[..HEADER_SIZE],
            &mut self.filled,
            read
        ))?;
        let result = if eof {
            Err(Error::Truncated)
        } else {
            let header = self.buf[..HEADER_SIZE].try_into().unwrap();
            crate::open_header(key.as_ref(), context, header)
        };
        self.filled = 0;
        match result {
            Ok(cipher) => {
                self.phase = DecryptPhase::Body(DecryptBuffer::new(Decryptor::new(cipher)));
                Poll::Ready(Ok(()))
            }
            Err(err) => {
                self.header_failed = Some(err.clone());
                Poll::Ready(Err(err.into()))
            }
        }
    }

    pub(crate) fn poll_read(
        &mut self,
        dst: &mut [u8],
        mut read: impl FnMut(&mut [u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<usize>> {
        ready!(self.poll_header(&mut read))?;
        let DecryptPhase::Body(state) = &mut self.phase else {
            unreachable!("header was read");
        };
        loop {
            if !state.is_drained() {
                let n = copy_out(state.pending(&self.buf), dst);
                state.advance(n);
                return Poll::Ready(Ok(n));
            }
            if let Some(err) = state.failed() {
                return Poll::Ready(Err(err.clone().into()));
            }
            if state.is_done() || dst.is_empty() {
                return Poll::Ready(Ok(0));
            }
            let full = match ready!(read(state.space(&mut self.buf))) {
                Ok(0) => true,
                Ok(n) => state.filled(n),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => false,
                Err(e) => return Poll::Ready(Err(e)),
            };
            if full {
                state.open(&mut self.buf)?;
            }
        }
    }
}
