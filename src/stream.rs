//! Streaming state machines shared by the blocking and async wrappers.
//!
//! Each state machine performs I/O through a poll-style closure, so that the
//! blocking wrappers can drive them with `Poll::Ready(inner.read(buf))` and the
//! async wrappers with the inner stream's `poll_read`/`poll_write`. All state is
//! kept across `Poll::Pending` and retryable errors, so a call may be retried.

use std::io;
use std::task::{Poll, ready};

use crate::key::sealed::{Variant, VariantRef};
use crate::raw::{AesGcm, CHUNK_SIZE, Decryptor, ENC_CHUNK_SIZE, Encryptor, TAG_SIZE};
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

/// Copies as much of `buf[*pos..end]` as fits into `dst`.
fn drain(buf: &[u8], pos: &mut usize, end: usize, dst: &mut [u8]) -> usize {
    let n = (end - *pos).min(dst.len());
    dst[..n].copy_from_slice(&buf[*pos..*pos + n]);
    *pos += n;
    n
}

/// Writes `buf[*pos..end]` to the sink.
fn poll_flush_buf(
    buf: &[u8],
    pos: &mut usize,
    end: usize,
    mut write: impl FnMut(&[u8]) -> Poll<io::Result<usize>>,
) -> Poll<io::Result<()>> {
    while *pos < end {
        match ready!(write(&buf[*pos..end])) {
            Ok(0) => return Poll::Ready(Err(io::ErrorKind::WriteZero.into())),
            Ok(n) => *pos += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Poll::Ready(Err(e)),
        }
    }
    Poll::Ready(Ok(()))
}

/// Pull-based encryption: plaintext is read from a source and ciphertext is
/// produced.
pub(crate) struct EncryptRead {
    enc: Encryptor<AesGcm>,
    buf: Box<[u8]>,
    /// While `filling`, the length of plaintext accumulated in `buf`.
    /// Otherwise, the end of the output pending in `buf`.
    len: usize,
    /// The start of the output pending in `buf`.
    pos: usize,
    filling: bool,
    eof: bool,
}

impl EncryptRead {
    pub(crate) fn new(header: [u8; HEADER_SIZE], enc: Encryptor<AesGcm>) -> Self {
        let mut buf = vec![0; ENC_CHUNK_SIZE].into_boxed_slice();
        buf[..HEADER_SIZE].copy_from_slice(&header);
        EncryptRead {
            enc,
            buf,
            len: HEADER_SIZE,
            pos: 0,
            filling: false,
            eof: false,
        }
    }

    pub(crate) fn poll_read(
        &mut self,
        dst: &mut [u8],
        mut read: impl FnMut(&mut [u8]) -> Poll<io::Result<usize>>,
    ) -> Poll<io::Result<usize>> {
        loop {
            if !self.filling && self.pos < self.len {
                return Poll::Ready(Ok(drain(&self.buf, &mut self.pos, self.len, dst)));
            }
            if self.eof || dst.is_empty() {
                return Poll::Ready(Ok(0));
            }
            if !self.filling {
                self.filling = true;
                self.len = 0;
            }
            let eof = ready!(poll_fill(
                &mut self.buf[..CHUNK_SIZE],
                &mut self.len,
                &mut read
            ))?;
            let tag = self
                .enc
                .seal(&mut self.buf[..self.len], eof)
                .map_err(io::Error::from)?;
            self.buf[self.len..self.len + TAG_SIZE].copy_from_slice(&tag);
            self.len += TAG_SIZE;
            self.pos = 0;
            self.filling = false;
            self.eof = eof;
        }
    }
}

/// Push-based encryption: plaintext is written and ciphertext is written to a
/// sink.
pub(crate) struct EncryptWrite {
    enc: Encryptor<AesGcm>,
    buf: Box<[u8]>,
    /// The length of plaintext accumulated in `buf`, when not flushing.
    acc: usize,
    /// The range of output pending in `buf`. Plaintext is accumulated only
    /// when this is empty.
    pos: usize,
    end: usize,
    finished: bool,
    failed: bool,
}

impl EncryptWrite {
    pub(crate) fn new(header: [u8; HEADER_SIZE], enc: Encryptor<AesGcm>) -> Self {
        let mut buf = vec![0; ENC_CHUNK_SIZE].into_boxed_slice();
        buf[..HEADER_SIZE].copy_from_slice(&header);
        EncryptWrite {
            enc,
            buf,
            acc: 0,
            pos: 0,
            end: HEADER_SIZE,
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
        let res = ready!(poll_flush_buf(&self.buf, &mut self.pos, self.end, write));
        if let Err(e) = &res
            && e.kind() != io::ErrorKind::WouldBlock
        {
            self.failed = true;
        }
        if res.is_ok() {
            self.pos = 0;
            self.end = 0;
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
        let n = data.len().min(CHUNK_SIZE - self.acc);
        self.buf[self.acc..self.acc + n].copy_from_slice(&data[..n]);
        self.acc += n;
        if self.acc == CHUNK_SIZE {
            self.seal(false)?;
        }
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
            self.seal(true)?;
            self.finished = true;
        }
        self.poll_flush_pending(write)
    }

    fn seal(&mut self, last: bool) -> io::Result<()> {
        let tag = match self.enc.seal(&mut self.buf[..self.acc], last) {
            Ok(tag) => tag,
            Err(e) => {
                self.failed = true;
                return Err(e.into());
            }
        };
        self.buf[self.acc..self.acc + TAG_SIZE].copy_from_slice(&tag);
        self.pos = 0;
        self.end = self.acc + TAG_SIZE;
        self.acc = 0;
        Ok(())
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
    Body(Decryptor<AesGcm>),
}

/// Pull-based decryption: ciphertext is read from a source and authenticated
/// plaintext is produced, one chunk at a time.
pub(crate) struct DecryptRead {
    phase: DecryptPhase,
    buf: Box<[u8]>,
    /// The amount of ciphertext read into `buf` so far, while reading.
    filled: usize,
    /// The range of plaintext pending in `buf`.
    pos: usize,
    end: usize,
    header_failed: Option<Error>,
}

impl DecryptRead {
    pub(crate) fn new(key: VariantRef<'_>, context: &[u8]) -> Self {
        DecryptRead {
            phase: DecryptPhase::Header {
                key: key.into_owned(),
                context: context.to_vec(),
            },
            buf: vec![0; ENC_CHUNK_SIZE].into_boxed_slice(),
            filled: 0,
            pos: 0,
            end: 0,
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
                self.phase = DecryptPhase::Body(Decryptor::new(cipher));
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
        let DecryptPhase::Body(dec) = &mut self.phase else {
            unreachable!("header was read");
        };
        loop {
            if self.pos < self.end {
                return Poll::Ready(Ok(drain(&self.buf, &mut self.pos, self.end, dst)));
            }
            if let Some(err) = dec.failed() {
                return Poll::Ready(Err(err.clone().into()));
            }
            if dec.is_done() || dst.is_empty() {
                return Poll::Ready(Ok(0));
            }
            ready!(poll_fill(&mut self.buf, &mut self.filled, &mut read))?;
            let len = dec.open(&mut self.buf[..self.filled]);
            self.filled = 0;
            self.pos = 0;
            self.end = len.as_ref().copied().unwrap_or(0);
            len?;
        }
    }
}
