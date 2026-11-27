//! The buffering of the streaming types, without any I/O, so that Charon can
//! extract it for the Lean proofs. The streaming types in stream.rs own the
//! buffer, which they wipe on drop, and pass it to every call. It must be
//! [`ENC_CHUNK_SIZE`] bytes long.

use crate::Error;
use crate::raw::{CHUNK_SIZE, ChunkAead, Decryptor, ENC_CHUNK_SIZE, Encryptor, TAG_SIZE};

/// Plaintext accumulates at the start of the buffer until it fills a chunk, or
/// the caller seals the final chunk, and is then encrypted in place. The
/// ciphertext is then pending, and plaintext is accepted again only once it has
/// been drained.
pub(crate) struct EncryptBuffer<A> {
    enc: Encryptor<A>,
    /// The length of the plaintext accumulated. Zero while output is pending.
    acc: usize,
    /// The range of the output pending.
    pos: usize,
    end: usize,
}

impl<A: ChunkAead> EncryptBuffer<A> {
    /// Returns a buffer with `prefix` pending, which must fit in the buffer.
    pub(crate) fn new(enc: Encryptor<A>, buf: &mut [u8], prefix: &[u8]) -> Self {
        buf[..prefix.len()].copy_from_slice(prefix);
        EncryptBuffer {
            enc,
            acc: 0,
            pos: 0,
            end: prefix.len(),
        }
    }

    pub(crate) fn is_drained(&self) -> bool {
        self.pos == self.end
    }

    pub(crate) fn pending<'a>(&self, buf: &'a [u8]) -> &'a [u8] {
        &buf[self.pos..self.end]
    }

    /// Marks `n` bytes of the pending output as written out.
    pub(crate) fn advance(&mut self, n: usize) {
        self.pos += n.min(self.end - self.pos);
        if self.pos == self.end {
            self.pos = 0;
            self.end = 0;
        }
    }

    /// The space for more plaintext. Only valid while no output is pending.
    pub(crate) fn space<'a>(&self, buf: &'a mut [u8]) -> &'a mut [u8] {
        &mut buf[self.acc..CHUNK_SIZE]
    }

    /// Accepts `n` bytes of plaintext written to [`space`](Self::space), and
    /// seals the chunk if it's full.
    pub(crate) fn filled(&mut self, buf: &mut [u8], n: usize) -> Result<(), Error> {
        self.acc += n.min(CHUNK_SIZE - self.acc);
        if self.acc == CHUNK_SIZE {
            self.seal(buf, false)
        } else {
            Ok(())
        }
    }

    /// Accepts as much of `data` as fits in the chunk, and returns how much.
    /// Only valid while no output is pending.
    pub(crate) fn absorb(&mut self, buf: &mut [u8], data: &[u8]) -> Result<usize, Error> {
        let n = data.len().min(CHUNK_SIZE - self.acc);
        buf[self.acc..self.acc + n].copy_from_slice(&data[..n]);
        self.filled(buf, n)?;
        Ok(n)
    }

    /// Encrypts the plaintext accumulated as the next chunk, which makes it
    /// pending. Only valid while no output is pending.
    pub(crate) fn seal(&mut self, buf: &mut [u8], last: bool) -> Result<(), Error> {
        let tag = self.enc.seal(&mut buf[..self.acc], last)?;
        buf[self.acc..self.acc + TAG_SIZE].copy_from_slice(&tag);
        self.pos = 0;
        self.end = self.acc + TAG_SIZE;
        self.acc = 0;
        Ok(())
    }
}

/// Ciphertext accumulates at the start of the buffer until it fills an
/// encrypted chunk, or the caller reaches the end of the ciphertext, and is then
/// decrypted in place. The plaintext is then pending, and ciphertext is accepted
/// again only once it has been drained.
pub(crate) struct DecryptBuffer<A> {
    dec: Decryptor<A>,
    /// The length of the ciphertext accumulated. Zero while output is pending.
    filled: usize,
    /// The range of the output pending.
    pos: usize,
    end: usize,
}

impl<A: ChunkAead> DecryptBuffer<A> {
    pub(crate) fn new(dec: Decryptor<A>) -> Self {
        DecryptBuffer {
            dec,
            filled: 0,
            pos: 0,
            end: 0,
        }
    }

    pub(crate) fn is_drained(&self) -> bool {
        self.pos == self.end
    }

    /// Returns true once the final chunk has been decrypted.
    pub(crate) fn is_done(&self) -> bool {
        self.dec.is_done()
    }

    /// Returns the error that previously caused decryption to fail, if any.
    pub(crate) fn failed(&self) -> Option<&Error> {
        self.dec.failed()
    }

    pub(crate) fn pending<'a>(&self, buf: &'a [u8]) -> &'a [u8] {
        &buf[self.pos..self.end]
    }

    /// Marks `n` bytes of the pending output as read out.
    pub(crate) fn advance(&mut self, n: usize) {
        self.pos += n.min(self.end - self.pos);
        if self.pos == self.end {
            self.pos = 0;
            self.end = 0;
        }
    }

    /// The space for more ciphertext. Only valid while no output is pending.
    pub(crate) fn space<'a>(&self, buf: &'a mut [u8]) -> &'a mut [u8] {
        &mut buf[self.filled..ENC_CHUNK_SIZE]
    }

    /// Accepts `n` bytes of ciphertext written to [`space`](Self::space), and
    /// returns true if that filled an encrypted chunk.
    pub(crate) fn filled(&mut self, n: usize) -> bool {
        self.filled += n.min(ENC_CHUNK_SIZE - self.filled);
        self.filled == ENC_CHUNK_SIZE
    }

    /// Decrypts the ciphertext accumulated as the next chunk, which makes its
    /// plaintext pending. It is the final chunk if it's shorter than a full
    /// encrypted chunk, so the caller must only open a partial chunk at the end
    /// of the ciphertext. Only valid while no output is pending and before the
    /// final chunk.
    pub(crate) fn open(&mut self, buf: &mut [u8]) -> Result<(), Error> {
        let result = self.dec.open(&mut buf[..self.filled]);
        self.filled = 0;
        self.pos = 0;
        match result {
            Ok(len) => {
                self.end = len;
                Ok(())
            }
            Err(err) => {
                self.end = 0;
                Err(err)
            }
        }
    }
}
