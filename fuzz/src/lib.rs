//! Helpers shared by the fuzz targets.
//!
//! libFuzzer inputs are small, so messages are generated from a length and a
//! seed instead of being taken from the input. That lets a short input
//! describe a message that spans several chunks.

use std::cell::Cell;
use std::io::{self, Read, Write};

use arbitrary::Arbitrary;

/// The size of a plaintext chunk.
pub const CHUNK_SIZE: usize = 16 * 1024;
/// The size of an encrypted full chunk.
pub const ENC_CHUNK_SIZE: usize = CHUNK_SIZE + 16;
/// The size of the salt and commitment before the first chunk.
pub const HEADER_SIZE: usize = 56;

/// The key of either instantiation.
#[derive(Arbitrary, Debug)]
pub enum AnyKey {
    Cobblestone128([u8; 16]),
    Cobblestone256([u8; 32]),
}

/// The length of a message, of up to four chunks.
#[derive(Arbitrary, Debug)]
pub enum Len {
    Any(u16),
    /// Lengths around a chunk boundary, where the chunking is most likely to
    /// go wrong. The fuzzer rarely finds them by chance.
    NearBoundary {
        chunks: u8,
        delta: i8,
    },
}

impl Len {
    pub fn get(&self) -> usize {
        match *self {
            Len::Any(n) => n as usize,
            Len::NearBoundary { chunks, delta } => {
                let boundary = (chunks % 4) as usize * CHUNK_SIZE;
                boundary.saturating_add_signed(delta as isize)
            }
        }
    }
}

/// Generates a message in which every chunk is different, so that a chunk
/// returned in place of another is noticed.
pub fn message(len: &Len, seed: u8) -> Vec<u8> {
    (0..len.get())
        .map(|i| (i as u8) ^ ((i >> 8) as u8).wrapping_mul(167) ^ seed)
        .collect()
}

/// How a stream is driven: the size of each read or write, and which calls
/// fail with `WouldBlock` first.
#[derive(Arbitrary, Debug)]
pub struct Pacing {
    /// The size of each call, minus one, cycled. Empty means unlimited.
    sizes: Vec<u16>,
    /// Bit `i` makes call `i` (modulo 32) fail with `WouldBlock`.
    would_block: u32,
}

/// The position in a [`Pacing`].
pub struct Pace<'a> {
    pacing: &'a Pacing,
    step: usize,
    blocked: bool,
}

impl<'a> Pace<'a> {
    pub fn new(pacing: &'a Pacing) -> Self {
        Pace {
            pacing,
            step: 0,
            blocked: false,
        }
    }

    /// Returns the size of the next call, which is at least one, or `None`
    /// if it must fail with `WouldBlock`. It never returns `None` twice in a
    /// row, so that a caller that retries always makes progress.
    pub fn advance(&mut self) -> Option<usize> {
        let i = self.step;
        self.step += 1;
        let block = (self.pacing.would_block >> (i % 32)) & 1 == 1;
        if block && !self.blocked {
            self.blocked = true;
            return None;
        }
        self.blocked = false;
        Some(match self.pacing.sizes.len() {
            0 => usize::MAX,
            n => self.pacing.sizes[i % n] as usize + 1,
        })
    }
}

/// A reader that returns its data in pieces, and sometimes fails with
/// `WouldBlock`, like a non-blocking source.
pub struct Source<'a> {
    data: &'a [u8],
    pace: Pace<'a>,
}

impl<'a> Source<'a> {
    pub fn new(data: &'a [u8], pacing: &'a Pacing) -> Self {
        Source {
            data,
            pace: Pace::new(pacing),
        }
    }
}

impl Read for Source<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let Some(size) = self.pace.advance() else {
            return Err(io::ErrorKind::WouldBlock.into());
        };
        let n = self.data.len().min(size).min(buf.len());
        buf[..n].copy_from_slice(&self.data[..n]);
        self.data = &self.data[n..];
        Ok(n)
    }
}

/// A writer that accepts its data in pieces, and sometimes fails with
/// `WouldBlock`, like a non-blocking sink.
pub struct Sink<'a> {
    pub out: Vec<u8>,
    pace: Pace<'a>,
    reliable: Cell<bool>,
}

impl<'a> Sink<'a> {
    pub fn new(pacing: &'a Pacing) -> Self {
        Sink {
            out: Vec::new(),
            pace: Pace::new(pacing),
            reliable: Cell::new(false),
        }
    }

    /// Stops the sink from failing with `WouldBlock`. `EncryptWriter::finish`
    /// consumes the writer, so it can't be retried.
    pub fn set_reliable(&self) {
        self.reliable.set(true);
    }
}

impl Write for Sink<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let size = match self.pace.advance() {
            Some(size) => size,
            None if self.reliable.get() => 1,
            None => return Err(io::ErrorKind::WouldBlock.into()),
        };
        let n = buf.len().min(size);
        self.out.extend_from_slice(&buf[..n]);
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Reads until EOF or an error other than `WouldBlock`, into buffers sized
/// by `pacing`. Returns what was read before the error.
pub fn read_all(mut r: impl Read, pacing: &Pacing) -> (Vec<u8>, Option<io::Error>) {
    let mut pace = Pace::new(pacing);
    let mut out = Vec::new();
    let mut buf = vec![0; 1 << 16];
    loop {
        let Some(size) = pace.advance() else { continue };
        let size = size.min(buf.len());
        match r.read(&mut buf[..size]) {
            Ok(0) => return (out, None),
            Ok(n) => out.extend_from_slice(&buf[..n]),
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {}
            Err(e) => return (out, Some(e)),
        }
    }
}
