//! Wycheproof test vectors for c2sp.org/chunked-encryption, applied through
//! every public API. Raw mode is tested by the unit tests in src/raw.rs.

mod vectors;

use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

#[cfg(feature = "cobblestone-256")]
use cobblestone::Key256;
use cobblestone::{
    CobblestoneKey, DecryptReader, EncryptReader, EncryptWriter, Error, InvalidKeySize, Key,
    RandomAccessDecryptor, ciphertext_size, decrypt, encrypt, plaintext_size,
};
use vectors::Vector;

/// A reader that returns at most `piece` bytes per read.
struct Pieces<'a> {
    data: &'a [u8],
    piece: usize,
}

impl Read for Pieces<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.data.len().min(self.piece).min(buf.len());
        buf[..n].copy_from_slice(&self.data[..n]);
        self.data = &self.data[n..];
        Ok(n)
    }
}

fn pieces(data: &[u8], piece: usize) -> Pieces<'_> {
    Pieces { data, piece }
}

/// Reads until EOF or an error, checking that errors are sticky.
fn read_until_error(mut r: impl Read) -> (Vec<u8>, Option<io::Error>) {
    let mut data = Vec::new();
    let mut buf = [0; 5000];
    loop {
        match r.read(&mut buf) {
            Ok(0) => return (data, None),
            Ok(n) => data.extend_from_slice(&buf[..n]),
            Err(err) => {
                for _ in 0..3 {
                    assert!(r.read(&mut buf).is_err(), "stream did not keep failing");
                }
                return (data, Some(err));
            }
        }
    }
}

fn cobblestone_error(err: &io::Error) -> &Error {
    err.get_ref()
        .and_then(|e| e.downcast_ref::<Error>())
        .unwrap_or_else(|| panic!("not a cobblestone error: {err:?}"))
}

fn is_header_error(err: &Error) -> bool {
    matches!(err, Error::InvalidCommitment | Error::Truncated)
}

#[test]
fn wycheproof() {
    let vectors = vectors::load();
    assert!(!vectors.is_empty());
    let (mut count_128, mut count_256) = (0, 0);
    for v in &vectors {
        if v.valid {
            let len = v.msg_length.unwrap() as u64;
            assert_eq!(plaintext_size(v.ct.len() as u64), Ok(len), "{}", v.name);
            assert_eq!(ciphertext_size(len), Some(v.ct.len() as u64), "{}", v.name);
        }

        // The instantiation is selected by the type of the key.
        match v.aead.as_str() {
            "AEAD_AES_128_GCM" => {
                check_vector(v, Key::try_from(&v.key[..]), cobblestone::KEY_SIZE);
                count_128 += 1;
            }
            "AEAD_AES_256_GCM" => {
                // Without the feature, Cobblestone-256 is only tested in raw
                // mode, by the unit tests in src/raw.rs.
                #[cfg(feature = "cobblestone-256")]
                check_vector(v, Key256::try_from(&v.key[..]), cobblestone::KEY256_SIZE);
                count_256 += 1;
            }
            aead => panic!("unknown AEAD {aead}"),
        }
    }
    // Every vector of both instantiations goes through the public APIs.
    assert_eq!(count_128 + count_256, vectors.len());
    assert!(count_128 > 0 && count_256 > 0);
}

fn check_vector(v: &Vector, key: Result<impl CobblestoneKey, InvalidKeySize>, key_size: usize) {
    if v.has("InvalidKeySize") {
        // Keys are validated when a key is created, so no API can be called
        // with an invalid key.
        assert_ne!(v.key.len(), key_size);
        let err = key.err().expect("invalid key size accepted");
        assert_eq!(
            err.to_string(),
            format!(
                "invalid key size: {} bytes, expected {key_size}",
                v.key.len()
            ),
            "{}",
            v.name
        );
        return;
    }
    let key = key.unwrap();
    if v.valid {
        check_valid(v, &key);
        check_round_trip(v, &key);
    } else {
        check_invalid(v, &key);
    }
}

fn check_valid(v: &Vector, key: &impl CobblestoneKey) {
    v.check_message(&decrypt(key, &v.ctx, &v.ct).unwrap());

    for piece in [usize::MAX, 1000, 1] {
        if piece == 1 && v.ct.len() > 1 << 20 {
            continue;
        }
        let mut r = DecryptReader::new(key, &v.ctx, pieces(&v.ct, piece));
        let mut msg = Vec::new();
        r.read_to_end(&mut msg).unwrap();
        v.check_message(&msg);
        // Reads after the end keep returning EOF.
        assert_eq!(r.read(&mut [0; 10]).unwrap(), 0);
    }

    let mut r = RandomAccessDecryptor::new(key, &v.ctx, Cursor::new(&v.ct)).unwrap();
    assert_eq!(
        r.plaintext_len(),
        v.msg_length.unwrap() as u64,
        "{}",
        v.name
    );
    let mut msg = Vec::new();
    r.read_to_end(&mut msg).unwrap();
    v.check_message(&msg);
    assert_eq!(r.read(&mut [0; 10]).unwrap(), 0);

    // Read it again in pieces, exercising the cache and chunk boundaries.
    let mut pieced = Vec::new();
    let mut off = 0;
    while off < msg.len() {
        r.seek(SeekFrom::Start(off as u64)).unwrap();
        let mut buf = vec![0; 1000.min(msg.len() - off)];
        r.read_exact(&mut buf).unwrap();
        pieced.extend_from_slice(&buf);
        off += 1000;
    }
    v.check_message(&pieced);

    // Seek relative to the end, like an application reading a trailer would.
    let tail_len = msg.len().min(100);
    r.seek(SeekFrom::End(-(tail_len as i64))).unwrap();
    let mut tail = Vec::new();
    r.read_to_end(&mut tail).unwrap();
    assert_eq!(tail, msg[msg.len() - tail_len..], "{}", v.name);
    if msg.len() > 3000 {
        r.seek(SeekFrom::Start(1000)).unwrap();
        let mut range = vec![0; 2000];
        r.read_exact(&mut range).unwrap();
        assert_eq!(range, msg[1000..3000], "{}", v.name);
    }
    assert!(r.seek(SeekFrom::End(-(msg.len() as i64) - 1)).is_err());

    // Positional reads, which leave the Read/Seek position alone.
    r.seek(SeekFrom::Start(0)).unwrap();
    let mut off = 0;
    while off < msg.len() {
        let mut buf = vec![0; 1000.min(msg.len() - off)];
        r.read_exact_at(&mut buf, off as u64).unwrap();
        assert_eq!(buf, msg[off..off + buf.len()], "{}", v.name);
        off += 1000;
    }
    assert_eq!(r.stream_position().unwrap(), 0, "{}", v.name);
    r.read_exact_at(&mut [], msg.len() as u64).unwrap();
    for (len, at) in [(1, msg.len() as u64), (msg.len() + 1, 0), (1, u64::MAX)] {
        let err = r.read_exact_at(&mut vec![0; len], at).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof, "{}", v.name);
    }

    #[cfg(feature = "tokio")]
    tokio_tests::check_valid(v, key);
}

fn check_round_trip(v: &Vector, key: &impl CobblestoneKey) {
    let msg = decrypt(key, &v.ctx, &v.ct).unwrap();

    let ct = encrypt(key, &v.ctx, &msg).unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    v.check_message(&decrypt(key, &v.ctx, &ct).unwrap());

    let mut w = EncryptWriter::new(key, &v.ctx, Vec::new());
    for piece in msg.chunks(1000) {
        w.write_all(piece).unwrap();
    }
    let ct = w.finish().unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    v.check_message(&decrypt(key, &v.ctx, &ct).unwrap());

    let mut ct = Vec::new();
    EncryptReader::new(key, &v.ctx, pieces(&msg, 1000))
        .read_to_end(&mut ct)
        .unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    let mut r = RandomAccessDecryptor::new(key, &v.ctx, Cursor::new(&ct)).unwrap();
    let mut out = Vec::new();
    r.read_to_end(&mut out).unwrap();
    v.check_message(&out);

    #[cfg(feature = "tokio")]
    tokio_tests::check_round_trip(v, key, &msg);
}

fn check_invalid(v: &Vector, key: &impl CobblestoneKey) {
    assert!(decrypt(key, &v.ctx, &v.ct).is_err(), "{}", v.name);

    if v.has("HeaderFailure") {
        // Rejected before any chunk is decrypted, and without any output.
        let err = decrypt(key, &v.ctx, &v.ct).unwrap_err();
        assert!(is_header_error(&err), "{}: {err}", v.name);
        // The header is checked on the first read, before any output.
        let r = DecryptReader::new(key, &v.ctx, pieces(&v.ct, 7));
        let (data, err) = read_until_error(r);
        let err = err.expect("decryption succeeded");
        assert!(
            is_header_error(cobblestone_error(&err)),
            "{}: {err}",
            v.name
        );
        assert!(data.is_empty(), "{}", v.name);
        let err = RandomAccessDecryptor::new(key, &v.ctx, Cursor::new(&v.ct))
            .err()
            .unwrap();
        assert!(
            is_header_error(cobblestone_error(&err)),
            "{}: {err}",
            v.name
        );
        #[cfg(feature = "tokio")]
        tokio_tests::check_header_failure(v, key);
        return;
    }

    for piece in [usize::MAX, 1000, 1] {
        if piece == 1 && v.ct.len() > 1 << 20 {
            continue;
        }
        let r = DecryptReader::new(key, &v.ctx, pieces(&v.ct, piece));
        let (data, err) = read_until_error(r);
        assert!(err.is_some(), "{}: decryption succeeded", v.name);
        v.check_prefix(&data);
        if piece == 1 {
            // With a byte-by-byte source, every valid chunk is delivered
            // before the error.
            assert_eq!(data.len(), v.prefix_length(), "{}", v.name);
        }
    }

    // Authenticating the message length must fail, unless the final chunk is
    // valid.
    let r = RandomAccessDecryptor::new(key, &v.ctx, Cursor::new(&v.ct));
    if !v.has("ValidFinalChunk") {
        assert!(r.is_err(), "{}: opened for random access", v.name);
    } else {
        let mut r = r.unwrap();
        assert!(r.read_to_end(&mut Vec::new()).is_err(), "{}", v.name);
        // Reading only validly encrypted chunks succeeds.
        r.seek(SeekFrom::Start(0)).unwrap();
        let mut prefix = vec![0; v.prefix_length()];
        r.read_exact(&mut prefix).unwrap();
        v.check_prefix(&prefix);

        // The same, through positional reads. The prefix is whole chunks, so
        // the first invalid chunk starts right after it.
        let bad_chunk = Error::DecryptionFailed {
            chunk: (v.prefix_length() / 16384) as u64,
        };
        let len = r.plaintext_len() as usize;
        let err = r.read_exact_at(&mut vec![0; len], 0).unwrap_err();
        assert_eq!(cobblestone_error(&err), &bad_chunk, "{}", v.name);
        let mut prefix = vec![0; v.prefix_length()];
        r.read_exact_at(&mut prefix, 0).unwrap();
        v.check_prefix(&prefix);
        // The first byte past the valid prefix is in an invalid chunk.
        let err = r
            .read_exact_at(&mut [0], v.prefix_length() as u64)
            .unwrap_err();
        assert_eq!(cobblestone_error(&err), &bad_chunk, "{}", v.name);
    }

    #[cfg(feature = "tokio")]
    tokio_tests::check_invalid(v, key);
}

#[cfg(feature = "tokio")]
mod tokio_tests {
    use super::*;
    use cobblestone::tokio::{
        DecryptReader as AsyncDecryptReader, EncryptReader as AsyncEncryptReader,
        EncryptWriter as AsyncEncryptWriter,
    };
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    fn block_on<F: Future>(f: F) -> F::Output {
        tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap()
            .block_on(f)
    }

    /// An async reader that returns at most `piece` bytes per read, and
    /// returns Pending before every read.
    struct AsyncPieces<'a> {
        data: &'a [u8],
        piece: usize,
        pending: bool,
    }

    impl tokio::io::AsyncRead for AsyncPieces<'_> {
        fn poll_read(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &mut tokio::io::ReadBuf<'_>,
        ) -> std::task::Poll<io::Result<()>> {
            self.pending = !self.pending;
            if self.pending {
                cx.waker().wake_by_ref();
                return std::task::Poll::Pending;
            }
            let n = self.data.len().min(self.piece).min(buf.remaining());
            buf.put_slice(&self.data[..n]);
            self.data = &self.data[n..];
            std::task::Poll::Ready(Ok(()))
        }
    }

    fn async_pieces(data: &[u8], piece: usize) -> AsyncPieces<'_> {
        AsyncPieces {
            data,
            piece,
            pending: false,
        }
    }

    async fn read_until_error(
        mut r: impl tokio::io::AsyncRead + Unpin,
    ) -> (Vec<u8>, Option<io::Error>) {
        let mut data = Vec::new();
        let mut buf = [0; 5000];
        loop {
            match r.read(&mut buf).await {
                Ok(0) => return (data, None),
                Ok(n) => data.extend_from_slice(&buf[..n]),
                Err(err) => {
                    for _ in 0..3 {
                        assert!(
                            r.read(&mut buf).await.is_err(),
                            "stream did not keep failing"
                        );
                    }
                    return (data, Some(err));
                }
            }
        }
    }

    pub fn check_valid(v: &Vector, key: &impl CobblestoneKey) {
        block_on(async {
            for piece in [usize::MAX, 1000, 1] {
                if piece == 1 && v.ct.len() > 1 << 20 {
                    continue;
                }
                let mut r = AsyncDecryptReader::new(key, &v.ctx, async_pieces(&v.ct, piece));
                let mut msg = Vec::new();
                r.read_to_end(&mut msg).await.unwrap();
                v.check_message(&msg);
            }
        })
    }

    pub fn check_round_trip(v: &Vector, key: &impl CobblestoneKey, msg: &[u8]) {
        block_on(async {
            let mut w = AsyncEncryptWriter::new(key, &v.ctx, Vec::new());
            for piece in msg.chunks(1000) {
                w.write_all(piece).await.unwrap();
            }
            w.shutdown().await.unwrap();
            let ct = w.into_inner();
            assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
            v.check_message(&decrypt(key, &v.ctx, &ct).unwrap());

            let mut ct = Vec::new();
            AsyncEncryptReader::new(key, &v.ctx, async_pieces(msg, 1000))
                .read_to_end(&mut ct)
                .await
                .unwrap();
            assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
            v.check_message(&decrypt(key, &v.ctx, &ct).unwrap());
        })
    }

    pub fn check_header_failure(v: &Vector, key: &impl CobblestoneKey) {
        block_on(async {
            let r = AsyncDecryptReader::new(key, &v.ctx, async_pieces(&v.ct, 7));
            let (data, err) = read_until_error(r).await;
            let err = err.expect("decryption succeeded");
            assert!(
                is_header_error(cobblestone_error(&err)),
                "{}: {err}",
                v.name
            );
            assert!(data.is_empty());
        })
    }

    pub fn check_invalid(v: &Vector, key: &impl CobblestoneKey) {
        block_on(async {
            for piece in [usize::MAX, 1000, 1] {
                if piece == 1 && v.ct.len() > 1 << 20 {
                    continue;
                }
                let r = AsyncDecryptReader::new(key, &v.ctx, async_pieces(&v.ct, piece));
                let (data, err) = read_until_error(r).await;
                assert!(err.is_some(), "{}: decryption succeeded", v.name);
                v.check_prefix(&data);
                if piece == 1 {
                    // With a byte-by-byte source, every valid chunk is
                    // delivered before the error.
                    assert_eq!(data.len(), v.prefix_length(), "{}", v.name);
                }
            }
        })
    }
}

/// A writer that accepts at most 7 bytes per write, and fails every other
/// write with `Interrupted`.
struct Stingy {
    out: Vec<u8>,
    interrupt: bool,
}

impl Write for Stingy {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.interrupt = !self.interrupt;
        if self.interrupt {
            return Err(io::ErrorKind::Interrupted.into());
        }
        let n = buf.len().min(7);
        self.out.extend_from_slice(&buf[..n]);
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn partial_writes() {
    let key = Key::generate();
    let msg: Vec<u8> = (0..40_000u32).map(|i| i as u8).collect();
    let sink = Stingy {
        out: Vec::new(),
        interrupt: false,
    };
    let mut w = EncryptWriter::new(&key, b"", sink);
    w.write_all(&msg).unwrap();
    w.flush().unwrap();
    let ct = w.finish().unwrap().out;
    assert_eq!(decrypt(&key, b"", &ct).unwrap(), msg);
}

#[test]
fn writer_reports_sink_errors() {
    struct Broken;
    impl Write for Broken {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(io::ErrorKind::BrokenPipe.into())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let key = Key::generate();
    let mut w = EncryptWriter::new(&key, b"", Broken);
    assert!(w.write(b"x").is_err());
    // The error is sticky: the ciphertext is incomplete.
    assert!(w.finish().is_err());
}

#[test]
fn empty_writer_produces_valid_ciphertext() {
    let key = Key::generate();
    let ct = EncryptWriter::new(&key, b"", Vec::new()).finish().unwrap();
    assert_eq!(decrypt(&key, b"", &ct).unwrap(), b"");
}

#[cfg(feature = "tokio")]
#[test]
fn async_writer_with_pending_sink() {
    use std::pin::Pin;
    use std::task::{Context, Poll};
    use tokio::io::AsyncWriteExt;

    /// An async writer that returns Pending before every write, and accepts
    /// at most 7 bytes per write.
    struct Slow {
        out: Vec<u8>,
        pending: bool,
        shut_down: bool,
    }

    impl tokio::io::AsyncWrite for Slow {
        fn poll_write(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            self.pending = !self.pending;
            if self.pending {
                cx.waker().wake_by_ref();
                return Poll::Pending;
            }
            let n = buf.len().min(7);
            self.out.extend_from_slice(&buf[..n]);
            Poll::Ready(Ok(n))
        }
        fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
        fn poll_shutdown(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
            self.shut_down = true;
            Poll::Ready(Ok(()))
        }
    }

    let key = Key::generate();
    let msg: Vec<u8> = (0..40_000u32).map(|i| (i * 7) as u8).collect();
    let sink = Slow {
        out: Vec::new(),
        pending: false,
        shut_down: false,
    };
    let sink = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(async {
            let mut w = cobblestone::tokio::EncryptWriter::new(&key, b"x", sink);
            w.write_all(&msg).await.unwrap();
            w.flush().await.unwrap();
            w.shutdown().await.unwrap();
            assert!(w.write(b"more").await.is_err());
            w.into_inner()
        });
    assert!(sink.shut_down);
    assert_eq!(decrypt(&key, b"x", &sink.out).unwrap(), msg);
}

/// A reader that returns at most `piece` bytes per read, and fails every
/// other read with `kind`.
struct Flaky<'a> {
    data: &'a [u8],
    piece: usize,
    fail: bool,
    kind: io::ErrorKind,
}

fn flaky(data: &[u8], piece: usize, kind: io::ErrorKind) -> Flaky<'_> {
    Flaky {
        data,
        piece,
        fail: false,
        kind,
    }
}

impl Read for Flaky<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.fail = !self.fail;
        if self.fail {
            return Err(self.kind.into());
        }
        let n = self.data.len().min(self.piece).min(buf.len());
        buf[..n].copy_from_slice(&self.data[..n]);
        self.data = &self.data[n..];
        Ok(n)
    }
}

/// Reads to the end into a buffer of `buf_len` bytes, retrying `WouldBlock`
/// like a caller polling a non-blocking source would.
fn read_retrying(mut r: impl Read, buf_len: usize) -> io::Result<Vec<u8>> {
    let mut out = Vec::new();
    let mut buf = vec![0; buf_len];
    loop {
        match r.read(&mut buf) {
            Ok(0) => return Ok(out),
            Ok(n) => out.extend_from_slice(&buf[..n]),
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {}
            Err(e) => return Err(e),
        }
    }
}

/// Message lengths around the chunk boundaries.
const BOUNDARY_LENGTHS: [usize; 7] = [0, 1, 16383, 16384, 16385, 32768, 40000];

fn message(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i * 31) as u8).collect()
}

#[test]
fn readers_resume_after_transient_errors() {
    let key = Key::generate();
    for len in BOUNDARY_LENGTHS {
        let msg = message(len);
        let ct = encrypt(&key, b"ctx", &msg).unwrap();
        for kind in [io::ErrorKind::WouldBlock, io::ErrorKind::Interrupted] {
            // Interrupted is retried inside the reader, and WouldBlock by the
            // caller. Either way, no data may be lost or duplicated.
            let r = DecryptReader::new(&key, b"ctx", flaky(&ct, 7, kind));
            assert_eq!(read_retrying(r, 4096).unwrap(), msg, "{kind:?}, {len}");

            let r = EncryptReader::new(&key, b"ctx", flaky(&msg, 7, kind));
            let ct = read_retrying(r, 4096).unwrap();
            assert_eq!(decrypt(&key, b"ctx", &ct).unwrap(), msg, "{kind:?}, {len}");
        }
    }
}

#[test]
fn one_byte_buffers() {
    let key = Key::generate();
    for len in BOUNDARY_LENGTHS {
        let msg = message(len);
        let ct = encrypt(&key, b"ctx", &msg).unwrap();

        let r = DecryptReader::new(&key, b"ctx", &ct[..]);
        assert_eq!(read_retrying(r, 1).unwrap(), msg, "decrypt, {len}");

        let r = EncryptReader::new(&key, b"ctx", &msg[..]);
        let ct = read_retrying(r, 1).unwrap();
        assert_eq!(
            decrypt(&key, b"ctx", &ct).unwrap(),
            msg,
            "encrypt reader, {len}"
        );

        let mut w = EncryptWriter::new(&key, b"ctx", Vec::new());
        for byte in &msg {
            w.write_all(std::slice::from_ref(byte)).unwrap();
        }
        let ct = w.finish().unwrap();
        assert_eq!(
            decrypt(&key, b"ctx", &ct).unwrap(),
            msg,
            "encrypt writer, {len}"
        );
    }
}

#[test]
fn every_message_gets_a_fresh_salt() {
    // The spec requires that salts never repeat under a key. Encrypting the
    // same message twice must give different salts, and so different
    // ciphertexts, through every encryption API.
    let key = Key::generate();
    let encryptions: [fn(&Key) -> Vec<u8>; 3] = [
        |key| encrypt(key, b"", b"same").unwrap(),
        |key| {
            let mut w = EncryptWriter::new(key, b"", Vec::new());
            w.write_all(b"same").unwrap();
            w.finish().unwrap()
        },
        |key| {
            let mut ct = Vec::new();
            EncryptReader::new(key, b"", &b"same"[..])
                .read_to_end(&mut ct)
                .unwrap();
            ct
        },
    ];
    for f in encryptions {
        let (a, b) = (f(&key), f(&key));
        assert_ne!(a[..24], b[..24], "salt repeated");
        assert_ne!(a[..24], [0; 24], "salt is all zeros");
        assert_ne!(a, b);
    }
}

#[test]
fn final_chunk_shorter_than_a_tag_is_truncation() {
    let key = Key::generate();
    let ct = encrypt(&key, b"", &message(16384)).unwrap();
    // The ciphertext is the header, one full chunk, and an empty final chunk
    // that is just a 16-byte tag. Cut that tag short.
    for cut in [1, 15] {
        let truncated = &ct[..ct.len() - cut];
        assert_eq!(decrypt(&key, b"", truncated), Err(Error::Truncated));
        let r = DecryptReader::new(&key, b"", truncated);
        let (data, err) = read_until_error(r);
        let err = err.expect("decryption succeeded");
        assert_eq!(cobblestone_error(&err), &Error::Truncated);
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
        // The full chunk before it was valid, and may be released.
        assert!(data.len() <= 16384);
    }
}

#[cfg(feature = "cobblestone-256")]
#[test]
fn instantiations_are_not_interchangeable() {
    // The header doesn't record the instantiation, so a ciphertext of one
    // must fail the commitment check under the other, even with related key
    // bytes.
    let key = Key::generate();
    let mut bytes = [0; 32];
    bytes[..16].copy_from_slice(key.as_bytes());
    let key256 = Key256::from(bytes);

    let ct = encrypt(&key, b"", b"hello").unwrap();
    assert_eq!(decrypt(&key256, b"", &ct), Err(Error::InvalidCommitment));
    let ct = encrypt(&key256, b"", b"hello").unwrap();
    assert_eq!(decrypt(&key, b"", &ct), Err(Error::InvalidCommitment));
    assert_eq!(decrypt(&key256, b"", &ct).unwrap(), b"hello");
}
