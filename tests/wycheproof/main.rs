//! Wycheproof test vectors for c2sp.org/chunked-encryption, applied through
//! every public API. Raw mode is tested by the unit tests in src/raw.rs.

mod vectors;

use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

use cobblestone::{
    DecryptReader, EncryptReader, EncryptWriter, Error, Key, RandomAccessDecryptor,
    ciphertext_size, decrypt, encrypt, plaintext_size,
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
                assert!(r.read(&mut buf).is_err(), "stream did not keep failing");
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
    for v in &vectors {
        if v.valid {
            let len = v.msg_length.unwrap() as u64;
            assert_eq!(plaintext_size(v.ct.len() as u64), Ok(len), "{}", v.name);
            assert_eq!(ciphertext_size(len), Some(v.ct.len() as u64), "{}", v.name);
        }

        if !v.is_cobblestone_128() && v.has("HeaderFailure") {
            // Cobblestone-256 is only implemented in raw mode.
        } else if v.has("InvalidKeySize") {
            check_invalid_key(v);
        } else if v.is_cobblestone_128() && v.valid {
            check_valid(v);
            check_round_trip(v);
        } else if v.is_cobblestone_128() {
            check_invalid(v);
        }
    }
}

fn check_invalid_key(v: &Vector) {
    // Keys are validated when a Key is created, so no API can be called with
    // an invalid key.
    assert_ne!(v.key.len(), cobblestone::KEY_SIZE);
    assert_eq!(
        Key::try_from(&v.key[..]),
        Err(Error::InvalidKeySize(v.key.len())),
        "{}",
        v.name
    );
}

fn check_valid(v: &Vector) {
    v.check_message(&decrypt(&v.input_key(), &v.ctx, &v.ct).unwrap());

    for piece in [usize::MAX, 1000, 1] {
        if piece == 1 && v.ct.len() > 1 << 20 {
            continue;
        }
        let mut r = DecryptReader::new(&v.input_key(), &v.ctx, pieces(&v.ct, piece)).unwrap();
        let mut msg = Vec::new();
        r.read_to_end(&mut msg).unwrap();
        v.check_message(&msg);
        // Reads after the end keep returning EOF.
        assert_eq!(r.read(&mut [0; 10]).unwrap(), 0);
    }

    let mut r = RandomAccessDecryptor::new(&v.input_key(), &v.ctx, Cursor::new(&v.ct)).unwrap();
    assert_eq!(r.len(), v.msg_length.unwrap() as u64, "{}", v.name);
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
    tokio_tests::check_valid(v);
}

fn check_round_trip(v: &Vector) {
    let msg = decrypt(&v.input_key(), &v.ctx, &v.ct).unwrap();

    let ct = encrypt(&v.input_key(), &v.ctx, &msg).unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    v.check_message(&decrypt(&v.input_key(), &v.ctx, &ct).unwrap());

    let mut w = EncryptWriter::new(&v.input_key(), &v.ctx, Vec::new()).unwrap();
    for piece in msg.chunks(1000) {
        w.write_all(piece).unwrap();
    }
    let ct = w.finish().unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    v.check_message(&decrypt(&v.input_key(), &v.ctx, &ct).unwrap());

    let mut ct = Vec::new();
    EncryptReader::new(&v.input_key(), &v.ctx, pieces(&msg, 1000))
        .read_to_end(&mut ct)
        .unwrap();
    assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
    let mut r = RandomAccessDecryptor::new(&v.input_key(), &v.ctx, Cursor::new(&ct)).unwrap();
    let mut out = Vec::new();
    r.read_to_end(&mut out).unwrap();
    v.check_message(&out);

    #[cfg(feature = "tokio")]
    tokio_tests::check_round_trip(v, &msg);
}

fn check_invalid(v: &Vector) {
    assert!(
        decrypt(&v.input_key(), &v.ctx, &v.ct).is_err(),
        "{}",
        v.name
    );

    if v.has("HeaderFailure") {
        // Rejected before any chunk is decrypted, and without any output.
        let err = decrypt(&v.input_key(), &v.ctx, &v.ct).unwrap_err();
        assert!(is_header_error(&err), "{}: {err}", v.name);
        let err = DecryptReader::new(&v.input_key(), &v.ctx, &v.ct[..])
            .err()
            .unwrap();
        assert!(
            is_header_error(cobblestone_error(&err)),
            "{}: {err}",
            v.name
        );
        let err = RandomAccessDecryptor::new(&v.input_key(), &v.ctx, Cursor::new(&v.ct))
            .err()
            .unwrap();
        assert!(
            is_header_error(cobblestone_error(&err)),
            "{}: {err}",
            v.name
        );
        #[cfg(feature = "tokio")]
        tokio_tests::check_header_failure(v);
        return;
    }

    for piece in [usize::MAX, 1000, 1] {
        if piece == 1 && v.ct.len() > 1 << 20 {
            continue;
        }
        let r = DecryptReader::new(&v.input_key(), &v.ctx, pieces(&v.ct, piece)).unwrap();
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
    let r = RandomAccessDecryptor::new(&v.input_key(), &v.ctx, Cursor::new(&v.ct));
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
    }

    #[cfg(feature = "tokio")]
    tokio_tests::check_invalid(v);
}

#[cfg(feature = "tokio")]
mod tokio_tests {
    use super::*;
    use cobblestone::tokio::{AsyncDecryptReader, AsyncEncryptReader, AsyncEncryptWriter};
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
                    assert!(
                        r.read(&mut buf).await.is_err(),
                        "stream did not keep failing"
                    );
                    return (data, Some(err));
                }
            }
        }
    }

    pub fn check_valid(v: &Vector) {
        block_on(async {
            for piece in [usize::MAX, 1000] {
                let mut r =
                    AsyncDecryptReader::new(&v.input_key(), &v.ctx, async_pieces(&v.ct, piece));
                let mut msg = Vec::new();
                r.read_to_end(&mut msg).await.unwrap();
                v.check_message(&msg);
            }
        })
    }

    pub fn check_round_trip(v: &Vector, msg: &[u8]) {
        block_on(async {
            let mut w = AsyncEncryptWriter::new(&v.input_key(), &v.ctx, Vec::new());
            for piece in msg.chunks(1000) {
                w.write_all(piece).await.unwrap();
            }
            w.shutdown().await.unwrap();
            let ct = w.into_inner();
            assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
            v.check_message(&decrypt(&v.input_key(), &v.ctx, &ct).unwrap());

            let mut ct = Vec::new();
            AsyncEncryptReader::new(&v.input_key(), &v.ctx, async_pieces(msg, 1000))
                .read_to_end(&mut ct)
                .await
                .unwrap();
            assert_eq!(ct.len(), v.ct.len(), "{}", v.name);
            v.check_message(&decrypt(&v.input_key(), &v.ctx, &ct).unwrap());
        })
    }

    pub fn check_header_failure(v: &Vector) {
        block_on(async {
            let r = AsyncDecryptReader::new(&v.input_key(), &v.ctx, async_pieces(&v.ct, 7));
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

    pub fn check_invalid(v: &Vector) {
        block_on(async {
            for piece in [usize::MAX, 1000] {
                let r = AsyncDecryptReader::new(&v.input_key(), &v.ctx, async_pieces(&v.ct, piece));
                let (data, err) = read_until_error(r).await;
                assert!(err.is_some(), "{}: decryption succeeded", v.name);
                v.check_prefix(&data);
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
    let mut w = EncryptWriter::new(&key, b"", sink).unwrap();
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
    assert!(EncryptWriter::new(&key, b"", Broken).is_err());
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
            let mut w = cobblestone::tokio::AsyncEncryptWriter::new(&key, b"x", sink);
            w.write_all(&msg).await.unwrap();
            w.flush().await.unwrap();
            w.shutdown().await.unwrap();
            assert!(w.write(b"more").await.is_err());
            w.into_inner()
        });
    assert!(sink.shut_down);
    assert_eq!(decrypt(&key, b"x", &sink.out).unwrap(), msg);
}
