# cobblestone

[![CI](https://github.com/marsavar/cobblestone-rs/actions/workflows/ci.yaml/badge.svg)](https://github.com/marsavar/cobblestone-rs/actions/workflows/ci.yaml)
[![crates.io](https://img.shields.io/crates/v/cobblestone.svg)](https://crates.io/crates/cobblestone)
[![docs.rs](https://img.shields.io/docsrs/cobblestone)](https://docs.rs/cobblestone)

A Rust implementation of **Cobblestone-128**, the chunked (streaming)
encryption scheme specified at
[c2sp.org/chunked-encryption](https://c2sp.org/chunked-encryption).

It supports authenticated streaming encryption and decryption and
authenticated random access, and is interoperable with the Go, Python and
TypeScript implementations.

Cobblestone-256, the compliance-oriented instantiation with AES-256-GCM, is
available behind the `cobblestone-256` feature, for environments that require
256-bit keys.

## Installation

```sh
cargo add cobblestone
# With the async API:
cargo add cobblestone --features tokio
```

Requires Rust 1.89 or later.

## Usage

In memory:

```rust
use cobblestone::{Key, decrypt, encrypt};

fn main() -> Result<(), cobblestone::Error> {
    let key = Key::generate();
    let ciphertext = encrypt(&key, b"file.txt", b"hello world")?;
    let plaintext = decrypt(&key, b"file.txt", &ciphertext)?;
    assert_eq!(plaintext, b"hello world");
    Ok(())
}
```

Streaming, with constant memory use whatever the size of the message:

```rust
use std::io::{self, Read, Write};

use cobblestone::{DecryptReader, EncryptWriter, Key};

fn main() -> io::Result<()> {
    let key = Key::generate();

    let mut w = EncryptWriter::new(&key, b"backup", Vec::new());
    w.write_all(b"hello ")?;
    w.write_all(b"world")?;
    let ciphertext = w.finish()?; // Required: writes the final chunk.

    let mut r = DecryptReader::new(&key, b"backup", &ciphertext[..]);
    let mut plaintext = Vec::new();
    r.read_to_end(&mut plaintext)?;
    assert_eq!(plaintext, b"hello world");
    Ok(())
}
```

For random access and async examples, guidance on keys and context, error
handling, and choosing between the blocking and async APIs, see the
[documentation][docs]. The API reference is on
[docs.rs](https://docs.rs/cobblestone).

[docs]: https://github.com/marsavar/cobblestone-rs/blob/main/docs.md

## Development

This crate was largely written by Claude, Anthropic's AI model, under my
direction and review. It passes the full Wycheproof test suite for the
scheme, but it has not been independently audited. Please report problems
in the [issue tracker](https://github.com/marsavar/cobblestone-rs/issues),
and I will do my best to address them.

## Acknowledgements

The scheme was designed by Filippo Valsorda. This crate's structure follows his
Go implementation, [filippo.io/cobblestone](https://github.com/FiloSottile/cobblestone),
and its test suite follows that of [cobblestone.ts](https://github.com/FiloSottile/cobblestone.ts).
This is an independent implementation, not affiliated with or endorsed by
either project.

## License

BSD-3-Clause; see [LICENSE](LICENSE).

The test vectors in `tests/testdata` are from the C2SP Wycheproof project and
remain under its Apache License 2.0, Copyright 2016-2026 The Wycheproof
Authors; see `tests/testdata/LICENSE`. They are only used by the tests.
The specification at c2sp.org is licensed under CC BY 4.0.
