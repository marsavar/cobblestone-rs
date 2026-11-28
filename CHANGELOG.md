# Changelog

## [0.3.1](https://github.com/marsavar/cobblestone-rs/compare/v0.3.0...v0.3.1) (2026-11-28)


### Miscellaneous Chores

* release 0.3.1 ([466150b](https://github.com/marsavar/cobblestone-rs/commit/466150b4526db020c8efabf420fa6fafc87b126d))

## [0.3.0](https://github.com/marsavar/cobblestone-rs/compare/v0.2.0...v0.3.0) (2026-11-15)


### ⚠ BREAKING CHANGES

* **tokio:** tokio::EncryptWriter::into_inner now returns Result<W, IntoInnerError<EncryptWriter<W>>> instead of W.

### Features

* **tokio:** make EncryptWriter::into_inner fail unless shut down ([47341ed](https://github.com/marsavar/cobblestone-rs/commit/47341ed74ce33f3f1b081071fe1702328ecdfd0d))


### Bug Fixes

* **deps:** bump ctutils to 0.4.8 for RUSTSEC-2026-0385 ([509a639](https://github.com/marsavar/cobblestone-rs/commit/509a639ec77cecacf067f9b4fd62f4b12d78528b))

## [0.2.0](https://github.com/marsavar/cobblestone-rs/compare/v0.1.0...v0.2.0) (2026-10-31)


### Features

* add Cobblestone-256 behind the cobblestone-256 feature ([806b35f](https://github.com/marsavar/cobblestone-rs/commit/806b35fa602b27fa1819d0ae83f7d6924dcf2db7))
* cobblestone-256 ([70f3343](https://github.com/marsavar/cobblestone-rs/commit/70f334379bee3de8aafc62588ccc3f16ff25d3d2))

## 0.1.0 (2026-10-15)


### Features

* initial release ([65d4642](https://github.com/marsavar/cobblestone-rs/commit/65d464248df070a466a6451b78676a4f88ed59fe))
