# Test vectors

These files are unmodified copies of the Wycheproof test vectors for
c2sp.org/chunked-encryption, from the C2SP Wycheproof repository:

| File | Upstream path |
|---|---|
| `c2sp_chunked_encryption_aes_128_gcm_test.json` | `testvectors_v1/c2sp_chunked_encryption_aes_128_gcm_test.json` |
| `c2sp_chunked_encryption_aes_256_gcm_test.json` | `testvectors_v1/c2sp_chunked_encryption_aes_256_gcm_test.json` |

- Repository: https://github.com/C2SP/wycheproof
- Commit: `b61843a9a5115bb758134b6a1f5d5e502d445342` (2026-07-13)

The files' headers say "See doc/c2sp_chunked_encryption.md". That path is in
the upstream repository, not this one:
https://github.com/C2SP/wycheproof/blob/b61843a9a5115bb758134b6a1f5d5e502d445342/doc/c2sp_chunked_encryption.md

They are kept byte-for-byte identical to upstream, so they can be checked
against it:

```text
2e0a512c47bfae6efd0b59644ab72f3dd7e80e4f74d6642c2c10427a02b095db  c2sp_chunked_encryption_aes_128_gcm_test.json
0f8e35568d59649fb55fb0e5602dc678dc8910d6822beef4945aee0b5994ef05  c2sp_chunked_encryption_aes_256_gcm_test.json
```

To update them, copy the files from a newer upstream commit and update the
commit and hashes above.

## License

Copyright 2016-2026 The Wycheproof Authors. Licensed under the Apache License,
Version 2.0; see [LICENSE](LICENSE) in this directory. The rest of this crate
is licensed under BSD-3-Clause.
