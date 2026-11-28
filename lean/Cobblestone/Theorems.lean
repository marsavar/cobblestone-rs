module
public import Cobblestone.Proofs.Conformance
public import Cobblestone.Proofs.StreamMessage
@[expose] public section

/-!
# What is proved

The top-level results, stated in full. Together with `Spec.lean`, which states
the scheme from the specification, and `Assumptions.lean`, which states what is
assumed about the primitives, these are the parts a reviewer needs to read.
The proofs in `Proofs/` only need to be checked by Lean.

In these statements:

- `encryptMsg` and `decryptMsg` are the in-memory `encrypt` and `decrypt` of
  `src/lib.rs`: the header code of `src/header.rs` and the chunk layer of
  `src/raw.rs`, as Aeneas translates them, driven by hand-written mirrors of the
  loops in `src/lib.rs` (`Proofs/Message.lean`, `Proofs/Full.lean`).
- `streamEncryptMsg` and `streamDecryptBody` are the streaming types: the buffering of
  `src/buffer.rs`, as Aeneas translates it, driven by any sequence of
  operations that the loops in `src/stream.rs` can perform, modeled by hand in
  `Proofs/Stream.lean`.
- `macI`, `initI` and `ctI` are HMAC-SHA-512, AES-GCM and the constant-time
  comparison as the code reaches them, and `P` the primitives of the
  specification.

The specification defines encryption, `spec.encrypt`, but not a decryption
function. So encryption is proved equal to it, while decryption is proved to
accept exactly its ciphertexts and return their messages (`decrypt_sound` and
`decrypt_complete`). Which error decryption returns for an invalid ciphertext is
not part of the specification, and is not part of these theorems.
-/

open Aeneas Aeneas.Std Result

namespace cobblestone.theorems

open spec raw header conformance buffer

variable {M A C : Type} {macI : Mac M} {initI : AeadInit A} {ctI : CtEq C} {P : Primitives}
  {st : M → List U8 × List U8}

/-- Key derivation computes the specification: the AEAD is created from
`spec.aeadKey`, and the base nonce and commitment are `spec.baseNonce` and
`spec.commitment`. -/
theorem derive_conforms (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) :
    derive macI initI (toSuite ins) key salt context okm t ⦃ cc _ _ =>
      (∃ k : Slice U8, k.val = aeadKey P ins key.val salt.val context.val ∧
        initI.new (toSuite ins) k = ok cc.1.aead) ∧
      cc.1.base_nonce.val = baseNonce P ins key.val salt.val context.val ∧
      cc.2.val = commitment P ins key.val salt.val context.val ⦄ :=
  derive_eq_spec hM hI ins key hk salt context okm t

/-- Chunk nonces compute the specification: for every chunk index the encryptor
and decryptor can use, the nonce is `spec.chunkNonce` of the base nonce. -/
theorem nonce_conforms (inst : ChunkAead A) (cipher : ChunkCipher A) (i : U64)
    (hi : i.val < maxChunks) (n : Std.Array U8 12#usize)
    (hn : ChunkCipher.nonce inst cipher i = ok n) :
    n.val = chunkNonce cipher.base_nonce.val i.val :=
  nonce_eq_chunkNonce inst cipher i hi n hn

/-- Encryption computes the specification: for every key of the instantiation's
size, salt, context, and message of at most 2^38 chunks, `encrypt` succeeds and
returns `spec.encrypt`. -/
theorem encrypt_conforms (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hS : SealImplements P initI) (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (m : Bytes) (hm : numChunks m ≤ maxChunks) :
    ∃ ct, spec.encrypt P ins key.val salt.val context.val m = some ct ∧
      encryptMsg macI initI (toSuite ins) key salt context okm t m = ok (.Ok ct) :=
  encryptMsg_eq_spec hM hI hS hA ins key hk salt context okm t m hm

/-- Decryption only accepts ciphertexts of the specification: if `decrypt`
returns `m`, the ciphertext is `spec.encrypt` of `m`, with the salt in its
header. So any truncation, reordering, modification or extension is rejected. -/
theorem decrypt_sound (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hC : CtEqLaws ctI) (hS : SealImplements P initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hT : ∀ a, AeadTagCheck initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins) (context : Slice U8)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (ct m : Bytes)
    (h : decryptMsg macI initI ctI (toSuite ins) key context okm t ct = ok (.Ok m)) :
    spec.encrypt P ins key.val (ct.take saltLen) context.val m = some ct :=
  decryptMsg_sound hM hI hC hS hA hT ins key hk context okm t ct m h

/-- Decryption accepts every ciphertext of the specification, and returns its
message. -/
theorem decrypt_complete (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hC : CtEqLaws ctI) (hS : SealImplements P initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hCo : ∀ a, AeadCorrect initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (m ct : Bytes)
    (h : spec.encrypt P ins key.val salt.val context.val m = some ct) :
    decryptMsg macI initI ctI (toSuite ins) key context okm t ct = ok (.Ok m) :=
  decryptMsg_complete hM hI hC hS hA hCo ins key hk salt context okm t m ct h

/-- Streaming encryption produces the in-memory ciphertext of the plaintext it
accepted, for any sequence of writes, reads and drains of any sizes, once it
has finished and all its output has been drained. -/
theorem stream_encrypt_conforms (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a) (ins : Instantiation) (key : Slice U8)
    (hk : key.length = keyLen ins) (salt : Std.Array U8 24#usize) (context : Slice U8)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (buf : Slice U8)
    (hbuf : buf.length = 16400) (ops : List EncOp) (drains : List Usize) :
    streamEncryptMsg macI initI (toSuite ins) key salt context okm t buf ops drains ⦃ o =>
      ∀ out acc, o = some (out, acc, true) →
        encryptMsg macI initI (toSuite ins) key salt context okm t acc = ok (.Ok out) ⦄ :=
  streamEncrypt_eq_encryptMsg macI initI hM hI hA (toSuite ins) key (by rw [hk, keyLen_eq]) salt
    context okm t buf hbuf ops drains

/-- Streaming decryption agrees with in-memory decryption once the header has
been accepted, for any sequence of reads and drains of any sizes: when the
final chunk is authenticated and all its plaintext read out, the plaintext is
the in-memory one, and when it fails, in-memory decryption fails with the same
error. -/
theorem stream_decrypt_conforms (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (ins : Instantiation) (key context : Slice U8) (hdr : Std.Array U8 56#usize)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (cipher : ChunkCipher A)
    (okm' : Std.Array U8 76#usize) (t' : Std.Array U8 64#usize)
    (hopen : open_header macI initI ctI (toSuite ins) key context hdr okm t =
      ok (.Ok cipher, okm', t'))
    (buf : Slice U8) (hbuf : buf.length = 16400) (ops : List DecOp) :
    streamDecryptBody initI cipher buf ops ⦃ x =>
      (x.1.dec.done = true → x.1.pos = x.1.end →
        decryptMsg macI initI ctI (toSuite ins) key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Ok x.2.2.1)) ∧
      (∀ e, x.1.dec.failed = some e →
        decryptMsg macI initI ctI (toSuite ins) key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Err e)) ⦄ :=
  streamDecrypt_eq_decryptMsg macI initI ctI hA (toSuite ins) key context hdr okm t cipher okm' t'
    hopen buf hbuf ops

end cobblestone.theorems
