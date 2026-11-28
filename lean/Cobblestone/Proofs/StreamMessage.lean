module
public import Cobblestone.Proofs.Stream
public import Cobblestone.Proofs.Full
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone

open header raw buffer

-- No binder with a `#usize` literal goes in `variable`: its proof would be
-- private to this module, and the theorems' types unusable from other modules.
variable {M A C : Type} (macI : Mac M) (initI : AeadInit A) (ctI : CtEq C)

/-- A streaming encryptor started from a new header, as `EncryptWrite::new` and
`EncryptReader::new` do. -/
def streamEncryptMsg (suite : Suite) (key : Slice U8) (salt : Std.Array U8 24#usize)
    (context : Slice U8) (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize)
    (buf : Slice U8) (ops : List EncOp) (drains : List Usize) :
    Result (Option (List U8 × List U8 × Bool)) := do
  let r ← new_header macI initI suite key salt context okm t
  streamEncrypt initI.rawChunkAeadInst r.1.2 buf r.1.1.to_slice ops drains

/-- A streaming decryptor started once the header has been accepted with
`cipher`, as `DecryptReader` does. -/
def streamDecryptBody (cipher : ChunkCipher A) (buf : Slice U8) (ops : List DecOp) :
    Result (DecryptBuffer A × Slice U8 × List U8 × List U8) := do
  let dec ← Decryptor.new initI.rawChunkAeadInst cipher
  streamDecrypt initI.rawChunkAeadInst dec buf ops

/-- `EncryptWrite` and `EncryptRead`, started from a new header, produce exactly
the one-shot encryption of the plaintext they accepted. -/
theorem streamEncrypt_eq_encryptMsg {hmac : List U8 → List U8 → Std.Array U8 64#usize}
    {st : M → List U8 × List U8} (hM : MacLaws macI hmac st) (hI : AeadInitLaws initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a) (suite : Suite) (key : Slice U8)
    (hk : key.length = suiteKeyLen suite) (salt : Std.Array U8 24#usize) (context : Slice U8)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (buf : Slice U8)
    (hbuf : buf.length = 16400) (ops : List EncOp) (drains : List Usize) :
    streamEncryptMsg macI initI suite key salt context okm t buf ops drains ⦃ o =>
      ∀ out acc, o = some (out, acc, true) →
        encryptMsg macI initI suite key salt context okm t acc = ok (.Ok out) ⦄ := by
  obtain ⟨⟨he, okm1, t1⟩, hnh, cm, -, -, hnext, hfin⟩ :=
    spec_ok_eq (new_header_spec hM hI suite key salt context okm t hk)
  rw [streamEncryptMsg, hnh, bind_ok]
  apply WP.spec_mono (streamEncrypt_spec initI.rawChunkAeadInst he.2 (hA _) (by simp [hfin])
    (by rw [hnext]; simp) buf he.1.to_slice hbuf (by simp) ops drains)
  intro o ho out acc hoeq
  obtain ⟨ct, hct, hout⟩ := ho out acc hoeq
  rw [hout, Aeneas.Std.Array.val_to_slice]
  simp [encryptMsg, hnh, hct]

/-- `DecryptRead`, once the header is accepted, agrees with one-shot decryption of
the header and the body it accepted. -/
theorem streamDecrypt_eq_decryptMsg (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (suite : Suite) (key context : Slice U8) (hdr : Std.Array U8 56#usize) (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize)
    (cipher : ChunkCipher A) (okm' : Std.Array U8 76#usize) (t' : Std.Array U8 64#usize)
    (hopen : open_header macI initI ctI suite key context hdr okm t = ok (.Ok cipher, okm', t'))
    (buf : Slice U8) (hbuf : buf.length = 16400) (ops : List DecOp) :
    streamDecryptBody initI cipher buf ops ⦃ x =>
      (x.1.dec.done = true → x.1.pos = x.1.end →
        decryptMsg macI initI ctI suite key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Ok x.2.2.1)) ∧
      (∀ e, x.1.dec.failed = some e →
        decryptMsg macI initI ctI suite key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Err e)) ⦄ := by
  simp only [streamDecryptBody, Decryptor.new, bind_ok]
  apply WP.spec_mono (streamDecrypt_spec initI.rawChunkAeadInst _ (hA _) rfl rfl (by simp) buf
    hbuf ops)
  rintro x ⟨hok, herr⟩
  have hdm : ∀ ct, decryptMsg macI initI ctI suite key context okm t (hdr.val ++ ct) =
      decryptFrom initI.rawChunkAeadInst ⟨cipher, 0#u64, false, none⟩ ct := by
    intro ct
    rw [decryptMsg, dite_eq_right (by simp)]
    simp [hopen, Decryptor.new, List.drop_left' (show hdr.val.length = 56 by simp)]
  exact ⟨fun hd hp => by rw [hdm]; exact hok hd hp, fun e he => by rw [hdm]; exact herr e he⟩

end cobblestone
