module
public import Cobblestone.Spec
public import Cobblestone.Proofs.Full
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone.conformance

open spec header raw

theorem keyLen_eq (i : Instantiation) : keyLen i = suiteKeyLen (toSuite i) := by
  cases i <;> rfl

theorem label_eq (i : Instantiation) :
    ascii "c2sp.org/chunked-encryption@v1+" ++ ascii (aeadName i) ++ [⟨0#8⟩] =
      suiteLabel (toSuite i) := by
  cases i
  · rw [toSuite, suiteLabel_aes128]; decide
  · rw [toSuite, suiteLabel_aes256]; decide

theorem info_eq (i : Instantiation) (salt context : Bytes) :
    info i salt context = suiteLabel (toSuite i) ++ salt ++ context := by
  rw [info, label_eq]

/-! ## HKDF -/

theorem hkdfT_eq (P : Primitives) (prk info : Bytes) (i : Nat) :
    spec.hkdfT P prk info i = header.hkdfT P.hmac prk info i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [spec.hkdfT, header.hkdfT, ih]

theorem flatMap_hkdfT (P : Primitives) (prk info : Bytes) (n : Nat) :
    (List.range n).flatMap (fun i => spec.hkdfT P prk info (i + 1)) =
      header.hkdfBlocks P.hmac prk info n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, hkdfBlocks]
    simp [hkdfT_eq]

theorem hkdfExpand_eq (P : Primitives) (prk info : Bytes) (L : Nat) (hL : L ≤ 255 * 64) :
    spec.hkdfExpand P prk info L = header.hkdfExpand P.hmac prk info L := by
  rw [spec.hkdfExpand, flatMap_hkdfT, hkdfBlocks_take _ _ _ _ (by omega) (by omega)]

theorem spec_of_eq {α : Type} {m : Result α} {v : α} {p : α → Prop} (h : m = ok v)
    (hs : m ⦃ p ⦄) : p v := by
  rw [h] at hs; simpa using hs

/-! ## Nonces -/

theorem list_ext_getElem! {l1 l2 : List U8} (h : l1.length = l2.length)
    (h2 : ∀ k < l1.length, l1[k]! = l2[k]!) : l1 = l2 := by
  apply List.ext_getElem h
  intro k hk1 hk2
  have := h2 k hk1
  rwa [getElem!_pos l1 k hk1, getElem!_pos l2 k hk2] at this

theorem toBEBytes_getElem! (x : U64) (j : Nat) (hj : j < 8) :
    x.bv.toBEBytes[j]! = BitVec.ofNat 8 (x.val / 256 ^ (7 - j)) := by
  have hx : x.val = x.bv.toNat := rfl
  rw [hx]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | (simp [BitVec.toBEBytes, BitVec.toLEBytes]; done)
    | (simp [BitVec.toBEBytes, BitVec.toLEBytes]; bv_omega)

theorem nonce_eq_chunkNonce {A : Type} (inst : ChunkAead A) (cipher : ChunkCipher A) (i : U64)
    (hi : i.val < 2 ^ 38) (n : Std.Array U8 12#usize)
    (hn : ChunkCipher.nonce inst cipher i = ok n) :
    n.val = chunkNonce cipher.base_nonce.val i.val := by
  have hs := spec_of_eq hn (ChunkCipher.nonce_spec inst cipher i hi)
  apply list_ext_getElem! (by simp [chunkNonce, bigEndian, nonceLen])
  intro k hk
  have hk12 : k < 12 := by simpa using hk
  have hb : cipher.base_nonce.val.length = 12 := by simp
  rw [hs k hk12]
  simp only [chunkNonce, bigEndian, nonceLen]
  rw [getElem!_pos (List.zipWith _ _ _) k (by simp; omega)]
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rw [getElem!_pos cipher.base_nonce.val k (by omega)]
  by_cases h7 : 7 ≤ k
  · simp only [h7, ite_true]
    rw [counterBytes_getElem! i (k - 4) (by omega), toBEBytes_getElem! i (k - 4) (by omega),
      show 7 - (k - 4) = 12 - 1 - k by omega]
  · simp only [h7, ite_false]
    have h0 : i.val / 256 ^ (12 - 1 - k) = 0 := by
      apply Nat.div_eq_of_lt
      calc i.val < 2 ^ 38 := hi
        _ < 256 ^ 5 := by norm_num
        _ ≤ 256 ^ (12 - 1 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h0, UScalar.eq_equiv_bv_eq]
    simp

/-! ## The body -/

def bodyFrom (P : Primitives) (ins : Instantiation) (key base : Bytes) (start : Nat) (m : Bytes) :
    Bytes :=
  (List.range (numChunks m)).flatMap fun j =>
    P.aeadSeal ins key (chunkNonce base (start + j)) (chunk m j)

theorem bodyFrom_long (P : Primitives) (ins : Instantiation) (key base : Bytes) (start : Nat)
    (m : Bytes) (h : 16384 ≤ m.length) :
    bodyFrom P ins key base start m =
      P.aeadSeal ins key (chunkNonce base start) (m.take 16384) ++
        bodyFrom P ins key base (start + 1) (m.drop 16384) := by
  have hn : numChunks m = numChunks (m.drop 16384) + 1 := by
    simp only [numChunks, chunkSize, List.length_drop]; omega
  have h1 : chunk m 0 = m.take 16384 := by simp [chunk, chunkSize]
  have h2 : ∀ j, chunk m (j + 1) = chunk (m.drop 16384) j := by
    intro j; simp only [chunk, chunkSize, List.drop_drop]; congr 2; ring
  have h3 : ∀ j, start + (j + 1) = start + 1 + j := fun j => by omega
  rw [bodyFrom, hn, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, bodyFrom, h1,
    Nat.add_zero]
  congr 1
  congr 1
  funext j
  simp only [Nat.succ_eq_add_one]
  rw [h2, h3]

theorem bodyFrom_short (P : Primitives) (ins : Instantiation) (key base : Bytes) (start : Nat)
    (m : Bytes) (h : m.length < 16384) :
    bodyFrom P ins key base start m = P.aeadSeal ins key (chunkNonce base start) m := by
  have hn : numChunks m = 1 := by simp only [numChunks, chunkSize]; omega
  simp [bodyFrom, hn, chunk, chunkSize, List.take_of_length_le (le_of_lt h)]

theorem encryptFrom_spec {A : Type} {P : Primitives} {initI : AeadInit A}
    (hS : SealImplements P initI) (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (ins : Instantiation) (k : Slice U8) (a : A) (hk : initI.new (toSuite ins) k = ok a)
    (m : List U8) (enc : Encryptor A) (hcip : enc.cipher.aead = a) (hf : ¬ enc.finished)
    (hb : enc.next.val + m.length / 16384 + 1 ≤ 2 ^ 38) :
    encryptFrom initI.rawChunkAeadInst enc m =
      ok (.Ok (bodyFrom P ins k.val enc.cipher.base_nonce.val enc.next.val m)) := by
  have hn38 : enc.next.val < 2 ^ 38 := by omega
  have hA' := hA enc.cipher.aead
  by_cases hshort : m.length < 16384
  · obtain ⟨⟨r, enc', c⟩, hseal, -, -, hr⟩ := spec_ok_eq
      (Encryptor.seal_spec initI.rawChunkAeadInst enc hA' (Slice.from m (by scalar_tac)) true hf
        hn38 (by simpa using hshort))
    cases r with
    | Err e => simp at hr
    | Ok tag =>
      obtain ⟨⟨n, hn, hs⟩, -, -, -⟩ := hr
      have hct := hS.sealed ins k a hk n _ tag c (hcip ▸ hs)
      rw [nonce_eq_chunkNonce _ _ _ hn38 n hn, Slice.from_val] at hct
      rw [encryptFrom]
      simp [hshort, hseal, hct, bodyFrom_short _ _ _ _ _ _ hshort]
  · have hm16 : 16384 ≤ m.length := by omega
    obtain ⟨⟨r, enc', c⟩, hseal, hec, -, hr⟩ := spec_ok_eq
      (Encryptor.seal_spec initI.rawChunkAeadInst enc hA'
        (Slice.from (m.take 16384) (by scalar_tac)) false hf hn38 (by simp; omega))
    cases r with
    | Err e => simp at hr; omega
    | Ok tag =>
      obtain ⟨⟨n, hn, hs⟩, hen, hef, -⟩ := hr
      have hct := hS.sealed ins k a hk n _ tag c (hcip ▸ hs)
      rw [nonce_eq_chunkNonce _ _ _ hn38 n hn, Slice.from_val] at hct
      have hrec := encryptFrom_spec hS hA ins k a hk (m.drop 16384) enc'
        (by rw [hec, hcip]) (by simp [hef]) (by rw [hen]; simp; omega)
      rw [hec, hen] at hrec
      rw [encryptFrom, bodyFrom_long _ _ _ _ _ _ hm16, ← hct]
      simp [hshort, hseal, hrec]
termination_by m.length
decreasing_by simp; omega

/-! ## Whole messages -/

variable {M A C : Type} {macI : Mac M} {initI : AeadInit A} {ctI : CtEq C} {P : Primitives}
  {st : M → List U8 × List U8}

theorem derived_eq (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt context : Bytes) :
    derived P ins key.val salt context =
      header.hkdfExpand P.hmac key.val (suiteLabel (toSuite ins) ++ salt ++ context)
        (key.val.length + 44) := by
  have hL : keyLen ins + nonceLen + commitmentLen ≤ 255 * 64 := by
    cases ins <;> simp [keyLen, nonceLen, commitmentLen]
  rw [derived, hkdfExpand_eq _ _ _ _ hL, info_eq]
  congr 1; simp only [Slice.length] at hk; simp [hk, nonceLen, commitmentLen]

/-- Key derivation computes the specification: `derive` returns the AEAD created
from `spec.aeadKey`, `spec.baseNonce` as the base nonce, and `spec.commitment`. -/
theorem derive_eq_spec (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) :
    derive macI initI (toSuite ins) key salt context okm t ⦃ cc _ _ =>
      (∃ k : Slice U8, k.val = aeadKey P ins key.val salt.val context.val ∧
        initI.new (toSuite ins) k = ok cc.1.aead) ∧
      cc.1.base_nonce.val = baseNonce P ins key.val salt.val context.val ∧
      cc.2.val = commitment P ins key.val salt.val context.val ⦄ := by
  have hk' : key.length = suiteKeyLen (toSuite ins) := by rw [hk, keyLen_eq]
  have hkl : keyLen ins = key.val.length := by simp only [Slice.length] at hk; omega
  apply WP.spec_mono (derive_spec hM hI (toSuite ins) key salt context okm t hk')
  rintro ⟨⟨c, cm⟩, okm1, t1⟩ ⟨⟨kS, hkS, hnew⟩, hbase, hcm⟩
  refine ⟨⟨kS, ?_, hnew⟩, ?_, ?_⟩
  · rw [hkS, aeadKey, derived_eq ins key hk, hkl]
  · rw [hbase, baseNonce, derived_eq ins key hk, hkl]; rfl
  · rw [hcm, commitment, derived_eq ins key hk, hkl]; rfl

/-- Encryption computes the specification. -/
theorem encryptMsg_eq_spec (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hS : SealImplements P initI) (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (m : Bytes) (hm : numChunks m ≤ maxChunks) :
    ∃ ct, spec.encrypt P ins key.val salt.val context.val m = some ct ∧
      encryptMsg macI initI (toSuite ins) key salt context okm t m = ok (.Ok ct) := by
  have hk' : key.length = suiteKeyLen (toSuite ins) := by rw [hk, keyLen_eq]
  obtain ⟨⟨he, okm1, t1⟩, hnh, cm, hD, hbytes, hnext, hfin⟩ :=
    spec_ok_eq (new_header_spec hM hI (toSuite ins) key salt context okm t hk')
  obtain ⟨⟨kS, hkS, hnew⟩, hbase, hcm⟩ := hD
  have hbody := encryptFrom_spec hS hA ins kS he.2.cipher.aead hnew m he.2 rfl (by simp [hfin])
    (by rw [hnext]; simp only [numChunks, chunkSize, maxChunks] at hm; simp; omega)
  rw [hnext] at hbody
  refine ⟨he.1.val ++ bodyFrom P ins kS.val he.2.cipher.base_nonce.val 0 m, ?_, ?_⟩
  · have hL : keyLen ins + nonceLen + commitmentLen ≤ 255 * 64 := by
      cases ins <;> simp [keyLen, nonceLen, commitmentLen]
    have hder : derived P ins key.val salt.val context.val =
        header.hkdfExpand P.hmac key.val (suiteLabel (toSuite ins) ++ salt.val ++ context.val)
          (key.val.length + 44) := by
      rw [derived, hkdfExpand_eq _ _ _ _ hL, info_eq]
      congr 1; simp only [Slice.length] at hk; simp [hk, nonceLen, commitmentLen]
    have hkl : keyLen ins = key.val.length := by simp only [Slice.length] at hk; omega
    have hsl : salt.val.length = saltLen := by simp [saltLen]
    have hkl2 : key.val.length = keyLen ins := hk
    rw [spec.encrypt, ite_eq_right (by
      intro hc
      rcases hc with h1 | h2 | h3
      · exact h1 hkl2
      · exact h2 hsl
      · omega)]
    simp only [Option.some.injEq]
    rw [hbytes, hcm, bodyFrom, aeadKey, baseNonce, commitment, hder, hkl, ← hkS,
      show nonceLen = 12 from rfl, ← hbase]
    simp
  · simp [encryptMsg, hnh, hbody]

theorem encryptFrom_ok_bound (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a) (m : Bytes)
    (enc : Encryptor A) (hf : ¬ enc.finished) (hn38 : enc.next.val < 2 ^ 38) (ct : Bytes)
    (h : encryptFrom initI.rawChunkAeadInst enc m = ok (.Ok ct)) :
    enc.next.val + m.length / 16384 + 1 ≤ 2 ^ 38 := by
  by_cases hshort : m.length < 16384
  · omega
  · obtain ⟨⟨r, enc', c⟩, hseal, -, -, hr⟩ := spec_ok_eq
      (Encryptor.seal_spec initI.rawChunkAeadInst enc (hA _)
        (Slice.from (m.take 16384) (by scalar_tac)) false hf hn38 (by simp; omega))
    rw [encryptFrom] at h
    simp only [hshort, _root_.dite_false, hseal, bind_ok] at h
    cases r with
    | Err e => simp at h
    | Ok tag =>
      obtain ⟨-, hen, hef, hlt⟩ := hr
      generalize hR : encryptFrom initI.rawChunkAeadInst enc' (m.drop 16384) = R at h
      obtain ⟨ct', hct'⟩ : ∃ ct', R = ok (.Ok ct') := by
        cases R <;> simp_all
        rename_i v; cases v <;> simp_all
      subst hct'
      have := encryptFrom_ok_bound hA (m.drop 16384) enc' (by simp [hef]) (hlt (by simp)) ct' hR
      rw [hen] at this; simp at this; omega
termination_by m.length
decreasing_by simp; omega

theorem encryptMsg_ok_spec (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hS : SealImplements P initI) (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (m ct : Bytes)
    (h : encryptMsg macI initI (toSuite ins) key salt context okm t m = ok (.Ok ct)) :
    spec.encrypt P ins key.val salt.val context.val m = some ct := by
  have hk' : key.length = suiteKeyLen (toSuite ins) := by rw [hk, keyLen_eq]
  obtain ⟨⟨he, okm1, t1⟩, hnh, -, -, -, hnext, hfin⟩ :=
    spec_ok_eq (new_header_spec hM hI (toSuite ins) key salt context okm t hk')
  have hbound : numChunks m ≤ maxChunks := by
    have h' := h
    simp only [encryptMsg, hnh, bind_ok] at h'
    generalize hR : encryptFrom initI.rawChunkAeadInst he.2 m = R at h'
    obtain ⟨body, hb⟩ : ∃ body, R = ok (.Ok body) := by
      cases R <;> simp_all
      rename_i v; cases v <;> simp_all
    subst hb
    have := encryptFrom_ok_bound hA m he.2 (by simp [hfin]) (by rw [hnext]; simp) body hR
    rw [hnext] at this; simp only [numChunks, chunkSize, maxChunks]; simp at this; omega
  obtain ⟨ct', hspec, henc⟩ :=
    encryptMsg_eq_spec hM hI hS hA ins key hk salt context okm t m hbound
  rw [h, ok_eq_ok_iff, core.result.Result.Ok.injEq] at henc
  rw [hspec, henc]

/-- Decryption only accepts the specification's ciphertext of the message it
returns, encrypted with the salt in the ciphertext's header. -/
theorem decryptMsg_sound (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hC : CtEqLaws ctI) (hS : SealImplements P initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hT : ∀ a, AeadTagCheck initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins) (context : Slice U8)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (ct m : Bytes)
    (h : decryptMsg macI initI ctI (toSuite ins) key context okm t ct = ok (.Ok m)) :
    spec.encrypt P ins key.val (ct.take 24) context.val m = some ct := by
  have hk' : key.length = suiteKeyLen (toSuite ins) := by rw [hk, keyLen_eq]
  obtain ⟨salt, hsalt, henc⟩ :=
    full_integrity macI initI ctI hM hI hC hA hT (toSuite ins) key context hk' okm okm t t ct m h
  rw [← hsalt]
  exact encryptMsg_ok_spec hM hI hS hA ins key hk salt context okm t m ct henc

/-- Every ciphertext of the specification decrypts to its message. -/
theorem decryptMsg_complete (hM : MacLaws macI P.hmac st) (hI : AeadInitLaws initI)
    (hC : CtEqLaws ctI) (hS : SealImplements P initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hCo : ∀ a, AeadCorrect initI.rawChunkAeadInst a)
    (ins : Instantiation) (key : Slice U8) (hk : key.length = keyLen ins)
    (salt : Std.Array U8 24#usize) (context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (m ct : Bytes)
    (h : spec.encrypt P ins key.val salt.val context.val m = some ct) :
    decryptMsg macI initI ctI (toSuite ins) key context okm t ct = ok (.Ok m) := by
  have hk' : key.length = suiteKeyLen (toSuite ins) := by rw [hk, keyLen_eq]
  have hbound : numChunks m ≤ maxChunks := by
    by_contra hc
    rw [spec.encrypt, ite_eq_left (Or.inr (Or.inr (by omega)))] at h
    cases h
  obtain ⟨ct', hspec, henc⟩ :=
    encryptMsg_eq_spec hM hI hS hA ins key hk salt context okm t m hbound
  rw [h, Option.some.injEq] at hspec
  subst hspec
  obtain ⟨ct'', henc', hdec⟩ := full_roundtrip macI initI ctI hM hI hC hA hCo (toSuite ins) key
    context hk' salt okm okm t t m (by simp only [numChunks, chunkSize, maxChunks] at hbound; omega)
  rw [henc, ok_eq_ok_iff, core.result.Result.Ok.injEq] at henc'
  rw [henc']; exact hdec

end cobblestone.conformance
