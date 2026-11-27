module
public import Cobblestone.Proofs.Header
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone

open header raw

variable {M A C : Type} (macI : Mac M) (initI : AeadInit A) (ctI : CtEq C)

-- encryptMsg and decryptMsg are hand-written mirrors of `encrypt` and `decrypt`
-- in src/lib.rs, which Aeneas doesn't extract: the header, then the body. The
-- salt and the scratch buffers are parameters, as in the extracted header code.
def encryptMsg (suite : Suite) (key : Slice U8) (salt : Std.Array U8 24#usize)
    (context : Slice U8) (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize)
    (m : List U8) : Result (core.result.Result (List U8) Error) := do
  let (he, _, _) ← new_header macI initI suite key salt context okm t
  let r ← encryptFrom initI.rawChunkAeadInst he.2 m
  match r with
  | .Ok body => ok (.Ok (he.1.val ++ body))
  | .Err e => ok (.Err e)

def decryptMsg (suite : Suite) (key context : Slice U8) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (ct : List U8) : Result (core.result.Result (List U8) Error) :=
  if h : ct.length < 56 then ok (.Err .Truncated)
  else do
    let (r, _, _) ← open_header macI initI ctI suite key context
      (Std.Array.from (ct.take 56) (by simp; omega)) okm t
    match r with
    | .Err e => ok (.Err e)
    | .Ok cipher =>
      let dec ← Decryptor.new initI.rawChunkAeadInst cipher
      decryptFrom initI.rawChunkAeadInst dec (ct.drop 56)

variable {hmac : List U8 → List U8 → Std.Array U8 64#usize} {st : M → List U8 × List U8}

theorem full_roundtrip (hM : MacLaws macI hmac st) (hI : AeadInitLaws initI) (hC : CtEqLaws ctI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hCo : ∀ a, AeadCorrect initI.rawChunkAeadInst a)
    (suite : Suite) (key context : Slice U8) (hk : key.length = suiteKeyLen suite)
    (salt : Std.Array U8 24#usize) (okm okm' : Std.Array U8 76#usize)
    (t t' : Std.Array U8 64#usize) (m : List U8) (hm : m.length / 16384 + 1 ≤ 2 ^ 38) :
    ∃ ct, encryptMsg macI initI suite key salt context okm t m = ok (.Ok ct) ∧
      decryptMsg macI initI ctI suite key context okm' t' ct = ok (.Ok m) := by
  obtain ⟨⟨he, okm1, t1⟩, hnh, cm, hD, hbytes, hnext, hfin⟩ :=
    spec_ok_eq (new_header_spec hM hI suite key salt context okm t hk)
  obtain ⟨⟨r, okm2, t2⟩, hoh, c, cm', hD', hr⟩ :=
    spec_ok_eq (open_header_spec hM hI hC suite key context he.1 okm' t' hk)
  have htake : he.1.val.take 24 = salt.val := by rw [hbytes]; exact List.take_left' (by simp)
  rw [htake] at hD'
  obtain ⟨hcc, hcm⟩ := Derived_unique hD' hD
  subst hcc hcm
  have hdrop : he.1.val.drop 24 = cm'.val := by rw [hbytes]; exact List.drop_left' (by simp)
  simp only [hdrop, ite_true] at hr
  subst hr
  obtain ⟨body, henc, hdec⟩ := roundtrip initI.rawChunkAeadInst m he.2
    ⟨he.2.cipher, 0#u64, false, none⟩ (hA _) (hCo _) rfl (by rw [hnext]) (by simp [hfin]) (by simp) rfl
    (by rw [hnext]; simp; omega)
  refine ⟨he.1.val ++ body, ?_, ?_⟩
  · simp [encryptMsg, hnh, henc]
  · rw [decryptMsg, dite_eq_right (by simp)]
    simp [hoh, Decryptor.new, hdec]

theorem full_integrity (hM : MacLaws macI hmac st) (hI : AeadInitLaws initI) (hC : CtEqLaws ctI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a)
    (hT : ∀ a, AeadTagCheck initI.rawChunkAeadInst a)
    (suite : Suite) (key context : Slice U8) (hk : key.length = suiteKeyLen suite)
    (okm okm' : Std.Array U8 76#usize) (t t' : Std.Array U8 64#usize) (ct m : List U8)
    (hdec : decryptMsg macI initI ctI suite key context okm' t' ct = ok (.Ok m)) :
    ∃ salt : Std.Array U8 24#usize, salt.val = ct.take 24 ∧
      encryptMsg macI initI suite key salt context okm t m = ok (.Ok ct) := by
  by_cases hshort : ct.length < 56
  · rw [decryptMsg, dite_eq_left hshort] at hdec; simp at hdec
  have h56 : (ct.take 56).length = 56 := by simp; omega
  rw [decryptMsg, dite_eq_right hshort] at hdec
  obtain ⟨⟨r, okm2, t2⟩, hoh, c, cm, hD, hr⟩ := spec_ok_eq
    (open_header_spec hM hI hC suite key context (Std.Array.from (ct.take 56) (by simp; omega))
      okm' t' hk)
  rw [hoh] at hdec
  simp only [Std.Array.from_val, List.take_take, show min 24 56 = 24 from rfl,
    List.drop_take] at hD hr
  by_cases hcm : List.take (56 - 24) (List.drop 24 ct) = cm.val
  · simp only [hcm, ite_true] at hr
    subst hr
    simp [Decryptor.new] at hdec
    let salt : Std.Array U8 24#usize := Std.Array.from (ct.take 24) (by simp; omega)
    obtain ⟨⟨he, okm1, t1⟩, hnh, cm2, hD2, hbytes, hnext, hfin⟩ :=
      spec_ok_eq (new_header_spec hM hI suite key salt context okm t hk)
    have hsalt : salt.val = ct.take 24 := Std.Array.from_val _ _
    rw [hsalt] at hD2
    obtain ⟨hcc, hcm2⟩ := Derived_unique hD2 hD
    subst hcc hcm2
    have hbody := integrity initI.rawChunkAeadInst (ct.drop 56) he.2
      ⟨he.2.cipher, 0#u64, false, none⟩ (hA _) (hT _) rfl (by rw [hnext]) (by simp [hfin])
      (by simp) rfl (by rw [hnext]; simp) m hdec
    refine ⟨salt, hsalt, ?_⟩
    have hct : he.1.val ++ ct.drop 56 = ct := by
      rw [hbytes, hsalt, ← hcm, List.append_assoc,
        show List.drop 56 ct = List.drop (56 - 24) (List.drop 24 ct) by simp [List.drop_drop],
        List.take_append_drop, List.take_append_drop]
    simp [encryptMsg, hnh, hbody, hct]
  · simp only [hcm, ite_false] at hr
    subst hr
    simp at hdec

end cobblestone
