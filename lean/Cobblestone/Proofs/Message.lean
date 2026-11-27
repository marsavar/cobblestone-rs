module
public import Cobblestone.Proofs.Chunks
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone.raw

@[simp] theorem ok_eq_ok_iff {α : Type} {a b : α} : (ok a : Result α) = ok b ↔ a = b :=
  ⟨fun h => Result.ok_injective h, congrArg _⟩

variable {A : Type} (inst : ChunkAead A)

-- encryptFrom and decryptFrom are hand-written mirrors of the loops in `encrypt`
-- and `decrypt` in src/lib.rs, which Aeneas doesn't extract. Keep them in step.
def encryptFrom (enc : Encryptor A) (m : List U8) :
    Result (core.result.Result (List U8) Error) :=
  if h : m.length < 16384 then do
    let (r, _, c) ← Encryptor.seal inst enc (Slice.from m (by scalar_tac)) true
    match r with
    | .Ok tag => ok (.Ok (c.val ++ tag.val))
    | .Err e => ok (.Err e)
  else do
    let (r, enc', c) ← Encryptor.seal inst enc (Slice.from (m.take 16384) (by scalar_tac)) false
    match r with
    | .Ok tag =>
      let rest ← encryptFrom enc' (m.drop 16384)
      match rest with
      | .Ok ct => ok (.Ok (c.val ++ tag.val ++ ct))
      | .Err e => ok (.Err e)
    | .Err e => ok (.Err e)
termination_by m.length

def decryptFrom (dec : Decryptor A) (body : List U8) :
    Result (core.result.Result (List U8) Error) := do
  let n := min body.length 16400
  let (r, dec', c) ← Decryptor.open inst dec (Slice.from (body.take n) (by scalar_tac))
  match r with
  | .Err e => ok (.Err e)
  | .Ok len =>
    let pt := c.val.take len.val
    if dec'.done then ok (.Ok pt)
    -- Unreachable: a chunk shorter than 16400 bytes is always final. Rust loops
    -- once more here instead, which Lean can't see terminates.
    else if body.length < 16400 then fail .panic
    else
      let rest ← decryptFrom dec' (body.drop 16400)
      match rest with
      | .Ok m => ok (.Ok (pt ++ m))
      | .Err e => ok (.Err e)
termination_by body.length

-- The two AEAD properties the message theorems assume, on top of AeadTotal.
-- Both hold for AES-GCM as plain functional facts, without any cryptographic
-- assumption: decryption inverts encryption, and a tag is accepted only if it
-- equals the one encryption computes, so re-sealing an accepted plaintext
-- reproduces the same ciphertext and tag.
structure AeadCorrect (aead : A) : Prop where
  open_seal : ∀ n b t c, inst.seal aead n b = ok (t, c) → inst.open aead n c t = ok (true, b)

structure AeadTagCheck (aead : A) : Prop where
  seal_open : ∀ n c t b, inst.open aead n c t = ok (true, b) → inst.seal aead n b = ok (t, c)

theorem opened_sealed (cipher : ChunkCipher A) (hC : AeadCorrect inst cipher.aead)
    (index : U64) (n : Std.Array U8 12#usize) (b c : Slice U8) (tag : Std.Array U8 16#usize)
    (hn : ChunkCipher.nonce inst cipher index = ok n)
    (hs : inst.seal cipher.aead n b = ok (tag, c)) (hl : c.length = b.length)
    (chunk : Slice U8) (hchunk : chunk.val = c.val ++ tag.val)
    (v : Bool) (c' : Slice U8) (ho : OpenedAt inst cipher index chunk v c') :
    v = true ∧ c'.val = b.val ++ tag.val := by
  obtain ⟨n', d, t, p, hn', hd, ht, ho', hc'⟩ := ho
  rw [hn, ok_eq_ok_iff] at hn'
  subst hn'
  have hlen : chunk.length - 16 = c.length := by
    simp only [Slice.length, hchunk, List.length_append]
    simp
  have hd' : d = c := by
    rw [Slice.eq_iff, hd, hlen, hchunk]; simp
  have ht' : t = tag := by
    apply Std.Array.ext; rw [ht, hlen, hchunk]; simp
  subst hd' ht'
  rw [hC.open_seal _ _ _ _ hs] at ho'
  simp only [ok_eq_ok_iff, Prod.mk.injEq] at ho'
  obtain ⟨rfl, rfl⟩ := ho'
  exact ⟨rfl, hc'⟩

theorem roundtrip (m : List U8) (enc : Encryptor A) (dec : Decryptor A)
    (hA : AeadTotal inst enc.cipher.aead) (hC : AeadCorrect inst enc.cipher.aead)
    (hc : dec.cipher = enc.cipher) (hnext : dec.next = enc.next)
    (hf : ¬ enc.finished) (hd : ¬ dec.done) (hfail : dec.failed = none)
    (hb : enc.next.val + m.length / 16384 + 1 ≤ 2 ^ 38) :
    ∃ ct, encryptFrom inst enc m = ok (.Ok ct) ∧ decryptFrom inst dec ct = ok (.Ok m) := by
  have hn38 : enc.next.val < 2 ^ 38 := by omega
  by_cases hshort : m.length < 16384
  · obtain ⟨⟨r, enc', c⟩, hseal, -, hcl, hr⟩ := spec_ok_eq
      (Encryptor.seal_spec inst enc hA (Slice.from m (by scalar_tac)) true hf hn38
        (by simpa using hshort))
    cases r with
    | Err e => simp at hr
    | Ok tag =>
      obtain ⟨⟨n, hn, hs⟩, -, -, -⟩ := hr
      refine ⟨c.val ++ tag.val, ?_, ?_⟩
      · rw [encryptFrom]; simp [hshort, hseal]
      · have hcl' : c.val.length = m.length := by simpa [Slice.length] using hcl
        have hctl : (c.val ++ tag.val).length = m.length + 16 := by simp [hcl']
        have hmin : min (c.val ++ tag.val).length 16400 = (c.val ++ tag.val).length := by
          omega
        obtain ⟨⟨r2, dec', c2⟩, hopen, -, hc2l, hpost⟩ := spec_ok_eq
          (Decryptor.open_spec inst dec (hc ▸ hA)
            (Slice.from (List.take (min (c.val ++ tag.val).length 16400) (c.val ++ tag.val))
              (by scalar_tac))
            (hnext ▸ hn38) (by simp only [Slice.length, Slice.from_val, List.length_take]; omega)
            (fun _ => hd))
        simp only [hfail] at hpost
        rw [decryptFrom]
        simp only [hopen, bind_ok]
        have hchunk : (Slice.from (List.take (min (c.val ++ tag.val).length 16400)
            (c.val ++ tag.val)) (by scalar_tac)).val = c.val ++ tag.val := by
          rw [Slice.from_val, hmin, List.take_length]
        have hl16 : (c.val ++ tag.val).length < 16400 := by omega
        have hclen : c.length = (Slice.from m (by scalar_tac)).length := by
          simp [Slice.length, hcl']
        cases r2 with
        | Ok len =>
          obtain ⟨⟨-, hlen, -, hop, -, hdone⟩, -⟩ := hpost
          obtain ⟨-, hc2⟩ := opened_sealed inst enc.cipher hC enc.next n _ c tag hn hs hclen _
            hchunk true c2 (by rw [hc, hnext] at hop; exact hop)
          simp only [Slice.length, hchunk] at hlen hdone
          have hdone' : dec'.done = true := by rw [hdone]; exact decide_eq_true hl16
          simp [hdone', hc2, hlen, hcl']
        | Err e =>
          obtain ⟨⟨-, -, -, -, hdf⟩, -⟩ := hpost
          simp only [Slice.length, hchunk] at hdf
          obtain ⟨-, hop⟩ := hdf (by omega) (Or.inl hl16)
          obtain ⟨hv, -⟩ := opened_sealed inst enc.cipher hC enc.next n _ c tag hn hs hclen _
            hchunk false c2 (by rw [hc, hnext] at hop; exact hop)
          exact absurd hv (by simp)
  · have hm16 : 16384 ≤ m.length := by omega
    have hnext2 : enc.next.val < 2 ^ 38 - 1 := by omega
    obtain ⟨⟨r, enc', c⟩, hseal, hec, hcl, hr⟩ := spec_ok_eq
      (Encryptor.seal_spec inst enc hA (Slice.from (m.take 16384) (by scalar_tac)) false hf hn38
        (by simp; omega))
    cases r with
    | Err e => simp at hr; omega
    | Ok tag =>
      obtain ⟨⟨n, hn, hs⟩, hen, hef, -⟩ := hr
      have hcl' : c.val.length = 16384 := by simpa [Slice.length, hm16] using hcl
      have hctl : (c.val ++ tag.val).length = 16400 := by simp [hcl']
      obtain ⟨⟨r2, dec', c2⟩, hopen, hdc', hc2l, hpost⟩ := spec_ok_eq
        (Decryptor.open_spec inst dec (hc ▸ hA) (Slice.from (c.val ++ tag.val) (by scalar_tac))
          (hnext ▸ hn38) (by simp [Slice.length, hctl]) (fun _ => hd))
      simp only [hfail] at hpost
      have hchunk : (Slice.from (c.val ++ tag.val) (by scalar_tac)).val = c.val ++ tag.val :=
        Slice.from_val _ _
      have hclen : c.length = (Slice.from (m.take 16384) (by scalar_tac)).length := by
        simp [Slice.length, hcl', hm16]
      cases r2 with
      | Err e =>
        exfalso
        obtain ⟨⟨-, -, -, hmt, hdf⟩, -⟩ := hpost
        simp only [Slice.length, hchunk, hctl] at hmt hdf
        obtain ⟨-, hop⟩ := hdf (by omega) (Or.inr (by rw [hnext]; omega))
        obtain ⟨hv, -⟩ := opened_sealed inst enc.cipher hC enc.next n _ c tag hn hs hclen _
          hchunk false c2 (by rw [hc, hnext] at hop; exact hop)
        exact absurd hv (by simp)
      | Ok len =>
        obtain ⟨⟨-, hlen, -, hop, hdn, hdone⟩, hdf'⟩ := hpost
        obtain ⟨-, hc2⟩ := opened_sealed inst enc.cipher hC enc.next n _ c tag hn hs hclen _
          hchunk true c2 (by rw [hc, hnext] at hop; exact hop)
        simp only [Slice.length, hchunk, hctl] at hlen hdone
        have hdone' : dec'.done = false := by rw [hdone]; decide
        obtain ⟨ct', henc', hdec'⟩ := roundtrip (m.drop 16384) enc' dec' (hec ▸ hA) (hec ▸ hC)
          (by rw [hdc', hc, hec]) (by apply UScalar.eq_of_val_eq; rw [hdn, hen, hnext])
          (by simp [hef]) (by simp [hdone']) hdf' (by rw [hen]; simp; omega)
        refine ⟨c.val ++ tag.val ++ ct', ?_, ?_⟩
        · rw [encryptFrom]; simp [hshort, hseal, henc']
        · have hS : Slice.from (List.take (min (c.val ++ tag.val ++ ct').length 16400)
              (c.val ++ tag.val ++ ct')) (by scalar_tac) =
              Slice.from (c.val ++ tag.val) (by scalar_tac) := by
            have hmin : min (c.val ++ tag.val ++ ct').length 16400 = (c.val ++ tag.val).length := by
              simp only [List.length_append] at hctl ⊢; omega
            rw [Slice.eq_iff, Slice.from_val, Slice.from_val, hmin]
            exact List.take_left' rfl
          rw [decryptFrom]
          simp only [hS, hopen, bind_ok]
          have hdrop : List.drop 16400 (c.val ++ (tag.val ++ ct')) = ct' := by
            rw [← List.append_assoc]; exact List.drop_left' hctl
          have htm : (List.take 16384 m).length = 16384 := by simp; omega
          have hpt : List.take 16384 (List.take 16384 m ++ tag.val) = List.take 16384 m :=
            List.take_left' htm
          simp [hdone', hdrop, hdec', hc2, hlen, hcl', hpt,
            show ¬ (16384 + (16 + ct'.length) < 16400) by omega]
termination_by m.length
decreasing_by simp; omega

theorem opened_reseal (cipher : ChunkCipher A) (hA : AeadTotal inst cipher.aead)
    (hT : AeadTagCheck inst cipher.aead) (index : U64) (chunk c2 : Slice U8)
    (ho : OpenedAt inst cipher index chunk true c2) :
    ∃ (n : Std.Array U8 12#usize) (p d : Slice U8) (t : Std.Array U8 16#usize),
      ChunkCipher.nonce inst cipher index = ok n ∧ inst.seal cipher.aead n p = ok (t, d) ∧
      d.val ++ t.val = chunk.val ∧ c2.val = p.val ++ t.val ∧ p.length = chunk.length - 16 := by
  obtain ⟨n, d, t, p, hn, hd, ht, hop, hc2⟩ := ho
  obtain ⟨⟨v', p'⟩, hop', -, hpl⟩ := spec_ok_eq (hA.open_ok n d t)
  rw [hop, ok_eq_ok_iff, Prod.mk.injEq] at hop'
  obtain ⟨-, rfl⟩ := hop'
  refine ⟨n, p, d, t, hn, hT.seal_open _ _ _ _ hop, ?_, hc2, ?_⟩
  · rw [hd, ht]; exact List.take_append_drop _ _
  · simp only [Slice.length] at hpl ⊢; rw [hpl, hd]; simp

theorem integrity (body : List U8) (enc : Encryptor A) (dec : Decryptor A)
    (hA : AeadTotal inst enc.cipher.aead) (hT : AeadTagCheck inst enc.cipher.aead)
    (hc : dec.cipher = enc.cipher) (hnext : dec.next = enc.next)
    (hf : ¬ enc.finished) (hd : ¬ dec.done) (hfail : dec.failed = none)
    (hn38 : enc.next.val < 2 ^ 38) (m : List U8)
    (hdec : decryptFrom inst dec body = ok (.Ok m)) :
    encryptFrom inst enc m = ok (.Ok body) := by
  have hcl : (Slice.from (body.take (min body.length 16400)) (by scalar_tac)).length =
      min body.length 16400 := by
    simp [Slice.length]
  obtain ⟨⟨r2, dec', c2⟩, hopen, hdc', hc2l, hpost⟩ := spec_ok_eq
    (Decryptor.open_spec inst dec (hc ▸ hA)
      (Slice.from (body.take (min body.length 16400)) (by scalar_tac))
      (hnext ▸ hn38) (by rw [hcl]; omega) (fun _ => hd))
  simp only [hfail] at hpost
  rw [decryptFrom] at hdec
  simp only [hopen, bind_ok] at hdec
  cases r2 with
  | Err e => simp at hdec
  | Ok len =>
    obtain ⟨⟨h16, hlen, hmax, hop, hdn, hdone⟩, hdf'⟩ := hpost
    rw [hcl] at h16 hlen hmax hdone
    obtain ⟨n, p, d, t, hn, hs, hdt, hc2, hpl⟩ :=
      opened_reseal inst enc.cipher hA hT enc.next _ c2 (by rw [hc, hnext] at hop; exact hop)
    rw [hcl] at hpl
    have hpt : c2.val.take len.val = p.val := by
      rw [hc2, hlen]; exact List.take_left' (by simpa [Slice.length] using hpl)
    simp only [Slice.from_val] at hdt
    by_cases hlast : body.length < 16400
    · have hmin : min body.length 16400 = body.length := by omega
      rw [hmin] at hdt hpl hdone
      have hdone' : dec'.done = true := by rw [hdone]; exact decide_eq_true hlast
      simp [hdone', hpt] at hdec
      subst hdec
      have hpS : Slice.from p.val (by scalar_tac) = p := by rw [Slice.eq_iff, Slice.from_val]
      have hml : p.val.length < 16384 := by simp [Slice.length] at hpl; omega
      obtain ⟨⟨r, enc', c'⟩, hseal, -, -, hr⟩ := spec_ok_eq
        (Encryptor.seal_spec inst enc hA (Slice.from p.val (by scalar_tac)) true hf hn38
          (by simpa using hml))
      cases r with
      | Err e => simp at hr
      | Ok tag' =>
        obtain ⟨⟨n', hn', hs'⟩, -, -, -⟩ := hr
        rw [hn, ok_eq_ok_iff] at hn'
        subst hn'
        rw [hpS, hs, ok_eq_ok_iff, Prod.mk.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        rw [hpS] at hseal
        rw [encryptFrom]
        simp [hml, hseal, hdt]
    · have hmin : min body.length 16400 = 16400 := by omega
      rw [hmin] at hdt hpl hdone hmax
      have hdone' : dec'.done = false := by rw [hdone]; decide
      have hnx : enc.next.val < 2 ^ 38 - 1 := by rw [← hnext]; exact hmax rfl
      simp only [hlast] at hdec
      generalize hR : decryptFrom inst dec' (List.drop 16400 body) = R at hdec
      obtain ⟨m', hR', rfl⟩ : ∃ m', R = ok (.Ok m') ∧ m = p.val ++ m' := by
        cases R <;> simp_all
        rename_i v; cases v <;> simp_all
      subst hR'
      have hpl' : p.val.length = 16384 := by simpa [Slice.length] using hpl
      have hpS : Slice.from ((p.val ++ m').take 16384) (by scalar_tac) = p := by
        rw [Slice.eq_iff, Slice.from_val]; exact List.take_left' hpl'
      obtain ⟨⟨r, enc', c'⟩, hseal, hec, -, hr⟩ := spec_ok_eq
        (Encryptor.seal_spec inst enc hA (Slice.from ((p.val ++ m').take 16384) (by scalar_tac))
          false hf hn38 (by simp; omega))
      cases r with
      | Err e => simp at hr; omega
      | Ok tag' =>
        obtain ⟨⟨n', hn', hs'⟩, hen, hef, -⟩ := hr
        rw [hn, ok_eq_ok_iff] at hn'
        subst hn'
        rw [hpS, hs, ok_eq_ok_iff, Prod.mk.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        have hrest := integrity (List.drop 16400 body) enc' dec' (hec ▸ hA) (hec ▸ hT)
          (by rw [hdc', hc, hec]) (by apply UScalar.eq_of_val_eq; rw [hdn, hen, hnext])
          (by simp [hef]) (by simp [hdone']) hdf' (by rw [hen]; omega) m' hR
        have hdrop : List.drop 16384 (p.val ++ m') = m' := List.drop_left' hpl'
        rw [hpS] at hseal
        rw [encryptFrom, dite_eq_right (by simp; omega), hpS, hseal]
        have hbody : d.val ++ (t.val ++ List.drop 16400 body) = body := by
          rw [← List.append_assoc, hdt, List.take_append_drop]
        simp [hdrop, hrest, hbody]
termination_by body.length
decreasing_by simp; omega

end cobblestone.raw
