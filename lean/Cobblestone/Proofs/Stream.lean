module
public import Cobblestone.Proofs.Full
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone.buffer

open raw

def mapOk (f : List U8 → List U8) (r : Result (core.result.Result (List U8) Error)) :
    Result (core.result.Result (List U8) Error) := do
  let x ← r
  match x with
  | .Ok c => ok (.Ok (f c))
  | .Err e => ok (.Err e)

theorem mapOk_id (r : Result (core.result.Result (List U8) Error)) :
    mapOk (fun c => c) r = r := by
  unfold mapOk
  have h : (fun x : core.result.Result (List U8) Error => match x with
      | .Ok c => (ok (.Ok c) : Result _)
      | .Err e => ok (.Err e)) = ok := by
    funext x; cases x <;> rfl
  rw [h, Std.bind_pure]

theorem mapOk_mapOk (f g : List U8 → List U8) (r : Result (core.result.Result (List U8) Error)) :
    mapOk f (mapOk g r) = mapOk (fun c => f (g c)) r := by
  unfold mapOk
  rw [Std.bind_assoc]
  congr 1
  funext x
  cases x <;> simp

variable {A : Type} (inst : ChunkAead A)

theorem encryptFrom_full (enc enc' : Encryptor A) (chunk c : Slice U8) (tag : Std.Array U8 16#usize)
    (hlen : chunk.val.length = 16384)
    (hseal : Encryptor.seal inst enc chunk false = ok (.Ok tag, enc', c)) (X : List U8) :
    encryptFrom inst enc (chunk.val ++ X) =
      mapOk (fun ct => c.val ++ tag.val ++ ct) (encryptFrom inst enc' X) := by
  have hS : Slice.from ((chunk.val ++ X).take 16384) (by scalar_tac) = chunk := by
    rw [Slice.eq_iff, Slice.from_val, ← hlen, List.take_left' rfl]
  rw [encryptFrom, dite_eq_right (by simp; omega), hS, hseal, bind_ok]
  simp only [← hlen, List.drop_left' rfl, mapOk, List.append_assoc]
  rfl

theorem encryptFrom_last (enc enc' : Encryptor A) (chunk c : Slice U8) (tag : Std.Array U8 16#usize)
    (hlen : chunk.val.length < 16384)
    (hseal : Encryptor.seal inst enc chunk true = ok (.Ok tag, enc', c)) :
    encryptFrom inst enc chunk.val = ok (.Ok (c.val ++ tag.val)) := by
  have hS : Slice.from chunk.val (by scalar_tac) = chunk := by rw [Slice.eq_iff, Slice.from_val]
  rw [encryptFrom, dite_eq_left hlen]
  simp [hS, hseal]

theorem spec_of_eq {α : Type} {m : Result α} {v : α} {p : α → Prop} (h : m = ok v)
    (hs : m ⦃ p ⦄) : p v := by
  rw [h] at hs; simpa using hs

theorem EncryptBuffer.seal_spec (st : EncryptBuffer A) (buf : Slice U8) (last : Bool)
    (hA : AeadTotal inst st.enc.cipher.aead) (hf : ¬ st.enc.finished)
    (hn : st.enc.next.val < 2 ^ 38) (hbuf : buf.length = 16400)
    (hacc : if last then st.acc.val < 16384 else st.acc.val = 16384) :
    EncryptBuffer.seal inst st buf last ⦃ r st' buf' =>
      buf'.length = 16400 ∧
      ∃ (chunk c : Slice U8) (re : core.result.Result (Std.Array U8 16#usize) Error),
        chunk.val = buf.val.take st.acc.val ∧
        Encryptor.seal inst st.enc chunk last = ok (re, st'.enc, c) ∧
        (∀ tag, re = .Ok tag → r = .Ok () ∧ st'.acc.val = 0 ∧ st'.pos.val = 0 ∧
            st'.end.val = st.acc.val + 16 ∧ buf'.val.take (st.acc.val + 16) = c.val ++ tag.val) ∧
        (∀ e, re = .Err e → r = .Err e) ⦄ := by
  have hlen : st.acc.val ≤ 16384 := by split at hacc <;> omega
  unfold EncryptBuffer.seal
  step as ⟨chunk, back, hcv, hcl, hback⟩
  have hcv' : chunk.val = buf.val.take st.acc.val := by rw [hcv, List.slice_zero_j]
  have hclen : chunk.length < 16384 ∨ chunk.length = 16384 := by
    simp only [Slice.length, hcv', List.length_take]; omega
  obtain ⟨⟨re, enc', c⟩, hseal, hpost⟩ := spec_ok_eq
    (Encryptor.seal_spec inst st.enc hA chunk last hf hn (by
      split at hacc <;> simp_all [Slice.length]))
  have hS : Encryptor.seal inst st.enc chunk last ⦃ r e s1 => r = re ∧ e = enc' ∧ s1 = c ⦄ := by
    rw [hseal]; simp
  step as ⟨r, e, s1, hr, he, hs1⟩
  subst hr he hs1
  obtain ⟨-, hcl', hpost⟩ := hpost
  cases r with
  | Err err =>
    step*
  | Ok tag =>
    step*
    have hcf : cf = .Continue val := ‹_›
    rw [cf_post] at hcf
    injection hcf with hval
    subst hval
    have hs1 : s1.val.length = st.acc.val := by
      simp only [Slice.length] at hcl' hcl; omega
    have hbl : (back s1).val.length = 16400 := by
      rw [hback, List.length_setSlice!]; exact hbuf
    have hb1 : (back s1).val.take st.acc.val = s1.val := by
      rw [hback, ← hs1, show s1.val.length = 0 + s1.val.length by simp,
        header.take_setSlice _ _ _ (by simp only [Slice.length] at hbuf; omega)]
      simp
    have hv4 : s4.val = tag.val := by rw [s4_post, s3_post, Aeneas.Std.Array.val_to_slice]
    have hT : (16 : Nat) = s4.val.length := by rw [hv4]; simp
    refine ⟨?_, chunk, s1, _, hcv', hseal, fun tag' ht => ?_, fun e' he' => by cases he'⟩
    · rw [s2_post2, Slice.setSlice!_length]; exact hbl
    · cases ht
      and_intros
      all_goals try rfl
      all_goals try scalar_tac
      rw [s2_post2, Slice.setSlice!_val,
        show st.acc.val + 16 = st.acc.val + s4.val.length by rw [← hT],
        header.take_setSlice _ _ _ (by rw [← hT]; omega), hb1, hv4]

theorem slice_split {α : Type} (l : List α) (a k c : Nat) (hk : a + k ≤ c) :
    (l.slice a c).take k ++ l.slice (a + k) c = l.slice a c := by
  unfold List.slice
  rw [List.take_take, show min k (c - a) = k by omega, ← List.drop_drop,
    show c - (a + k) = (c - a) - k by omega, ← List.take_add, show k + (c - a - k) = c - a by omega]

def pend (st : EncryptBuffer A) (buf : Slice U8) : List U8 := buf.val.slice st.pos.val st.end.val

/-- The invariant of an encrypting buffer before the final chunk. `pre` is the
output emitted before the first chunk (the header), `enc0` the encryptor it
started from, `out` the output drained so far and `acc` the plaintext accepted
so far. -/
def EncInv (pre : List U8) (enc0 : Encryptor A) (st : EncryptBuffer A) (buf : Slice U8)
    (out acc : List U8) : Prop :=
  buf.length = 16400 ∧ st.enc.cipher = enc0.cipher ∧ ¬ st.enc.finished ∧
  st.enc.next.val < 2 ^ 38 ∧ st.pos.val ≤ st.end.val ∧ st.end.val ≤ 16400 ∧
  st.acc.val < 16384 ∧ (st.pos.val < st.end.val → st.acc.val = 0) ∧
  ∃ sealedPt sealedCT,
    acc = sealedPt ++ buf.val.take st.acc.val ∧
    out ++ pend st buf = pre ++ sealedCT ∧
    ∀ X, encryptFrom inst enc0 (sealedPt ++ X) =
      mapOk (fun ct => sealedCT ++ ct) (encryptFrom inst st.enc X)

/-- The invariant once the final chunk has been sealed: the output drained so
far, followed by the output pending, is the one-shot encryption of `acc`. -/
def EncDone (pre : List U8) (enc0 : Encryptor A) (st : EncryptBuffer A) (buf : Slice U8)
    (out acc : List U8) : Prop :=
  buf.length = 16400 ∧ st.pos.val ≤ st.end.val ∧ st.end.val ≤ 16400 ∧
  ∃ ct, encryptFrom inst enc0 acc = ok (.Ok ct) ∧ out ++ pend st buf = pre ++ ct

theorem EncryptBuffer.new_spec (enc0 : Encryptor A) (buf pre : Slice U8)
    (hbuf : buf.length = 16400) (hpre : pre.length ≤ 16400) (hf : ¬ enc0.finished)
    (hn : enc0.next.val < 2 ^ 38) :
    EncryptBuffer.new inst enc0 buf pre ⦃ st buf' => EncInv inst pre.val enc0 st buf' [] [] ⦄ := by
  unfold EncryptBuffer.new
  step*
  have hpl : pre.len.val = pre.val.length := Slice.len_val _
  have hb : (index_mut_back s1).val = buf.val.setSlice! 0 pre.val := by rw [s_post2, s1_post]
  have hbl : (index_mut_back s1).val.length = 16400 := by
    rw [hb, List.length_setSlice!]; exact hbuf
  have hpl' : pre.val.length ≤ 16400 := hpre
  have htk : (buf.val.setSlice! 0 pre.val).take pre.val.length = pre.val := by
    rw [show pre.val.length = 0 + pre.val.length by simp,
      header.take_setSlice _ _ _ (by simp only [Slice.length] at hbuf; omega)]
    simp
  refine ⟨hbl, rfl, hf, hn, ?_, ?_, ?_, ?_, [], [], by simp, ?_, fun X => by simp [mapOk_id]⟩
  all_goals try dsimp only
  · simp
  · omega
  · simp
  · simp
  · simp [pend, List.slice, hb, hpl, htk]

theorem advance_pend (st : EncryptBuffer A) (buf : Slice U8) (n : Usize)
    (hpe : st.pos.val ≤ st.end.val) :
    EncryptBuffer.advance inst st n ⦃ st' =>
      st'.enc = st.enc ∧ st'.acc = st.acc ∧ st'.pos.val ≤ st'.end.val ∧
      st'.end.val ≤ st.end.val ∧ (st'.pos.val < st'.end.val → st.pos.val < st.end.val) ∧
      (pend st buf).take (min n.val (st.end.val - st.pos.val)) ++ pend st' buf =
        pend st buf ⦄ := by
  unfold EncryptBuffer.advance
  step*
  all_goals
    have hk : i1.val = min n.val (st.end.val - st.pos.val) := by
      rw [i1_post, core.cmp.impls.OrdUsize.min_val, i_post]
  · have he : i2.val = st.end.val := by rw [‹i2 = st.end›]
    have hfull : min n.val (st.end.val - st.pos.val) = st.end.val - st.pos.val := by omega
    refine ⟨le_refl _, Nat.zero_le _, fun h => absurd h (lt_irrefl _), ?_⟩
    simp only [pend, hfull]
    unfold List.slice
    rw [List.take_take, min_self]
    simp
  · have hne : i2.val ≠ st.end.val := fun h => ‹¬i2 = st.end› (UScalar.eq_of_val_eq h)
    simp only [pend]
    rw [show i2.val = st.pos.val + min n.val (st.end.val - st.pos.val) by omega]
    refine ⟨by omega, le_refl _, fun _ => by omega, ?_⟩
    exact slice_split _ _ _ _ (by omega)

theorem EncInv_advance {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc) (n : Usize) :
    EncryptBuffer.advance inst st n ⦃ st' =>
      EncInv inst pre enc0 st' buf
        (out ++ (pend st buf).take (min n.val (st.end.val - st.pos.val))) acc ⦄ := by
  obtain ⟨hbl, hc, hf, hn, hpe, hend, hacc, hpa, sp, sc, hsp, hout, hX⟩ := h
  apply WP.spec_mono (advance_pend inst st buf n hpe)
  rintro st' ⟨henc, hacc', hpe', hend', hpos', hsplit⟩
  unfold EncInv
  rw [henc, hacc']
  refine ⟨hbl, hc, hf, hn, hpe', by omega, hacc, fun h' => hpa (hpos' h'), sp, sc, hsp, ?_, hX⟩
  rw [List.append_assoc, hsplit, hout]

theorem EncDone_advance {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncDone inst pre enc0 st buf out acc) (n : Usize) :
    EncryptBuffer.advance inst st n ⦃ st' =>
      EncDone inst pre enc0 st' buf
        (out ++ (pend st buf).take (min n.val (st.end.val - st.pos.val))) acc ⦄ := by
  obtain ⟨hbl, hpe, hend, ct, hct, hout⟩ := h
  apply WP.spec_mono (advance_pend inst st buf n hpe)
  rintro st' ⟨-, -, hpe', hend', -, hsplit⟩
  refine ⟨hbl, hpe', by omega, ct, hct, ?_⟩
  rw [List.append_assoc, hsplit, hout]

theorem take_add_slice {α : Type} (l : List α) (a k : Nat) :
    l.take (a + k) = l.take a ++ l.slice a (a + k) := by
  rw [List.take_add]; simp [List.slice]

theorem EncInv_filled {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc)
    (hA : AeadTotal inst enc0.cipher.aead) (hd : st.pos = st.end) (buf' : Slice U8)
    (hbl' : buf'.length = 16400) (hkeep : buf'.val.take st.acc.val = buf.val.take st.acc.val)
    (n : Usize) :
    EncryptBuffer.filled inst st buf' n ⦃ r st' buf'' =>
      (r = .Ok () → EncInv inst pre enc0 st' buf'' out
        (acc ++ buf'.val.slice st.acc.val (st.acc.val + min n.val (16384 - st.acc.val)))) ∧
      (∀ e, r = .Err e → e = .MessageTooLarge) ⦄ := by
  obtain ⟨hbl, hc, hf, hn, hpe, hend, hacc, hpa, sp, sc, hsp, hout, hX⟩ := h
  have hpend : pend st buf = [] := by simp [pend, List.slice, hd]
  unfold EncryptBuffer.filled
  step*
  all_goals
    have hk : i3.val = st.acc.val + min n.val (16384 - st.acc.val) := by
      rw [i3_post, i2_post, core.cmp.impls.OrdUsize.min_val, i1_post, i_post]
    have hacc' : acc ++ buf'.val.slice st.acc.val (st.acc.val + min n.val (16384 - st.acc.val)) =
        sp ++ buf'.val.take i3.val := by
      rw [hsp, hk, take_add_slice _ st.acc.val, hkeep, List.append_assoc]
  · have hfull : i3.val = 16384 := by rw [‹i3 = i›, i_post]
    have hA' : AeadTotal inst st.enc.cipher.aead := hc ▸ hA
    apply WP.spec_mono (EncryptBuffer.seal_spec inst { st with acc := i } buf' false hA' hf hn hbl'
      (by simp only [Bool.false_eq_true, ite_false]; rw [i_post]))
    rintro ⟨r, st'', buf''⟩ ⟨hbl'', chunk, c, re, hchunk, hseal, hok, herr⟩
    simp only at hchunk hseal hok herr
    have hpost := spec_of_eq hseal (Encryptor.seal_spec inst st.enc hA' chunk false hf hn (by
      simp [Slice.length, hchunk, i_post]; simp only [Slice.length] at hbl'; omega))
    obtain ⟨hcip, hcl, hpost⟩ := hpost
    cases re with
    | Err e =>
      obtain ⟨rfl, -⟩ := hpost
      refine ⟨fun hr => ?_, fun e' he' => ?_⟩
      · rw [herr _ rfl] at hr; cases hr
      · rw [herr _ rfl] at he'; cases he'; rfl
    | Ok tag =>
      obtain ⟨-, hnext, hfin, hlt⟩ := hpost
      obtain ⟨hr, hacc0, hpos0, hend0, htake⟩ := hok tag rfl
      refine ⟨fun _ => ?_, fun e he => by rw [hr] at he; cases he⟩
      have hchunkl : chunk.val.length = 16384 := by
        rw [hchunk, List.length_take, i_post]; simp only [Slice.length] at hbl'; omega
      unfold EncInv
      have hi : i.val = 16384 := i_post
      refine ⟨hbl'', hcip.trans hc, by simp [hfin], hlt (by simp), ?_, ?_, ?_, fun _ => hacc0,
        sp ++ chunk.val, sc ++ (c.val ++ tag.val), ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · rw [hacc', hacc0, hchunk, hfull, hi]; simp
      · rw [hi] at htake
        have hp : pend st'' buf'' = c.val ++ tag.val := by
          simp only [pend, List.slice, hpos0, hend0, hi]
          simpa using htake
        have ho : out = pre ++ sc := by simpa [hpend] using hout
        rw [hp, ho]; simp
      · intro X
        rw [List.append_assoc, hX, encryptFrom_full inst _ _ chunk c tag hchunkl hseal, mapOk_mapOk]
        congr 1; funext ct; simp
  · have hlt : i3.val < 16384 := by
      have : i3 ≠ i := ‹¬i3 = i›
      have : i3.val ≠ i.val := fun h => this (UScalar.eq_of_val_eq h)
      rw [i_post] at this; omega
    refine ⟨fun _ => ?_, fun e he => by cases he⟩
    unfold EncInv
    refine ⟨hbl', hc, hf, hn, hpe, hend, hlt, fun h' => by simp only [hd] at h'; omega,
      sp, sc, hacc', ?_, hX⟩
    simpa [pend, List.slice, hd] using hout

theorem EncInv_seal_last {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc)
    (hA : AeadTotal inst enc0.cipher.aead) (hd : st.pos = st.end) :
    EncryptBuffer.seal inst st buf true ⦃ r st' buf' =>
      r = .Ok () ∧ EncDone inst pre enc0 st' buf' out acc ⦄ := by
  obtain ⟨hbl, hc, hf, hn, hpe, hend, hacc, hpa, sp, sc, hsp, hout, hX⟩ := h
  have hA' : AeadTotal inst st.enc.cipher.aead := hc ▸ hA
  apply WP.spec_mono (EncryptBuffer.seal_spec inst st buf true hA' hf hn hbl (by simpa using hacc))
  rintro ⟨r, st', buf'⟩ ⟨hbl', chunk, c, re, hchunk, hseal, hok, herr⟩
  have hchunkl : chunk.val.length < 16384 := by
    rw [hchunk, List.length_take]; omega
  have hpost := spec_of_eq hseal (Encryptor.seal_spec inst st.enc hA' chunk true hf hn (by
    simp only [ite_true, Slice.length]; omega))
  obtain ⟨-, -, hpost⟩ := hpost
  cases re with
  | Err e => obtain ⟨-, h, -⟩ := hpost; simp at h
  | Ok tag =>
    obtain ⟨hr, -, hpos0, hend0, htake⟩ := hok tag rfl
    refine ⟨hr, hbl', by omega, by omega, sc ++ (c.val ++ tag.val), ?_, ?_⟩
    · rw [hsp, ← hchunk, hX, encryptFrom_last inst _ _ chunk c tag hchunkl hseal]
      simp [mapOk]
    · have hpend : pend st buf = [] := by simp [pend, List.slice, hd]
      have ho : out = pre ++ sc := by simpa [hpend] using hout
      have hp : pend st' buf' = c.val ++ tag.val := by
        simp only [pend, List.slice, hpos0, hend0]
        simpa using htake
      rw [hp, ho]; simp

theorem take_setSlice_prefix {α : Type} (l s : List α) (i : Nat) (h : i ≤ l.length) :
    (l.setSlice! i s).take i = l.take i := by
  simp only [List.setSlice!, List.append_assoc]
  rw [List.take_left' (by simp; omega)]

theorem slice_setSlice {α : Type} (l s : List α) (i : Nat) (h : i + s.length ≤ l.length) :
    (l.setSlice! i s).slice i (i + s.length) = s := by
  have h1 := header.take_setSlice l s i h
  have h2 := take_setSlice_prefix l s i (by omega)
  have h3 := take_add_slice (l.setSlice! i s) i s.length
  rw [h1, h2] at h3
  exact (List.append_cancel_left h3).symm

theorem EncInv_absorb {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc)
    (hA : AeadTotal inst enc0.cipher.aead) (hd : st.pos = st.end) (data : Slice U8) :
    EncryptBuffer.absorb inst st buf data ⦃ r st' buf' =>
      (∀ n, r = .Ok n → n.val = min data.length (16384 - st.acc.val) ∧
        EncInv inst pre enc0 st' buf' out (acc ++ data.val.take n.val)) ∧
      (∀ e, r = .Err e → e = .MessageTooLarge) ⦄ := by
  have h' := h
  obtain ⟨hbl, hc, hf, hn, hpe, hend, hacc, hpa, sp, sc, hsp, hout, hX⟩ := h'
  unfold EncryptBuffer.absorb
  step*
  all_goals
    have hnv : n.val = min data.length (16384 - st.acc.val) := by
      rw [n_post, core.cmp.impls.OrdUsize.min_val, i2_post, i1_post, Slice.len_val]
  · rw [s_post1, s1_post1, i3_post]; omega
  · have hs2 : s2.val = data.val.take n.val := by rw [s2_post, s1_post, List.slice_zero_j]
    have hs2l : s2.val.length = n.val := by
      rw [hs2, List.length_take]; simp only [Slice.length] at hnv ⊢; omega
    have hb : (index_mut_back s2).val = buf.val.setSlice! st.acc.val s2.val := by
      rw [s_post2, Slice.setSlice!_val]
    have hbl2 : (index_mut_back s2).length = 16400 := by
      simp only [Slice.length]; rw [hb, List.length_setSlice!]; exact hbl
    have hkeep : (index_mut_back s2).val.take st.acc.val = buf.val.take st.acc.val := by
      rw [hb, take_setSlice_prefix _ _ _ (by simp only [Slice.length] at hbl; omega)]
    have hsl : (index_mut_back s2).val.slice st.acc.val
        (st.acc.val + min n.val (16384 - st.acc.val)) = data.val.take n.val := by
      rw [show min n.val (16384 - st.acc.val) = s2.val.length by omega, hb,
        slice_setSlice _ _ _ (by simp only [Slice.length] at hbl; omega), hs2]
    have hF := EncInv_filled inst h hA hd (index_mut_back s2) hbl2 hkeep n
    rw [hsl] at hF
    step as ⟨r, st1, buf2, hok, herr⟩
    cases r with
    | Ok u => step*; exact ⟨fun n' hn' => by cases hn'; exact ⟨hnv, hok rfl⟩, fun e he => by cases he⟩
    | Err e0 =>
      step*
      have hcf := ‹cf = core.ops.control_flow.ControlFlow.Break residual›
      rw [cf_post] at hcf
      injection hcf with hres
      rw [← hres] at residual_post
      injection residual_post with he1
      refine ⟨fun n hn => (by rw [r1_post] at hn; cases hn), fun e' he' => ?_⟩
      rw [r1_post] at he'
      injection he' with he2
      rw [← he2, ← e_post, ← he1]
      exact herr _ rfl

theorem take_slice {α : Type} (l : List α) (a k c : Nat) (h : a + k ≤ c) :
    (l.slice a c).take k = l.slice a (a + k) := by
  simp only [List.slice, List.take_take]
  congr 1; omega

theorem EncInv_fill {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc)
    (hA : AeadTotal inst enc0.cipher.aead) (hd : st.pos = st.end) (n : Usize) :
    EncryptBuffer.space inst st buf ⦃ s back =>
      s.length = 16384 - st.acc.val ∧
      ∀ s' : Slice U8, s'.length = s.length →
        EncryptBuffer.filled inst st (back s') n ⦃ r st' buf' =>
          (r = .Ok () → EncInv inst pre enc0 st' buf' out
            (acc ++ s'.val.take (min n.val (16384 - st.acc.val)))) ∧
          (∀ e, r = .Err e → e = .MessageTooLarge) ⦄ ⦄ := by
  have h' := h
  obtain ⟨hbl, -, -, -, -, -, hacc, -⟩ := h'
  have hbl0 : buf.val.length = 16400 := hbl
  unfold EncryptBuffer.space
  step*
  refine ⟨by rw [s_post1, i_post], fun s' hs' => ?_⟩
  have hsl : s'.val.length = 16384 - st.acc.val := by
    have : s'.length = s.length := hs'
    simp only [Slice.length] at this s_post1; rw [this, s_post1, i_post]
  have hb : (back s').val = buf.val.setSlice! st.acc.val s'.val := by
    rw [‹∀ (s' : Slice U8), back s' = buf.setSlice! ↑st.acc ↑s'›, Slice.setSlice!_val]
  have hbl' : (back s').length = 16400 := by
    simp only [Slice.length]; rw [hb, List.length_setSlice!]; exact hbl0
  have hkeep : (back s').val.take st.acc.val = buf.val.take st.acc.val := by
    rw [hb, take_setSlice_prefix _ _ _ (by omega)]
  apply WP.spec_mono (EncInv_filled inst h hA hd (back s') hbl' hkeep n)
  rintro ⟨r, st', buf'⟩ ⟨hok, herr⟩
  refine ⟨fun hr => ?_, herr⟩
  have hk := hok hr
  rwa [← take_slice _ _ _ (st.acc.val + s'.val.length) (by omega), hb,
    slice_setSlice _ _ _ (by omega)] at hk

/-- Once the final chunk has been sealed and all output drained, the output is
the one-shot encryption of the plaintext accepted. -/
theorem EncDone_drained {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncDone inst pre enc0 st buf out acc)
    (hd : st.pos = st.end) :
    ∃ ct, encryptFrom inst enc0 acc = ok (.Ok ct) ∧ out = pre ++ ct := by
  obtain ⟨-, -, -, ct, hct, hout⟩ := h
  refine ⟨ct, hct, ?_⟩
  simpa [pend, List.slice, hd] using hout

theorem pending_spec (st : EncryptBuffer A) (buf : Slice U8) (hpe : st.pos.val ≤ st.end.val)
    (hend : st.end.val ≤ buf.length) :
    EncryptBuffer.pending inst st buf ⦃ p => p.val = pend st buf ⦄ := by
  unfold EncryptBuffer.pending
  step*
  simp [pend, *]

/-- What the streaming wrappers can do to an encrypting buffer: accept written
plaintext, let a source write any bytes into the free space and report any
count, or have any amount of the pending output written out or read out. -/
inductive EncOp
  | absorb (data : Slice U8)
  | fill (data : Slice U8) (n : Usize)
  | drain (n : Usize)

/-- One operation, with the output drained and the plaintext accepted so far.
Plaintext is only accepted once the pending output is drained, as the wrappers
do. `none` means the operation failed, which ends the stream. -/
def encStep (st : EncryptBuffer A) (buf : Slice U8) (out acc : List U8) :
    EncOp → Result (Option (EncryptBuffer A × Slice U8 × List U8 × List U8))
  | .drain n => do
    let p ← EncryptBuffer.pending inst st buf
    let st' ← EncryptBuffer.advance inst st n
    ok (some (st', buf, out ++ p.val.take n.val, acc))
  | .absorb data => do
    let d ← EncryptBuffer.is_drained inst st
    if d then
      let res ← EncryptBuffer.absorb inst st buf data
      match res.1 with
      | .Ok n => ok (some (res.2.1, res.2.2, out, acc ++ data.val.take n.val))
      | .Err _ => ok none
    else ok (some (st, buf, out, acc))
  | .fill data n => do
    let d ← EncryptBuffer.is_drained inst st
    if d then
      let sb ← EncryptBuffer.space inst st buf
      if data.length = sb.1.length then
        let res ← EncryptBuffer.filled inst st (sb.2 data) n
        match res.1 with
        | .Ok _ => ok (some (res.2.1, res.2.2, out, acc ++ data.val.take n.val))
        | .Err _ => ok none
      else ok (some (st, buf, out, acc))
    else ok (some (st, buf, out, acc))

def runEnc (st : EncryptBuffer A) (buf : Slice U8) (out acc : List U8) :
    List EncOp → Result (Option (EncryptBuffer A × Slice U8 × List U8 × List U8))
  | [] => ok (some (st, buf, out, acc))
  | op :: ops => do
    let o ← encStep inst st buf out acc op
    match o with
    | none => ok none
    | some (st', buf', out', acc') => runEnc st' buf' out' acc' ops

theorem encStep_spec {pre : List U8} {enc0 : Encryptor A} {st : EncryptBuffer A}
    {buf : Slice U8} {out acc : List U8} (h : EncInv inst pre enc0 st buf out acc)
    (hA : AeadTotal inst enc0.cipher.aead) (op : EncOp) :
    encStep inst st buf out acc op ⦃ o =>
      ∀ x, o = some x → EncInv inst pre enc0 x.1 x.2.1 x.2.2.1 x.2.2.2 ⦄ := by
  have h0 := h
  obtain ⟨hbl, -, -, -, hpe, hend, -⟩ := h0
  have hplen : (pend st buf).length = st.end.val - st.pos.val := by
    simp only [pend, List.slice, List.length_take, List.length_drop]
    simp only [Slice.length] at hbl; omega
  cases op with
  | drain n =>
    unfold encStep
    have hp := pending_spec inst st buf hpe (by omega)
    step as ⟨p, hpv⟩
    apply WP.spec_bind (EncInv_advance inst h n)
    intro st' h'
    simp only [WP.spec_ok]
    intro x hx; simp only [Option.some.injEq] at hx; subst hx
    have hk : p.val.take n.val = (pend st buf).take (min n.val (st.end.val - st.pos.val)) := by
      rw [hpv, ← hplen]
      rcases Nat.le_total n.val (pend st buf).length with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right hle, List.take_of_length_le hle, List.take_length]
    rw [hk]; exact h'
  | absorb data =>
    unfold encStep
    simp only [EncryptBuffer.is_drained, bind_ok]
    by_cases hd : st.pos = st.end
    · simp only [hd, decide_true, ite_true]
      apply WP.spec_bind (EncInv_absorb inst h hA hd data)
      rintro ⟨r, st', buf'⟩ ⟨hok, -⟩
      cases r with
      | Ok n =>
        simp only [WP.spec_ok]
        intro x hx; simp only [Option.some.injEq] at hx; subst hx
        exact (hok n rfl).2
      | Err e => simp only [WP.spec_ok]; intro x hx; cases hx
    · simp only [hd, decide_false, Bool.false_eq_true, ite_false, WP.spec_ok]
      intro x hx; simp only [Option.some.injEq] at hx; subst hx; exact h
  | fill data n =>
    unfold encStep
    simp only [EncryptBuffer.is_drained, bind_ok]
    by_cases hd : st.pos = st.end
    · simp only [hd, decide_true, ite_true]
      apply WP.spec_bind (EncInv_fill inst h hA hd n)
      rintro ⟨s, back⟩ ⟨hsl, hF⟩
      by_cases hl : data.length = s.length
      · simp only [hl, ite_true]
        apply WP.spec_bind (hF data hl)
        rintro ⟨r, st', buf'⟩ ⟨hok, -⟩
        cases r with
        | Ok u =>
          simp only [WP.spec_ok]
          intro x hx; simp only [Option.some.injEq] at hx; subst hx
          have hk : data.val.take n.val = data.val.take (min n.val (16384 - st.acc.val)) := by
            have hdl : data.val.length = 16384 - st.acc.val := by
              have := hl; simp only [Slice.length] at this hsl ⊢; omega
            rw [← hdl]
            rcases Nat.le_total n.val data.val.length with hle | hle
            · rw [Nat.min_eq_left hle]
            · rw [Nat.min_eq_right hle, List.take_of_length_le hle, List.take_length]
          rw [hk]; exact hok rfl
        | Err e => simp only [WP.spec_ok]; intro x hx; cases hx
      · simp only [hl, ite_false, WP.spec_ok]
        intro x hx; simp only [Option.some.injEq] at hx; subst hx; exact h
    · simp only [hd, decide_false, Bool.false_eq_true, ite_false, WP.spec_ok]
      intro x hx; simp only [Option.some.injEq] at hx; subst hx; exact h

theorem runEnc_spec {pre : List U8} {enc0 : Encryptor A} (hA : AeadTotal inst enc0.cipher.aead)
    (ops : List EncOp) : ∀ {st : EncryptBuffer A} {buf : Slice U8} {out acc : List U8},
    EncInv inst pre enc0 st buf out acc →
    runEnc inst st buf out acc ops ⦃ o =>
      ∀ x, o = some x → EncInv inst pre enc0 x.1 x.2.1 x.2.2.1 x.2.2.2 ⦄ := by
  induction ops with
  | nil =>
    intro st buf out acc h
    simp only [runEnc, WP.spec_ok]
    intro x hx; simp only [Option.some.injEq] at hx; subst hx; exact h
  | cons op ops ih =>
    intro st buf out acc h
    unfold runEnc
    apply WP.spec_bind (encStep_spec inst h hA op)
    rintro (_ | ⟨st', buf', out', acc'⟩) hx
    · simp
    · exact ih (hx _ rfl)

def runDrains (st : EncryptBuffer A) (buf : Slice U8) (out : List U8) :
    List Usize → Result (EncryptBuffer A × List U8)
  | [] => ok (st, out)
  | n :: ns => do
    let p ← EncryptBuffer.pending inst st buf
    let st' ← EncryptBuffer.advance inst st n
    runDrains st' buf (out ++ p.val.take n.val) ns

theorem runDrains_spec {pre : List U8} {enc0 : Encryptor A} {acc : List U8} (ns : List Usize) :
    ∀ {st : EncryptBuffer A} {buf : Slice U8} {out : List U8},
    EncDone inst pre enc0 st buf out acc →
    runDrains inst st buf out ns ⦃ r => EncDone inst pre enc0 r.1 buf r.2 acc ⦄ := by
  induction ns with
  | nil => intro st buf out h; simpa [runDrains] using h
  | cons n ns ih =>
    intro st buf out h
    have h0 := h
    obtain ⟨hbl, hpe, hend, -⟩ := h0
    have hplen : (pend st buf).length = st.end.val - st.pos.val := by
      simp only [pend, List.slice, List.length_take, List.length_drop]
      simp only [Slice.length] at hbl; omega
    unfold runDrains
    have hp := pending_spec inst st buf hpe (by omega)
    step as ⟨p, hpv⟩
    apply WP.spec_bind (EncDone_advance inst h n)
    intro st' h'
    have hk : p.val.take n.val = (pend st buf).take (min n.val (st.end.val - st.pos.val)) := by
      rw [hpv, ← hplen]
      rcases Nat.le_total n.val (pend st buf).length with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right hle, List.take_of_length_le hle, List.take_length]
    rw [hk]; exact ih h'

/-- A whole encrypting stream: `pre` (the header) pending, then any operations,
then the final chunk sealed once the output is drained, as `poll_finish` and the
end of the source do, then any further drains. The result is the output drained,
the plaintext accepted, and whether all the output was drained. -/
def streamEncrypt (enc0 : Encryptor A) (buf pre : Slice U8) (ops : List EncOp)
    (drains : List Usize) : Result (Option (List U8 × List U8 × Bool)) := do
  let sb ← EncryptBuffer.new inst enc0 buf pre
  let o ← runEnc inst sb.1 sb.2 [] [] ops
  match o with
  | none => ok none
  | some (st, buf, out, acc) =>
    let d ← EncryptBuffer.is_drained inst st
    if d then
      let res ← EncryptBuffer.seal inst st buf true
      match res.1 with
      | .Err _ => ok none
      | .Ok _ =>
        let fin ← runDrains inst res.2.1 res.2.2 out drains
        let d' ← EncryptBuffer.is_drained inst fin.1
        ok (some (fin.2, acc, d'))
    else ok none

/-- Streaming encryption produces the one-shot encryption of the plaintext it
accepted, whatever the sequence of writes, reads and drains. -/
theorem streamEncrypt_spec (enc0 : Encryptor A) (hA : AeadTotal inst enc0.cipher.aead)
    (hf : ¬ enc0.finished) (hn : enc0.next.val < 2 ^ 38) (buf pre : Slice U8)
    (hbuf : buf.length = 16400) (hpre : pre.length ≤ 16400) (ops : List EncOp)
    (drains : List Usize) :
    streamEncrypt inst enc0 buf pre ops drains ⦃ o =>
      ∀ out acc, o = some (out, acc, true) →
        ∃ ct, encryptFrom inst enc0 acc = ok (.Ok ct) ∧ out = pre.val ++ ct ⦄ := by
  unfold streamEncrypt
  apply WP.spec_bind (EncryptBuffer.new_spec inst enc0 buf pre hbuf hpre hf hn)
  rintro ⟨st, buf1⟩ h0
  apply WP.spec_bind (runEnc_spec inst hA ops h0)
  rintro (_ | ⟨st1, buf2, out1, acc1⟩) h1
  · simp
  · have h1' := h1 _ rfl
    simp only [EncryptBuffer.is_drained, bind_ok]
    by_cases hd : st1.pos = st1.end
    · simp only [hd, decide_true, ite_true]
      apply WP.spec_bind (EncInv_seal_last inst h1' hA hd)
      rintro ⟨r, st2, buf3⟩ ⟨hr, h2⟩
      simp only [hr]
      apply WP.spec_bind (runDrains_spec inst drains h2)
      rintro ⟨st3, out3⟩ h3
      simp only [WP.spec_ok]
      intro out acc ho
      simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at ho
      obtain ⟨rfl, rfl, hd3⟩ := ho
      exact EncDone_drained inst h3 hd3
    · simp [hd]

theorem decryptFrom_full (dec dec' : Decryptor A) (chunk c : Slice U8) (len : Usize)
    (hlen : chunk.val.length = 16400)
    (hopen : Decryptor.open inst dec chunk = ok (.Ok len, dec', c)) (hdone : dec'.done = false)
    (X : List U8) :
    decryptFrom inst dec (chunk.val ++ X) =
      mapOk (fun pt => c.val.take len.val ++ pt) (decryptFrom inst dec' X) := by
  have hmin : min (chunk.val ++ X).length 16400 = 16400 := by simp; omega
  have hS : Slice.from ((chunk.val ++ X).take (min (chunk.val ++ X).length 16400))
      (by scalar_tac) = chunk := by
    rw [Slice.eq_iff, Slice.from_val, hmin, ← hlen, List.take_left' rfl]
  have hdrop : List.drop 16400 (chunk.val ++ X) = X := by rw [← hlen, List.drop_left' rfl]
  have hge : ¬ (chunk.val ++ X).length < 16400 := by simp; omega
  rw [decryptFrom, hS, hopen, bind_ok]
  simp [hdone, hdrop, mapOk, show ¬ chunk.val.length + X.length < 16400 by omega]
  rfl

theorem decryptFrom_last (dec dec' : Decryptor A) (chunk c : Slice U8) (len : Usize)
    (hlen : chunk.val.length < 16400)
    (hopen : Decryptor.open inst dec chunk = ok (.Ok len, dec', c)) (hdone : dec'.done = true) :
    decryptFrom inst dec chunk.val = ok (.Ok (c.val.take len.val)) := by
  have hS : Slice.from (chunk.val.take (min chunk.val.length 16400)) (by scalar_tac) = chunk := by
    rw [Slice.eq_iff, Slice.from_val, Nat.min_eq_left (by omega), List.take_length]
  rw [decryptFrom, hS, hopen, bind_ok]
  simp [hdone]

theorem decryptFrom_err (dec dec' : Decryptor A) (chunk c : Slice U8) (e : Error)
    (X : List U8) (hlen : chunk.val.length = 16400 ∨ (chunk.val.length < 16400 ∧ X = []))
    (hopen : Decryptor.open inst dec chunk = ok (.Err e, dec', c)) :
    decryptFrom inst dec (chunk.val ++ X) = ok (.Err e) := by
  have hS : Slice.from ((chunk.val ++ X).take (min (chunk.val ++ X).length 16400))
      (by scalar_tac) = chunk := by
    rw [Slice.eq_iff, Slice.from_val]
    rcases hlen with h | ⟨h, rfl⟩
    · rw [show min (chunk.val ++ X).length 16400 = chunk.val.length by simp; omega,
        List.take_left' rfl]
    · simp; omega
  rw [decryptFrom, hS, hopen, bind_ok]
  simp

def pendD (st : DecryptBuffer A) (buf : Slice U8) : List U8 := buf.val.slice st.pos.val st.end.val

/-- The invariant of a decrypting buffer before the final chunk. `out` is the
plaintext read out so far and `ct` the ciphertext accepted so far. -/
def DecInv (dec0 : Decryptor A) (st : DecryptBuffer A) (buf : Slice U8) (out ct : List U8) :
    Prop :=
  buf.length = 16400 ∧ st.dec.cipher = dec0.cipher ∧ st.dec.failed = none ∧
  st.dec.done = false ∧ st.dec.next.val < 2 ^ 38 ∧ st.pos.val ≤ st.end.val ∧
  st.end.val ≤ 16400 ∧ st.filled.val ≤ 16400 ∧ (st.pos.val < st.end.val → st.filled.val = 0) ∧
  ∃ openedCT openedPT,
    ct = openedCT ++ buf.val.take st.filled.val ∧
    out ++ pendD st buf = openedPT ∧
    ∀ X, decryptFrom inst dec0 (openedCT ++ X) =
      mapOk (fun pt => openedPT ++ pt) (decryptFrom inst st.dec X)

/-- Once the final chunk has been authenticated: the plaintext read out so far,
followed by the plaintext pending, is the one-shot decryption of `ct`. -/
def DecDone (dec0 : Decryptor A) (st : DecryptBuffer A) (buf : Slice U8) (out ct : List U8) :
    Prop :=
  buf.length = 16400 ∧ st.dec.done = true ∧ st.dec.failed = none ∧ st.pos.val ≤ st.end.val ∧
  st.end.val ≤ 16400 ∧
  ∃ pt, decryptFrom inst dec0 ct = ok (.Ok pt) ∧ out ++ pendD st buf = pt

/-- Once decryption has failed: the one-shot decryption of `ct` fails with the
same error. -/
def DecFail (dec0 : Decryptor A) (st : DecryptBuffer A) (buf : Slice U8) (ct : List U8) : Prop :=
  buf.length = 16400 ∧ st.end.val ≤ 16400 ∧ st.dec.done = false ∧
  ∃ e, st.dec.failed = some e ∧ st.pos = st.end ∧ decryptFrom inst dec0 ct = ok (.Err e)

theorem DecryptBuffer.open_spec (st : DecryptBuffer A) (buf : Slice U8)
    (hA : AeadTotal inst st.dec.cipher.aead) (hn : st.dec.next.val < 2 ^ 38)
    (hfl : st.filled.val ≤ 16400) (hbuf : buf.length = 16400)
    (hd : st.dec.failed = none → ¬ st.dec.done) :
    DecryptBuffer.open inst st buf ⦃ r st' buf' =>
      buf'.length = 16400 ∧ st'.filled.val = 0 ∧ st'.pos.val = 0 ∧
      ∃ (chunk c : Slice U8) (re : core.result.Result Usize Error),
        chunk.val = buf.val.take st.filled.val ∧
        Decryptor.open inst st.dec chunk = ok (re, st'.dec, c) ∧
        buf'.val.take c.val.length = c.val ∧
        (∀ len, re = .Ok len → r = .Ok () ∧ st'.end = len) ∧
        (∀ e, re = .Err e → r = .Err e ∧ st'.end.val = 0) ⦄ := by
  unfold DecryptBuffer.open
  step as ⟨chunk, back, hcv, hcl, hback⟩
  have hcv' : chunk.val = buf.val.take st.filled.val := by rw [hcv, List.slice_zero_j]
  obtain ⟨⟨re, d, c⟩, hop, hpost⟩ := spec_ok_eq
    (Decryptor.open_spec inst st.dec hA chunk hn (by rw [hcl]; exact hfl) hd)
  obtain ⟨-, hcl', -⟩ := hpost
  have hS : Decryptor.open inst st.dec chunk ⦃ r e s1 => r = re ∧ e = d ∧ s1 = c ⦄ := by
    rw [hop]; simp
  step as ⟨r, e, s1, hr, he, hs1⟩
  subst hr he hs1
  have hbl : (back s1).val.length = 16400 := by
    rw [hback, List.length_setSlice!]; exact hbuf
  have htk : (back s1).val.take s1.val.length = s1.val := by
    rw [hback, show s1.val.length = 0 + s1.val.length by simp,
      header.take_setSlice _ _ _ (by simp only [Slice.length] at hcl' hcl hbuf; omega)]
    simp
  cases r with
  | Ok len =>
    simp only [WP.spec_ok]
    refine ⟨hbl, rfl, rfl, chunk, s1, _, hcv', hop, htk, fun l hl => ?_, fun e he => (by cases he)⟩
    cases hl
    exact ⟨rfl, rfl⟩
  | Err err =>
    simp only [WP.spec_ok]
    refine ⟨hbl, rfl, rfl, chunk, s1, _, hcv', hop, htk, fun l hl => (by cases hl), fun e he => ?_⟩
    cases he; exact ⟨rfl, rfl⟩

theorem DecInv_open {dec0 : Decryptor A} {st : DecryptBuffer A} {buf : Slice U8}
    {out ct : List U8} (h : DecInv inst dec0 st buf out ct) (hA : AeadTotal inst dec0.cipher.aead)
    (hd : st.pos = st.end) :
    DecryptBuffer.open inst st buf ⦃ r st' buf' =>
      (r = .Ok () → DecInv inst dec0 st' buf' out ct ∨ DecDone inst dec0 st' buf' out ct) ∧
      (∀ e, r = .Err e → DecFail inst dec0 st' buf' ct) ⦄ := by
  obtain ⟨hbl, hc, hfail, hdone, hn, hpe, hend, hfl, hpa, oct, opt, hct, hout, hX⟩ := h
  have hA' : AeadTotal inst st.dec.cipher.aead := hc ▸ hA
  have hpend : pendD st buf = [] := by simp [pendD, List.slice, hd]
  have ho : out = opt := by simpa [hpend] using hout
  apply WP.spec_mono (DecryptBuffer.open_spec inst st buf hA' hn hfl hbl (by simp [hdone]))
  rintro ⟨r, st', buf'⟩ ⟨hbl', hfl0, hpos0, chunk, c, re, hchunk, hop, htk, hok, herr⟩
  have hchl : chunk.val.length = st.filled.val := by
    rw [hchunk, List.length_take]; simp only [Slice.length] at hbl; omega
  have hpost := spec_of_eq hop (Decryptor.open_spec inst st.dec hA' chunk hn
    (by simp only [Slice.length]; omega) (by simp [hdone]))
  obtain ⟨hcip, hcl, hpost⟩ := hpost
  simp only [hfail] at hpost
  have hct' : ct = oct ++ chunk.val := by rw [hct, hchunk]
  cases re with
  | Err e =>
    obtain ⟨hr, -⟩ := herr e rfl
    obtain ⟨⟨-, hdn', -, -, -⟩, hf'⟩ := hpost
    refine ⟨fun h' => (by rw [hr] at h'; cases h'), fun e' he' => ?_⟩
    rw [hr] at he'; cases he'
    refine ⟨hbl', by rw [(herr e rfl).2]; omega, by rw [hdn', hdone], e, hf', ?_, ?_⟩
    · apply UScalar.eq_of_val_eq; rw [hpos0, (herr e rfl).2]
    · rw [hct', show oct ++ chunk.val = oct ++ (chunk.val ++ []) by simp, hX,
        decryptFrom_err inst _ _ chunk c e [] (by
          rcases Nat.lt_or_ge chunk.val.length 16400 with h' | h'
          · exact Or.inr ⟨h', rfl⟩
          · left; omega) hop]
      simp [mapOk]
  | Ok len =>
    obtain ⟨hr, hend'⟩ := hok len rfl
    obtain ⟨⟨h16, hlen, hmax, -, hnext, hdone'⟩, hf'⟩ := hpost
    refine ⟨fun _ => ?_, fun e he => by rw [hr] at he; cases he⟩
    have hcl2 : c.val.length = chunk.val.length := by simpa [Slice.length] using hcl
    have hpd : pendD st' buf' = c.val.take len.val := by
      simp only [pendD, List.slice_zero_j, hpos0, hend']
      rw [← htk, List.take_take, Nat.min_eq_left (by simp only [Slice.length] at hlen; omega)]
    have hout' : out ++ pendD st' buf' = opt ++ c.val.take len.val := by rw [hpd, ho]
    rcases Nat.lt_or_ge chunk.val.length 16400 with hshort | hfull
    · right
      have hdt : st'.dec.done = true := by rw [hdone']; simp [Slice.length]; omega
      refine ⟨hbl', hdt, hf', by omega, by rw [hend']; simp only [Slice.length] at hlen; omega,
        opt ++ c.val.take len.val, ?_, hout'⟩
      rw [hct', show oct ++ chunk.val = oct ++ (chunk.val ++ []) by simp, hX, List.append_nil,
        decryptFrom_last inst _ _ chunk c len hshort hop hdt]
      simp [mapOk]
    · left
      have hfull' : chunk.val.length = 16400 := by omega
      have hdf : st'.dec.done = false := by rw [hdone']; simp [Slice.length]; omega
      refine ⟨hbl', hcip.trans hc, hf', hdf, ?_, by omega, ?_, by omega, fun _ => by omega,
        oct ++ chunk.val, opt ++ c.val.take len.val, ?_, hout', ?_⟩
      · rw [hnext]; have := hmax (by simpa [Slice.length] using hfull'); omega
      · rw [hend']; simp only [Slice.length] at hlen; omega
      · rw [hct', hfl0]; simp
      · intro X
        rw [List.append_assoc, hX, decryptFrom_full inst _ _ chunk c len hfull' hop hdf X,
          mapOk_mapOk]
        congr 1; funext pt; simp

theorem advanceD_pend (st : DecryptBuffer A) (buf : Slice U8) (n : Usize)
    (hpe : st.pos.val ≤ st.end.val) :
    DecryptBuffer.advance inst st n ⦃ st' =>
      st'.dec = st.dec ∧ st'.filled = st.filled ∧ st'.pos.val ≤ st'.end.val ∧
      st'.end.val ≤ st.end.val ∧ (st'.pos.val < st'.end.val → st.pos.val < st.end.val) ∧
      (st.pos = st.end → st'.pos = st'.end) ∧
      (pendD st buf).take (min n.val (st.end.val - st.pos.val)) ++ pendD st' buf =
        pendD st buf ⦄ := by
  unfold DecryptBuffer.advance
  step*
  all_goals
    have hk : i1.val = min n.val (st.end.val - st.pos.val) := by
      rw [i1_post, core.cmp.impls.OrdUsize.min_val, i_post]
  · have he : i2.val = st.end.val := by rw [‹i2 = st.end›]
    have hfull : min n.val (st.end.val - st.pos.val) = st.end.val - st.pos.val := by omega
    refine ⟨le_refl _, Nat.zero_le _, fun h => absurd h (lt_irrefl _), fun _ => trivial, ?_⟩
    simp only [pendD, hfull]
    unfold List.slice
    rw [List.take_take, min_self]
    simp
  · have hne : i2.val ≠ st.end.val := fun h => ‹¬i2 = st.end› (UScalar.eq_of_val_eq h)
    simp only [pendD]
    rw [show i2.val = st.pos.val + min n.val (st.end.val - st.pos.val) by omega]
    refine ⟨by omega, le_refl _, fun _ => by omega, fun h => ?_, ?_⟩
    · exfalso; have := congrArg UScalar.val h; omega
    · exact slice_split _ _ _ _ (by omega)

theorem pendingD_spec (st : DecryptBuffer A) (buf : Slice U8) (hpe : st.pos.val ≤ st.end.val)
    (hend : st.end.val ≤ buf.length) :
    DecryptBuffer.pending inst st buf ⦃ p => p.val = pendD st buf ⦄ := by
  unfold DecryptBuffer.pending
  step*
  simp [pendD, *]

/-- The states a decrypting stream can be in, each with what it guarantees. -/
def DecState (dec0 : Decryptor A) (st : DecryptBuffer A) (buf : Slice U8) (out ct : List U8) :
    Prop :=
  DecInv inst dec0 st buf out ct ∨ DecDone inst dec0 st buf out ct ∨ DecFail inst dec0 st buf ct

theorem DecState_advance {dec0 : Decryptor A} {st : DecryptBuffer A} {buf : Slice U8}
    {out ct : List U8} (h : DecState inst dec0 st buf out ct) (n : Usize) :
    DecryptBuffer.advance inst st n ⦃ st' =>
      DecState inst dec0 st' buf
        (out ++ (pendD st buf).take (min n.val (st.end.val - st.pos.val))) ct ⦄ := by
  rcases h with h | h | h
  · obtain ⟨hbl, hc, hf, hdn, hn, hpe, hend, hfl, hpa, oct, opt, hct, hout, hX⟩ := h
    apply WP.spec_mono (advanceD_pend inst st buf n hpe)
    rintro st' ⟨hdec, hfl', hpe', hend', hpos', -, hsplit⟩
    left
    unfold DecInv
    rw [hdec, hfl']
    refine ⟨hbl, hc, hf, hdn, hn, hpe', by omega, hfl, fun h' => hpa (hpos' h'), oct, opt, hct,
      ?_, hX⟩
    rw [List.append_assoc, hsplit, hout]
  · obtain ⟨hbl, hdn, hf, hpe, hend, pt, hpt, hout⟩ := h
    apply WP.spec_mono (advanceD_pend inst st buf n hpe)
    rintro st' ⟨hdec, -, hpe', hend', -, -, hsplit⟩
    right; left
    refine ⟨hbl, hdec ▸ hdn, hdec ▸ hf, hpe', by omega, pt, hpt, ?_⟩
    rw [List.append_assoc, hsplit, hout]
  · obtain ⟨hbl, hend, hdn, e, hf, hpe, hct⟩ := h
    apply WP.spec_mono (advanceD_pend inst st buf n (by rw [hpe]))
    rintro st' ⟨hdec, -, -, hend', -, hpe', -⟩
    right; right
    exact ⟨hbl, by omega, hdec ▸ hdn, e, hdec ▸ hf, hpe' hpe, hct⟩

theorem DecInv_frame {dec0 : Decryptor A} {st : DecryptBuffer A} {buf buf' : Slice U8}
    {out ct : List U8} (h : DecInv inst dec0 st buf out ct) (hd : st.pos = st.end)
    (hbl' : buf'.length = 16400) (hkeep : buf'.val.take st.filled.val = buf.val.take st.filled.val) :
    DecInv inst dec0 st buf' out ct := by
  obtain ⟨-, hc, hf, hdn, hn, hpe, hend, hfl, hpa, oct, opt, hct, hout, hX⟩ := h
  refine ⟨hbl', hc, hf, hdn, hn, hpe, hend, hfl, hpa, oct, opt, by rw [hct, hkeep], ?_, hX⟩
  simpa [pendD, List.slice, hd] using hout

theorem DecInv_filled {dec0 : Decryptor A} {st : DecryptBuffer A} {buf : Slice U8}
    {out ct : List U8} (h : DecInv inst dec0 st buf out ct) (hd : st.pos = st.end) (n : Usize) :
    DecryptBuffer.impl.filled inst st n ⦃ full st' =>
      full = decide (st'.filled.val = 16400) ∧ st'.pos = st'.end ∧
      DecInv inst dec0 st' buf out
        (ct ++ buf.val.slice st.filled.val (st.filled.val + min n.val (16400 - st.filled.val))) ⦄ := by
  obtain ⟨hbl, hc, hf, hdn, hn, hpe, hend, hfl, hpa, oct, opt, hct, hout, hX⟩ := h
  unfold DecryptBuffer.impl.filled
  step*
  have hk : i3.val = st.filled.val + min n.val (16400 - st.filled.val) := by
    rw [i3_post, i2_post, core.cmp.impls.OrdUsize.min_val, i1_post, i_post]
  have hi : i.val = 16400 := i_post
  refine ⟨?_, hd, ?_⟩
  · simp only [decide_eq_decide]
    exact ⟨fun h => by rw [h, hi], fun h => UScalar.eq_of_val_eq (by rw [h, hi])⟩
  · refine ⟨hbl, hc, hf, hdn, hn, hpe, hend, show i3.val ≤ 16400 by omega,
      fun h' => by simp only [hd] at h'; omega, oct, opt, ?_, ?_, hX⟩
    · rw [hct, hk, take_add_slice _ st.filled.val, List.append_assoc]
    · simpa [pendD, List.slice, hd] using hout

theorem DecryptBuffer.new_spec (dec0 : Decryptor A) (buf : Slice U8) (hbuf : buf.length = 16400)
    (hf : dec0.failed = none) (hdn : dec0.done = false) (hn : dec0.next.val < 2 ^ 38) :
    DecryptBuffer.new inst dec0 ⦃ st => DecInv inst dec0 st buf [] [] ⦄ := by
  unfold DecryptBuffer.new
  simp only [WP.spec_ok]
  exact ⟨hbuf, rfl, hf, hdn, hn, by simp, by simp, by simp, fun h => by simp at h, [], [],
    by simp, by simp [pendD, List.slice], fun X => by simp [mapOk_id]⟩

theorem DecryptBuffer.space_spec (st : DecryptBuffer A) (buf : Slice U8)
    (hfl : st.filled.val ≤ 16400) (hbuf : buf.length = 16400) :
    DecryptBuffer.space inst st buf ⦃ s back =>
      s.length = 16400 - st.filled.val ∧
      ∀ s', (back s').val = buf.val.setSlice! st.filled.val s'.val ⦄ := by
  unfold DecryptBuffer.space
  step*
  refine ⟨by rw [s_post1, i_post], fun s' => ?_⟩
  rw [s_post2, Slice.setSlice!_val]

/-- What `DecryptRead` can do to a decrypting buffer: let a source write any
bytes into the free space and report any count, where zero is the end of the
ciphertext, or have any amount of the pending plaintext read out. -/
inductive DecOp
  | read (data : Slice U8) (n : Usize)
  | drain (n : Usize)

/-- One operation, with the plaintext read out and the ciphertext accepted so far.
Ciphertext is only accepted once the pending plaintext is drained, and not after
the final chunk or a failure, as `DecryptRead` does. -/
def decStep (st : DecryptBuffer A) (buf : Slice U8) (out ct : List U8) :
    DecOp → Result (DecryptBuffer A × Slice U8 × List U8 × List U8)
  | .drain n => do
    let p ← DecryptBuffer.pending inst st buf
    let st' ← DecryptBuffer.advance inst st n
    ok (st', buf, out ++ p.val.take n.val, ct)
  | .read data n => do
    let d ← DecryptBuffer.is_drained inst st
    let f ← DecryptBuffer.failed inst st
    let dn ← DecryptBuffer.is_done inst st
    if d && f.isNone && !dn then
      let sb ← DecryptBuffer.space inst st buf
      if data.length = sb.1.length then
        if n = 0#usize then
          let res ← DecryptBuffer.open inst st (sb.2 data)
          ok (res.2.1, res.2.2, out, ct)
        else
          let fr ← DecryptBuffer.impl.filled inst st n
          if fr.1 then
            let res ← DecryptBuffer.open inst fr.2 (sb.2 data)
            ok (res.2.1, res.2.2, out, ct ++ data.val.take n.val)
          else ok (fr.2, sb.2 data, out, ct ++ data.val.take n.val)
      else ok (st, buf, out, ct)
    else ok (st, buf, out, ct)

def runDec (st : DecryptBuffer A) (buf : Slice U8) (out ct : List U8) :
    List DecOp → Result (DecryptBuffer A × Slice U8 × List U8 × List U8)
  | [] => ok (st, buf, out, ct)
  | op :: ops => do
    let x ← decStep inst st buf out ct op
    runDec x.1 x.2.1 x.2.2.1 x.2.2.2 ops

theorem decStep_spec {dec0 : Decryptor A} {st : DecryptBuffer A} {buf : Slice U8}
    {out ct : List U8} (h : DecState inst dec0 st buf out ct)
    (hA : AeadTotal inst dec0.cipher.aead) (op : DecOp) :
    decStep inst st buf out ct op ⦃ x => DecState inst dec0 x.1 x.2.1 x.2.2.1 x.2.2.2 ⦄ := by
  have hb : buf.length = 16400 ∧ st.pos.val ≤ st.end.val ∧ st.end.val ≤ 16400 := by
    rcases h with ⟨hbl, -, -, -, -, hpe, hend, -⟩ | ⟨hbl, -, -, hpe, hend, -⟩ |
      ⟨hbl, hend, -, -, -, hpe, -⟩
    · exact ⟨hbl, hpe, hend⟩
    · exact ⟨hbl, hpe, hend⟩
    · exact ⟨hbl, by rw [hpe], hend⟩
  obtain ⟨hbl, hpe, hend⟩ := hb
  cases op with
  | drain n =>
    unfold decStep
    have hp := pendingD_spec inst st buf hpe (by omega)
    step as ⟨p, hpv⟩
    apply WP.spec_bind (DecState_advance inst h n)
    intro st' h'
    simp only [WP.spec_ok]
    have hplen : (pendD st buf).length = st.end.val - st.pos.val := by
      simp only [pendD, List.slice, List.length_take, List.length_drop]
      simp only [Slice.length] at hbl; omega
    have hk : p.val.take n.val = (pendD st buf).take (min n.val (st.end.val - st.pos.val)) := by
      rw [hpv, ← hplen]
      rcases Nat.le_total n.val (pendD st buf).length with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right hle, List.take_of_length_le hle, List.take_length]
    rw [hk]; exact h'
  | read data n =>
    unfold decStep
    simp only [DecryptBuffer.is_drained, DecryptBuffer.failed, DecryptBuffer.is_done,
      Decryptor.is_done, Decryptor.impl.failed, core.option.Option.as_ref, bind_ok]
    rcases h with h | h | h
    · have h0 := h
      obtain ⟨-, -, hf, hdn, -, -, -, hfl, -⟩ := h0
      by_cases hd : st.pos = st.end
      · simp only [hd, hf, hdn, decide_true, Option.isNone_none, Bool.not_false, Bool.and_self,
          ite_true]
        apply WP.spec_bind (DecryptBuffer.space_spec inst st buf hfl hbl)
        rintro ⟨s, back⟩ ⟨hsl, hback⟩
        by_cases hl : data.length = s.length
        · simp only [hl, ite_true]
          have hdl : data.val.length = 16400 - st.filled.val := by
            have := hl; simp only [Slice.length] at this hsl ⊢; omega
          have hb1 : (back data).length = 16400 := by
            simp only [Slice.length]; rw [hback, List.length_setSlice!]; exact hbl
          have hkeep : (back data).val.take st.filled.val = buf.val.take st.filled.val := by
            rw [hback, take_setSlice_prefix _ _ _ (by simp only [Slice.length] at hbl; omega)]
          have h1 := DecInv_frame inst h hd hb1 hkeep
          by_cases hn0 : n = 0#usize
          · simp only [hn0, ite_true]
            apply WP.spec_bind (DecInv_open inst h1 hA hd)
            rintro ⟨r, st', buf'⟩ ⟨hok, herr⟩
            simp only [WP.spec_ok]
            cases r with
            | Ok u => rcases hok rfl with h2 | h2
                      · exact Or.inl h2
                      · exact Or.inr (Or.inl h2)
            | Err e => exact Or.inr (Or.inr (herr e rfl))
          · simp only [hn0, ite_false]
            apply WP.spec_bind (DecInv_filled inst h1 hd n)
            rintro ⟨full, st'⟩ ⟨hfull, hd', h2⟩
            have hsl2 : (back data).val.slice st.filled.val
                (st.filled.val + min n.val (16400 - st.filled.val)) = data.val.take n.val := by
              rw [← take_slice _ _ _ (st.filled.val + data.val.length) (by omega), hback,
                slice_setSlice _ _ _ (by simp only [Slice.length] at hbl; omega)]
              rcases Nat.le_total n.val data.val.length with hle | hle
              · rw [Nat.min_eq_left (by omega)]
              · rw [Nat.min_eq_right (by omega), ← hdl, List.take_of_length_le hle,
                  List.take_length]
            rw [hsl2] at h2
            cases full with
            | true =>
              simp only [ite_true]
              apply WP.spec_bind (DecInv_open inst h2 hA hd')
              rintro ⟨r, st'', buf''⟩ ⟨hok, herr⟩
              simp only [WP.spec_ok]
              cases r with
              | Ok u => rcases hok rfl with h3 | h3
                        · exact Or.inl h3
                        · exact Or.inr (Or.inl h3)
              | Err e => exact Or.inr (Or.inr (herr e rfl))
            | false =>
              simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
              exact Or.inl h2
        · simp only [hl, ite_false, WP.spec_ok]; exact Or.inl h
      · simp only [hd, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, WP.spec_ok]
        exact Or.inl h
    · have h0 := h
      obtain ⟨-, hdn, -⟩ := h0
      simp only [hdn, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, WP.spec_ok]
      exact Or.inr (Or.inl h)
    · have h0 := h
      obtain ⟨-, -, -, e, hf, -⟩ := h0
      simp only [hf, Option.isNone_some, Bool.and_false, Bool.false_and, Bool.false_eq_true,
        ite_false, WP.spec_ok]
      exact Or.inr (Or.inr h)

theorem runDec_spec {dec0 : Decryptor A} (hA : AeadTotal inst dec0.cipher.aead)
    (ops : List DecOp) : ∀ {st : DecryptBuffer A} {buf : Slice U8} {out ct : List U8},
    DecState inst dec0 st buf out ct →
    runDec inst st buf out ct ops ⦃ x => DecState inst dec0 x.1 x.2.1 x.2.2.1 x.2.2.2 ⦄ := by
  induction ops with
  | nil => intro st buf out ct h; simpa [runDec] using h
  | cons op ops ih =>
    intro st buf out ct h
    unfold runDec
    exact WP.spec_bind (decStep_spec inst h hA op) (fun x hx => ih hx)

def streamDecrypt (dec0 : Decryptor A) (buf : Slice U8) (ops : List DecOp) :
    Result (DecryptBuffer A × Slice U8 × List U8 × List U8) := do
  let st ← DecryptBuffer.new inst dec0
  runDec inst st buf [] [] ops

/-- Streaming decryption agrees with one-shot decryption of the ciphertext it
accepted, whatever the sequence of reads and drains: once the final chunk is
authenticated and its plaintext read out, the plaintext read out is the one-shot
plaintext, and if it fails, one-shot decryption fails with the same error. -/
theorem streamDecrypt_spec (dec0 : Decryptor A) (hA : AeadTotal inst dec0.cipher.aead)
    (hf : dec0.failed = none) (hdn : dec0.done = false) (hn : dec0.next.val < 2 ^ 38)
    (buf : Slice U8) (hbuf : buf.length = 16400) (ops : List DecOp) :
    streamDecrypt inst dec0 buf ops ⦃ x =>
      (x.1.dec.done = true → x.1.pos = x.1.end →
        decryptFrom inst dec0 x.2.2.2 = ok (.Ok x.2.2.1)) ∧
      (∀ e, x.1.dec.failed = some e → decryptFrom inst dec0 x.2.2.2 = ok (.Err e)) ⦄ := by
  unfold streamDecrypt
  apply WP.spec_bind (DecryptBuffer.new_spec inst dec0 buf hbuf hf hdn hn)
  intro st h0
  apply WP.spec_mono (runDec_spec inst hA ops (Or.inl h0))
  rintro ⟨st', buf', out, ct⟩ hst
  simp only
  rcases hst with h | h | h
  · obtain ⟨-, -, hf', hdn', -⟩ := h
    refine ⟨fun hd => ?_, fun e he => ?_⟩
    · rw [hdn'] at hd; cases hd
    · rw [hf'] at he; cases he
  · obtain ⟨-, -, hf', -, -, pt, hpt, hout⟩ := h
    refine ⟨fun _ hd => ?_, fun e he => ?_⟩
    · have h0 : st'.end.val - st'.pos.val = 0 := by rw [hd]; simp
      have : out = pt := by simpa [pendD, List.slice, h0] using hout
      rw [hpt, this]
    · rw [hf'] at he; cases he
  · obtain ⟨-, -, hdn', e, hf', -, hct⟩ := h
    refine ⟨fun hd => ?_, fun e' he' => ?_⟩
    · rw [hdn'] at hd; cases hd
    · rw [hf'] at he'; cases he'; exact hct

end cobblestone.buffer

namespace cobblestone

open header raw buffer

variable {M A C : Type} (macI : Mac M) (initI : AeadInit A) (ctI : CtEq C)
  {hmac : List U8 → List U8 → Std.Array U8 64#usize} {st : M → List U8 × List U8}

/-- `EncryptWrite` and `EncryptRead`, started from a new header, produce exactly
the one-shot encryption of the plaintext they accepted. -/
theorem streamEncrypt_eq_encryptMsg (hM : MacLaws macI hmac st) (hI : AeadInitLaws initI)
    (hA : ∀ a, AeadTotal initI.rawChunkAeadInst a) (suite : Suite) (key : Slice U8)
    (hk : key.length = suiteKeyLen suite) (salt : Std.Array U8 24#usize) (context : Slice U8)
    (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize) (buf : Slice U8)
    (hbuf : buf.length = 16400) (ops : List EncOp) (drains : List Usize) :
    (do
      let r ← new_header macI initI suite key salt context okm t
      streamEncrypt initI.rawChunkAeadInst r.1.2 buf r.1.1.to_slice ops drains) ⦃ o =>
      ∀ out acc, o = some (out, acc, true) →
        encryptMsg macI initI suite key salt context okm t acc = ok (.Ok out) ⦄ := by
  obtain ⟨⟨he, okm1, t1⟩, hnh, cm, -, -, hnext, hfin⟩ :=
    spec_ok_eq (new_header_spec hM hI suite key salt context okm t hk)
  rw [hnh, bind_ok]
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
    (do
      let dec ← Decryptor.new initI.rawChunkAeadInst cipher
      streamDecrypt initI.rawChunkAeadInst dec buf ops) ⦃ x =>
      (x.1.dec.done = true → x.1.pos = x.1.end →
        decryptMsg macI initI ctI suite key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Ok x.2.2.1)) ∧
      (∀ e, x.1.dec.failed = some e →
        decryptMsg macI initI ctI suite key context okm t (hdr.val ++ x.2.2.2) =
          ok (.Err e)) ⦄ := by
  simp only [Decryptor.new, bind_ok]
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
