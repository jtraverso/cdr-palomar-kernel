/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V39.NativeRows
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V39 §2 — lifting native row potentials from `G − Z` to `G`

`rowField G t e = ∑_i entry_G(i, e) t_i` is `natBᵀ t` extended to EVERY unordered pair `e`
(on native columns it is literally `S07V35.dat (natB G lab F) t e`, `rowField_eq_dat`; off the
native columns it vanishes, `rowField_of_not_ncol`).

`liftPot G Z t` lifts a real native row potential `t` of `J = G − Z` to one of `G`:
* rows of `G` rooted in `Z` get `0`;
* a surviving row `(v, K)` gets `rowSign(v, K) · t(v, K \ Z)` (the sign matching the chosen
  bipartite colourings, §1).

Proved, under the ORIGINAL H3/H4 only, `n ≥ n1Of α`, `|Z| ≤ delOf α h · n`:
* `liftPot_abs_le` — sup bound preserved: `|t i| ≤ L ⇒ |liftPot t j| ≤ L`;
* `liftPot_surv` — on surviving rows the defining condition is a theorem (item 1);
* `lift_dat` — `natB_Gᵀ (liftPot t) = natB_Jᵀ t` on EVERY native column of `J`;
* `rowField_abs_le` — `|natB_Gᵀ t'| ≤ 2 L` on every pair (so on all native columns of `G`);
* `rowField_pairing_zero`, `dat_pairing_zero` — the pairing of `natB_Gᵀ t'` with any actual local
  profile of `G` is zero (V38 `localProfile_natB`).
* `lift_potential` — the summary.

No row-span or extension provider appears among the hypotheses.
-/

open Finset Classical

noncomputable section

namespace S07V39

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open S07V25 S07V36 S07V37

variable {V I : Type*} [Fintype V] {lab : V → I} {F : Set (Multiset I)}

/-- `natBᵀ t` on every unordered pair. -/
def rowField (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (t : NRow G lab F → ℝ)
    (e : Sym2 V) : ℝ :=
  ∑ i, (entry G lab F i.1 e : ℝ) * t i

lemma rowField_eq_dat {G : SimpleGraph V} (t : NRow G lab F → ℝ) (e : NCol G lab F) :
    rowField G lab F t e.1 = S07V35.dat (natB G lab F) t e := rfl

/-- The contribution of the root `x` to the pair `xy`. -/
def endTerm (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (t : NRow G lab F → ℝ)
    (x y : V) : ℝ :=
  if hj : IsNRow G lab F (x, comp G lab F x y) then
    (TypedTriangle.SignedCover.sgn
      (TypedTriangle.ComponentRows.col G lab F (x, comp G lab F x y) y) : ℝ) * t ⟨_, hj⟩
  else 0

variable {G : SimpleGraph V}

lemma abs_sgn_real (b : Bool) : |(TypedTriangle.SignedCover.sgn b : ℝ)| = 1 := by
  cases b <;> simp [TypedTriangle.SignedCover.sgn]

lemma endTerm_abs_le (t : NRow G lab F → ℝ) {L : ℝ} (hL : 0 ≤ L) (ht : ∀ i, |t i| ≤ L)
    (x y : V) : |endTerm G lab F t x y| ≤ L := by
  unfold endTerm
  split_ifs with hj
  · rw [abs_mul, abs_sgn_real, one_mul]; exact ht _
  · simpa using hL

/-- Rows rooted at `x` contribute `endTerm t x y` to the pair `xy`. -/
lemma sum_root (t : NRow G lab F → ℝ) {x y : V} :
    ∑ i : NRow G lab F, (if i.1.1 = x then (entry G lab F i.1 s(x, y) : ℝ) * t i else 0) =
      endTerm G lab F t x y := by
  have hrow : ∀ i : NRow G lab F, i.1.1 = x → y ∈ i.1.2 →
      i.1 = (x, comp G lab F x y) := by
    intro i hx hy
    refine Prod.ext hx ?_
    rw [active_eq_comp i.2.1 hy, hx]
  unfold endTerm
  split_ifs with hj
  · rw [Fintype.sum_eq_single ⟨_, hj⟩]
    · simp only [if_true]
      rw [entry_root, if_pos (S07V38.mem_comp_self' x y)]
    · intro i hi
      split_ifs with hx
      · obtain ⟨⟨r, K⟩, hiK⟩ := i
        simp only at hx
        subst hx
        rw [entry_root]
        split_ifs with hy
        · exact absurd (Subtype.ext (hrow ⟨(r, K), hiK⟩ rfl hy)) hi
        · simp
      · rfl
  · refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hx
    · obtain ⟨⟨r, K⟩, hiK⟩ := i
      simp only at hx
      subst hx
      rw [entry_root]
      split_ifs with hy
      · exact absurd (hrow ⟨(r, K), hiK⟩ rfl hy ▸ hiK) hj
      · simp
    · rfl

/-- **Two-endpoint formula**: `natBᵀ t` on the pair `xy` (`x ≠ y`) is the sum of the
contributions of the two roots. -/
theorem rowField_pair (t : NRow G lab F → ℝ) {x y : V} (hxy : x ≠ y) :
    rowField G lab F t s(x, y) = endTerm G lab F t x y + endTerm G lab F t y x := by
  rw [← sum_root t, ← sum_root (x := y) (y := x) t, ← Finset.sum_add_distrib]
  unfold rowField
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Sym2.eq_swap (a := y)]
  by_cases hx : i.1.1 = x
  · have hy : i.1.1 ≠ y := hx ▸ hxy
    rw [if_pos hx, if_neg hy, add_zero]
  · by_cases hy : i.1.1 = y
    · rw [if_neg hx, if_pos hy, zero_add]
    · rw [if_neg hx, if_neg hy, entry_of_not_mem, Int.cast_zero, zero_mul, add_zero]
      rw [Sym2.mem_iff]; push_neg; exact ⟨hx, hy⟩

/-- `natBᵀ t` vanishes on every pair that is not a native column (in particular on the
diagonal and on host edges in no allowed triangle). -/
theorem rowField_of_not_ncol (t : NRow G lab F → ℝ) {e : Sym2 V} (he : ¬ IsNCol G lab F e) :
    rowField G lab F t e = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h0 : entry G lab F i.1 e = 0
  · rw [h0, Int.cast_zero, zero_mul]
  · obtain ⟨u, hu, rfl⟩ := entry_ne_zero h0
    exact absurd (isNCol_root i hu) he

/-- **Edge bound**: if `|t i| ≤ L` then `|natBᵀ t| ≤ 2 L` on every pair. -/
theorem rowField_abs_le (t : NRow G lab F → ℝ) {L : ℝ} (hL : 0 ≤ L) (ht : ∀ i, |t i| ≤ L)
    (e : Sym2 V) : |rowField G lab F t e| ≤ 2 * L := by
  by_cases he : IsNCol G lab F e
  · obtain ⟨T, -, heT⟩ := he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := (mem_triEdges.1 heT).2.2
      rw [rowField_pair t hxy]
      have h1 := endTerm_abs_le t hL ht x y
      have h2 := endTerm_abs_le t hL ht y x
      calc |endTerm G lab F t x y + endTerm G lab F t y x|
          ≤ |endTerm G lab F t x y| + |endTerm G lab F t y x| := abs_add_le _ _
        _ ≤ 2 * L := by linarith
  · rw [rowField_of_not_ncol t he, abs_zero]; linarith

/-- **Pairing with local profiles is zero** (V38 `localProfile_natB`), for every row potential. -/
theorem rowField_pairing_zero (t : NRow G lab F → ℝ) {x : Sym2 V → ℤ}
    (hx : IsLocalProfile G lab F x) : ∑ e, rowField G lab F t e * (x e : ℝ) = 0 := by
  unfold rowField
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hrow : ∑ e, (entry G lab F i.1 e : ℝ) * (x e : ℝ) = 0 := by
    have h := S07V38.localProfile_natB hx i
    have h2 : ∑ e, (entry G lab F i.1 e : ℝ) * (x e : ℝ) =
        ((∑ e : NCol G lab F, natB G lab F i e * x e.1 : ℤ) : ℝ) := by
      push_cast
      show _ = ∑ e : NCol G lab F, (entry G lab F i.1 e.1 : ℝ) * (x e.1 : ℝ)
      rw [S07V38.sum_ncol (fun e => (entry G lab F i.1 e : ℝ) * (x e : ℝ))]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs with he
      · rfl
      · rw [S07V38.localProfile_supp hx e he, Int.cast_zero, mul_zero]
    rw [h2, h, Int.cast_zero]
  calc ∑ e, (entry G lab F i.1 e : ℝ) * t i * (x e : ℝ)
      = t i * ∑ e, (entry G lab F i.1 e : ℝ) * (x e : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => by ring
    _ = 0 := by rw [hrow, mul_zero]

/-- The same pairing, over the native columns (`dat` form). -/
theorem dat_pairing_zero (t : NRow G lab F → ℝ) {x : Sym2 V → ℤ}
    (hx : IsLocalProfile G lab F x) :
    ∑ e : NCol G lab F, S07V35.dat (natB G lab F) t e * (x e.1 : ℝ) = 0 := by
  rw [← rowField_pairing_zero t hx]
  show ∑ e : NCol G lab F, rowField G lab F t e.1 * (x e.1 : ℝ) = _
  rw [S07V38.sum_ncol (fun e => rowField G lab F t e * (x e : ℝ))]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · rfl
  · rw [rowField_of_not_ncol t he, zero_mul]

/-! ### The lift -/

variable {Z : Finset V}

/-- **The lift of a native row potential of `G − Z` to `G`**: zero on rows rooted in `Z`;
`rowSign · t(v, K \ Z)` on surviving rows. -/
def liftPot (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (Z : Finset V)
    (t : NRow (delG G Z) lab F → ℝ) (j : NRow G lab F) : ℝ :=
  if hj : j.1.1 ∉ Z ∧ IsNRow (delG G Z) lab F (j.1.1, j.1.2 \ Z) then
    (rowSign G lab F Z j.1.1 j.1.2 : ℝ) * t ⟨(j.1.1, j.1.2 \ Z), hj.2⟩
  else 0

/-- Rows rooted in `Z` carry `0`. -/
theorem liftPot_root_mem (t : NRow (delG G Z) lab F → ℝ) {j : NRow G lab F} (hj : j.1.1 ∈ Z) :
    liftPot G lab F Z t j = 0 := by
  unfold liftPot
  rw [dif_neg (fun h => h.1 hj)]

/-- **The sup bound is preserved.** -/
theorem liftPot_abs_le (t : NRow (delG G Z) lab F → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (ht : ∀ i, |t i| ≤ L) (j : NRow G lab F) : |liftPot G lab F Z t j| ≤ L := by
  unfold liftPot
  split_ifs with hj
  · rw [abs_mul, abs_rowSign, one_mul]; exact ht _
  · simpa using hL

/-- **Surviving rows** (item 1): for `v ∉ Z` the row `(v, K \ Z)` is a native row of `G − Z`
and the lift is `rowSign · t(v, K \ Z)`. -/
theorem liftPot_surv {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (t : NRow (delG G Z) lab F → ℝ)
    (j : NRow G lab F) (hv : j.1.1 ∉ Z) :
    ∃ hJ : IsNRow (delG G Z) lab F (j.1.1, j.1.2 \ Z),
      liftPot G lab F Z t j = (rowSign G lab F Z j.1.1 j.1.2 : ℝ) * t ⟨_, hJ⟩ := by
  have hJ : IsNRow (delG G Z) lab F (j.1.1, j.1.2 \ Z) :=
    ⟨(row_survives hα hH3 hH4 hn hZ hv j.2.1).1, (bip_iff hα hH3 hH4 hn hZ hv j.2.1).2 j.2.2⟩
  refine ⟨hJ, ?_⟩
  unfold liftPot
  rw [dif_pos ⟨hv, hJ⟩]

omit [Fintype V] in
/-- Native columns of `G − Z` are native columns of `G`. -/
lemma ncol_of_delG {e : Sym2 V} (he : IsNCol (delG G Z) lab F e) : IsNCol G lab F e := by
  obtain ⟨T, hT, heT⟩ := he
  exact ⟨T, (allowed_delG_iff.1 hT).1, heT⟩

/-- Root contributions match at surviving endpoints. -/
theorem endTerm_lift {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (t : NRow (delG G Z) lab F → ℝ)
    {x y : V} (hx : x ∉ Z) (hy : y ∉ Z) :
    endTerm G lab F (liftPot G lab F Z t) x y = endTerm (delG G Z) lab F t x y := by
  by_cases hG : IsNRow G lab F (x, comp G lab F x y)
  · set K := comp G lab F x y with hKdef
    have hyK : y ∈ K \ Z := Finset.mem_sdiff.2 ⟨S07V38.mem_comp_self' x y, hy⟩
    obtain ⟨-, hJcomp⟩ := row_survives hα hH3 hH4 hn hZ hx hG.1
    have hc : comp (delG G Z) lab F x y = K \ Z := hJcomp y hyK
    obtain ⟨hJ, hlift⟩ := liftPot_surv hα hH3 hH4 hn hZ t ⟨_, hG⟩ hx
    have hsg := sgn_col_delG hα hH3 hH4 hn hZ hx hG y hyK
    have hR : endTerm (delG G Z) lab F t x y =
        (TypedTriangle.SignedCover.sgn
          (TypedTriangle.ComponentRows.col (delG G Z) lab F (x, K \ Z) y) : ℝ) * t ⟨_, hJ⟩ := by
      unfold endTerm
      simp only [hc]
      rw [dif_pos hJ]
    rw [hR]
    unfold endTerm
    rw [dif_pos hG, hlift, hsg]
    push_cast
    ring
  · have hR : ¬ IsNRow (delG G Z) lab F (x, comp (delG G Z) lab F x y) := by
      intro hJ
      obtain ⟨-, K, hK, hKeq⟩ := row_reflects hα hH3 hH4 hn hZ hJ.1
      have hyK : y ∈ K := by
        have : y ∈ comp (delG G Z) lab F x y := S07V38.mem_comp_self' x y
        rw [hKeq] at this
        exact (Finset.mem_sdiff.1 this).1
      have hKc : K = comp G lab F x y := active_eq_comp hK hyK
      apply hG
      rw [← hKc]
      refine ⟨hK, (bip_iff hα hH3 hH4 hn hZ hx hK).1 ?_⟩
      rw [← hKeq]; exact hJ.2
    unfold endTerm
    rw [dif_neg hG, dif_neg hR]

/-- **Item 2: the lift reproduces the row field on every native column of `G − Z`.** -/
theorem lift_rowField {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (t : NRow (delG G Z) lab F → ℝ)
    {e : Sym2 V} (he : IsNCol (delG G Z) lab F e) :
    rowField G lab F (liftPot G lab F Z t) e = rowField (delG G Z) lab F t e := by
  obtain ⟨T, hT, heT⟩ := he
  have hTZ := (allowed_delG_iff.1 hT).2
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hxT, hyT, hxy⟩ := mem_triEdges.1 heT
    rw [rowField_pair _ hxy, rowField_pair _ hxy,
      endTerm_lift hα hH3 hH4 hn hZ t (hTZ x hxT) (hTZ y hyT),
      endTerm_lift hα hH3 hH4 hn hZ t (hTZ y hyT) (hTZ x hxT)]

/-- **Item 2 in `dat` form**: `natB_Gᵀ (liftPot t) = natB_Jᵀ t` on every native column of `J`. -/
theorem lift_dat {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (t : NRow (delG G Z) lab F → ℝ)
    (e : NCol (delG G Z) lab F) :
    S07V35.dat (natB G lab F) (liftPot G lab F Z t) ⟨e.1, ncol_of_delG e.2⟩ =
      S07V35.dat (natB (delG G Z) lab F) t e :=
  lift_rowField hα hH3 hH4 hn hZ t e.2

/-- **Item 2 (summary): lifting real native row potentials.** For every real native row
potential `t` of `J = G − Z` with `|t i| ≤ L`, the lift `t' = liftPot G Z t` satisfies:
`|t'| ≤ L`; `t' = 0` on rows rooted in `Z`; `t' = rowSign · t(v, K \ Z)` on surviving rows;
`natB_Gᵀ t' = natB_Jᵀ t` on EVERY native column of `J`; `|natB_Gᵀ t'| ≤ 2 L` on every native
column of `G`; and `natB_Gᵀ t'` pairs to zero with every actual local profile of `G`. -/
theorem lift_potential {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (t : NRow (delG G Z) lab F → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (ht : ∀ i, |t i| ≤ L) :
    (∀ j, |liftPot G lab F Z t j| ≤ L) ∧
      (∀ j : NRow G lab F, j.1.1 ∈ Z → liftPot G lab F Z t j = 0) ∧
      (∀ j : NRow G lab F, j.1.1 ∉ Z → ∃ hJ : IsNRow (delG G Z) lab F (j.1.1, j.1.2 \ Z),
        liftPot G lab F Z t j = (rowSign G lab F Z j.1.1 j.1.2 : ℝ) * t ⟨_, hJ⟩) ∧
      (∀ e : NCol (delG G Z) lab F,
        S07V35.dat (natB G lab F) (liftPot G lab F Z t) ⟨e.1, ncol_of_delG e.2⟩ =
          S07V35.dat (natB (delG G Z) lab F) t e) ∧
      (∀ e : NCol G lab F, |S07V35.dat (natB G lab F) (liftPot G lab F Z t) e| ≤ 2 * L) ∧
      (∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
        ∑ e : NCol G lab F, S07V35.dat (natB G lab F) (liftPot G lab F Z t) e * (x e.1 : ℝ) = 0) :=
  ⟨liftPot_abs_le t hL ht, fun _ hj => liftPot_root_mem t hj,
    fun j hv => liftPot_surv hα hH3 hH4 hn hZ t j hv, lift_dat hα hH3 hH4 hn hZ t,
    fun e => rowField_abs_le _ hL (liftPot_abs_le t hL ht) e.1,
    fun _ hx => dat_pairing_zero _ hx⟩

end S07V39
