/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.ExactSeedK
public import CDRIIILib.KBicolor.TypeIdentities

/-!
# The exact type spectrum: correction by copies

* `coord_determines`: two type-count matrices with the same pair and row sums that agree on the
  cycle coordinates (`Y < Z`, both `≠ o`) agree everywhere.
* `diff_coord`: in the copies of the triple `(o, Y', Z')` (`tau3`), switching a copy from `T₀`
  to `T₁` moves the coordinate `(Y, Z)` by `−1` if `(Y, Z) = (Y', Z')` and by `0` otherwise.
* `exact_from_packing`: a residual decomposition whose coordinate counts are within `m²/4` of
  `t − B + m²/2` (`B` the count of the packing with all copies in `T₀`), completed by the
  packing with the right number of copies in `T₁` in each triple, is a k-bicoloured STS with type
  counts exactly `t`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
  CDRBicolour.Absorption.Refined

variable {k : ℕ}

theorem coord_determines (o : Fin k) (n t : Fin k → Fin k → ℕ)
    (hp : ∀ X Y, X ≠ Y → n X Y + n Y X = t X Y + t Y X)
    (hr : ∀ X, ∑ Y ∈ univ.filter (fun Y => Y ≠ X), n X Y =
      ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y)
    (hc : ∀ i : Coord o, n i.1.1 i.1.2 = t i.1.1 i.1.2) :
    ∀ X Y, X ≠ Y → n X Y = t X Y := by
  have h1 : ∀ Y Z, Y ≠ o → Z ≠ o → Y ≠ Z → n Y Z = t Y Z := by
    intro Y Z hY hZ hYZ
    rcases lt_or_gt_of_ne hYZ with h | h
    · exact hc ⟨(Y, Z), h, hY, hZ⟩
    · have h' : n Z Y = t Z Y := hc ⟨(Z, Y), h, hZ, hY⟩
      have := hp Y Z hYZ
      omega
  have h2 : ∀ Y, Y ≠ o → n Y o = t Y o := by
    intro Y hY
    have hmem : o ∈ univ.filter (fun Z => Z ≠ Y) := mem_filter.2 ⟨mem_univ _, Ne.symm hY⟩
    have e1 := add_sum_erase _ (n Y) hmem
    have e2 := add_sum_erase _ (t Y) hmem
    have e3 : ∑ Z ∈ (univ.filter fun Z => Z ≠ Y).erase o, n Y Z =
        ∑ Z ∈ (univ.filter fun Z => Z ≠ Y).erase o, t Y Z :=
      sum_congr rfl fun Z hZ => by
        simp only [mem_erase, mem_filter, mem_univ, true_and] at hZ
        exact h1 Y Z hY hZ.1 (Ne.symm hZ.2)
    have := hr Y
    omega
  intro X Y hXY
  by_cases hX : X = o
  · subst hX
    have := hp X Y hXY
    have := h2 Y (Ne.symm hXY)
    omega
  · by_cases hY : Y = o
    · subst hY; exact h2 X hX
    · exact h1 X Y hX hY hXY

/-- The roles of the triple of a coordinate. -/
def tau3 (o : Fin k) (j : Coord o) : Fin 3 → Fin k := ![o, j.1.1, j.1.2]

theorem tau3_inj (o : Fin k) (j : Coord o) : Function.Injective (tau3 o j) := by
  obtain ⟨⟨Y, Z⟩, hlt, hY, hZ⟩ := j
  simp only at hlt hY hZ
  have h3 : Y ≠ Z := ne_of_lt hlt
  intro a b h
  fin_cases a <;> fin_cases b <;> (try simp [tau3] at h) <;> first | rfl | exact absurd h.symm hY | exact absurd h hY | exact absurd h.symm hZ | exact absurd h hZ | exact absurd h h3 | exact absurd h.symm h3

theorem mcnt_tau3_zero (o : Fin k) {j i : Coord o} (hji : j ≠ i) (S : Finset (Finset (Fin 9))) :
    mcnt (tau3 o j) S i.1.1 i.1.2 = 0 := by
  unfold mcnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro T _ hT
  have hYm : i.1.1 ∈ (T.val.map mcol).map (tau3 o j) := by rw [hT]; simp
  have hZm : i.1.2 ∈ (T.val.map mcol).map (tau3 o j) := by rw [hT]; simp
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hYm
  obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hZm
  apply hji
  obtain ⟨⟨Y, Z⟩, hlt, hY, hZ⟩ := i
  obtain ⟨⟨Y', Z'⟩, hlt', hY', hZ'⟩ := j
  simp only at ha hb hY hZ hlt
  fin_cases a <;> fin_cases b <;> simp [tau3] at ha hb
  all_goals first
    | exact absurd ha.symm hY
    | exact absurd ha hY
    | exact absurd hb.symm hZ
    | exact absurd hb hZ
    | (subst ha; subst hb; exact absurd hlt (lt_irrefl _))
    | (subst ha; subst hb; rfl)
    | (subst ha; subst hb; exact absurd (hlt.trans hlt') (lt_irrefl _))

theorem diff_coord (o : Fin k) (j i : Coord o) :
    (mcnt (tau3 o j) T1m i.1.1 i.1.2 : ℤ) - mcnt (tau3 o j) T0m i.1.1 i.1.2 =
      if j = i then -1 else 0 := by
  by_cases h : j = i
  · subst h
    rw [if_pos rfl]
    have e1 : j.1.1 = tau3 o j 1 := rfl
    have e2 : j.1.2 = tau3 o j 2 := rfl
    rw [e1, e2, mcnt_map (tau3_inj o j), mcnt_map (tau3_inj o j), model_YZ.1, model_YZ.2.1]
    norm_num
  · rw [if_neg h, mcnt_tau3_zero o h, mcnt_tau3_zero o h]; simp

/-! ### Completion by the packing -/

variable {n m : ℕ} (lab : Fin n → Fin k)

/-- The `T₀` count of the packing on a coordinate. -/
def Bn (o : Fin k) [NeZero m] (P : Place lab (Coord o) m) (i : Coord o) : ℕ :=
  ∑ c : Coord o × ZMod m × ZMod m, mcnt (P.τ c.1) T0m i.1.1 i.1.2

theorem allowed_kHost_of_rHostK {L : Finset (Sym2 (Fin n))} {T : Finset (Fin n)}
    (h : IsAllowed (rHostK lab L) (bicF k) T) : IsAllowed (kHost lab) (bicF k) T :=
  ⟨h.1, fun x _ y _ hxy => by simpa [kHost] using hxy, h.2.2⟩

theorem disj_of_rHostK {L : Finset (Sym2 (Fin n))} {T : Finset (Fin n)}
    (h : IsAllowed (rHostK lab L) (bicF k) T) : Disjoint (triEdges T) L :=
  ((gallowed_iff (lab := lab) (F := bicF k) (L := L) (T := T)).1 h).2

/-- **Exact type counts from a close residual decomposition.** -/
theorem exact_from_packing (o : Fin k) [Fact m.Prime] (hm8 : 8 < m)
    (P : Place lab (Coord o) m) (hPτ : P.τ = tau3 o) (D : Finset (Finset (Fin n)))
    (hD : IsDecomposition (rHostK lab (leaveG P)) (bicF k) (edges (rHostK lab (leaveG P))) D)
    (t : Fin k → Fin k → ℕ)
    (hpair : ∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y)
    (hrow : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1))
    (hclose : ∀ i : Coord o, |(kTypeCount lab D i.1.1 i.1.2 : ℝ) -
      ((t i.1.1 i.1.2 : ℝ) - Bn lab o P i + (m : ℝ) ^ 2 / 2)| ≤ (m : ℝ) ^ 2 / 4) :
    ∃ D' : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D' ∧
      ∀ X Y, X ≠ Y → kTypeCount lab D' X Y = t X Y := by
  classical
  set L := leaveG P with hL
  -- the number of copies to switch in each triple
  set N : Coord o → ℤ := fun i =>
    (kTypeCount lab D i.1.1 i.1.2 : ℤ) + Bn lab o P i - t i.1.1 i.1.2 with hN
  have hNb : ∀ i, 0 ≤ N i ∧ N i ≤ (m : ℤ) ^ 2 := by
    intro i
    have h := abs_le.1 (hclose i)
    have hR : (N i : ℝ) = (kTypeCount lab D i.1.1 i.1.2 : ℝ) + Bn lab o P i - t i.1.1 i.1.2 := by
      simp only [hN]; push_cast; ring
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    constructor
    · have : (0 : ℝ) ≤ N i := by rw [hR]; linarith
      exact_mod_cast this
    · have : (N i : ℝ) ≤ (m : ℝ) ^ 2 := by rw [hR]; linarith
      exact_mod_cast this
  have hcardZ : #(univ : Finset (ZMod m × ZMod m)) = m ^ 2 := by
    rw [card_univ, Fintype.card_prod, ZMod.card, sq]
  have hS : ∀ i : Coord o, ∃ S : Finset (ZMod m × ZMod m), #S = (N i).toNat := by
    intro i
    have : (N i).toNat ≤ #(univ : Finset (ZMod m × ZMod m)) := by
      rw [hcardZ]
      have h' : N i ≤ ((m ^ 2 : ℕ) : ℤ) := by push_cast; exact (hNb i).2
      omega
    obtain ⟨S, -, hS⟩ := exists_subset_card_eq this
    exact ⟨S, hS⟩
  choose S hScard using hS
  set σ : Coord o × ZMod m × ZMod m → Bool := fun c => decide (c.2 ∈ S c.1) with hσ
  set Pk := packG P σ with hPk
  have hPkL : Pk.biUnion triEdges = L := packG_leave P σ
  -- the packing and the residual decomposition are disjoint
  have hDdisj : ∀ T ∈ D, Disjoint (triEdges T) L := fun T hT => disj_of_rHostK lab (hD.1 T hT)
  have hPksub : ∀ T ∈ Pk, triEdges T ⊆ L := fun T hT e he => by
    rw [← hPkL]; exact mem_biUnion.2 ⟨T, hT, he⟩
  have hPkne : ∀ T ∈ Pk, (triEdges T).Nonempty := by
    intro T hT
    obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp (packG_allowed P σ T hT).1
    exact ⟨s(x, y), by simp [triEdges, hxy]⟩
  have hDPk : Disjoint D Pk := by
    rw [Finset.disjoint_left]
    intro T hTD hTP
    obtain ⟨e, he⟩ := hPkne T hTP
    exact disjoint_left.mp (hDdisj T hTD) he (hPksub T hTP he)
  -- the union is a decomposition of the complete host
  have hdec : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D ∪ Pk) := by
    refine ⟨fun T hT => ?_, fun T hT T' hT' hne => ?_, ?_⟩
    · rcases mem_union.1 hT with h | h
      · exact allowed_kHost_of_rHostK lab (hD.1 T h)
      · exact packG_allowed P σ T h
    · simp only [coe_union, Set.mem_union, mem_coe] at hT hT'
      rcases hT with h | h <;> rcases hT' with h' | h'
      · exact hD.2.1 h h' hne
      · show Disjoint (triEdges T) (triEdges T')
        exact (hDdisj T h).mono_right (hPksub T' h')
      · show Disjoint (triEdges T) (triEdges T')
        exact ((hDdisj T' h').mono_right (hPksub T h)).symm
      · exact packG_disj P hm8 σ h h' hne
    · ext e
      have hDe := Finset.ext_iff.1 hD.2.2 e
      simp only [Finset.mem_biUnion, mem_union] at hDe ⊢
      constructor
      · rintro ⟨T, hT | hT, he⟩
        · have := hDe.1 ⟨T, hT, he⟩
          have h1 : e ∈ (rG L).edgeSet := by simpa [edges] using this
          simp only [edges, mem_filter, mem_univ, true_and]
          exact SimpleGraph.edgeSet_mono le_top h1
        · have heL : e ∈ L := hPksub T hT he
          induction e using Sym2.ind with
          | _ u v =>
          simp only [edges, mem_filter, mem_univ, true_and, kHost, SimpleGraph.top_adj,
            SimpleGraph.mem_edgeSet]
          have := (packG_allowed P σ T hT)
          simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
          exact he.2
      · intro he
        by_cases heL : e ∈ L
        · rw [← hPkL, mem_biUnion] at heL
          obtain ⟨T, hT, he'⟩ := heL
          exact ⟨T, Or.inr hT, he'⟩
        · obtain ⟨T, hT, he'⟩ := hDe.2 (by
            induction e using Sym2.ind with
            | _ u v =>
            simp only [edges, mem_filter, mem_univ, true_and, kHost, SimpleGraph.top_adj,
              SimpleGraph.mem_edgeSet, rG_adj] at he ⊢
            exact ⟨heL, he⟩)
          exact ⟨T, Or.inl hT, he'⟩
  refine ⟨D ∪ Pk, hdec, ?_⟩
  -- counts of the union
  have hcountU : ∀ X Y, kTypeCount lab (D ∪ Pk) X Y =
      kTypeCount lab D X Y + kTypeCount lab Pk X Y := by
    intro X Y
    unfold kTypeCount
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hDPk)]
  -- coordinates
  have hcoord : ∀ i : Coord o, kTypeCount lab (D ∪ Pk) i.1.1 i.1.2 = t i.1.1 i.1.2 := by
    intro i
    have hPc := packG_count P hm8 σ i.1.1 i.1.2
    have hsw : ∑ c : Coord o × ZMod m × ZMod m, (if σ c then
        ((mcnt (P.τ c.1) T1m i.1.1 i.1.2 : ℤ) - mcnt (P.τ c.1) T0m i.1.1 i.1.2) else 0) =
          -((N i).toNat : ℤ) := by
      rw [Fintype.sum_prod_type]
      have hin : ∀ j : Coord o, ∑ q : ZMod m × ZMod m, (if σ (j, q) then
          ((mcnt (P.τ j) T1m i.1.1 i.1.2 : ℤ) - mcnt (P.τ j) T0m i.1.1 i.1.2) else 0) =
            if j = i then -((S j).card : ℤ) else 0 := by
        intro j
        rw [hPτ, diff_coord o j i]
        by_cases hji : j = i
        · rw [if_pos hji]
          simp only [hσ, decide_eq_true_eq, if_pos hji]
          rw [← sum_filter, sum_const, filter_mem_eq_inter, univ_inter, nsmul_eq_mul, mul_neg,
            mul_one]
        · simp [hji]
      rw [sum_congr rfl fun j _ => hin j, sum_ite_eq', if_pos (mem_univ _), hScard]
    rw [hsw] at hPc
    have hB : (Bn lab o P i : ℤ) = ∑ c : Coord o × ZMod m × ZMod m,
        (mcnt (P.τ c.1) T0m i.1.1 i.1.2 : ℤ) := by unfold Bn; push_cast; rfl
    have hNi : ((N i).toNat : ℤ) = N i := Int.toNat_of_nonneg (hNb i).1
    have : (kTypeCount lab (D ∪ Pk) i.1.1 i.1.2 : ℤ) = t i.1.1 i.1.2 := by
      rw [hcountU]; push_cast; rw [hPc, ← hB, hNi]; simp only [hN]; ring
    exact_mod_cast this
  -- all types, by the linear identities
  refine coord_determines o (fun X Y => kTypeCount lab (D ∪ Pk) X Y) t (fun X Y h => ?_)
    (fun X => ?_) hcoord
  · have h1 := typeCount_pair lab hdec h
    have h2 := hpair X Y h
    show kTypeCount lab (D ∪ Pk) X Y + kTypeCount lab (D ∪ Pk) Y X = t X Y + t Y X
    omega
  · have h1 := typeCount_row lab hdec X
    have h2 := hrow X
    show ∑ Y ∈ univ.filter (fun Y => Y ≠ X), kTypeCount lab (D ∪ Pk) X Y =
      ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y
    omega

end CDRBicolour.KBicolor
