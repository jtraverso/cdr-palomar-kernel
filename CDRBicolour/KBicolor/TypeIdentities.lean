/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Monitored

/-!
# The linear identities of type counts

For a decomposition `D` of the complete `k`-class host into bicoloured triangles, with
`n_XY = kTypeCount lab D X Y`:

* `typeCount_pair`: `2 (n_XY + n_YX) = c_X c_Y` for `X ≠ Y`;
* `typeCount_row`: `2 Σ_{Y ≠ X} n_XY = c_X (c_X − 1)`.

Proof: every ordered pair `(u, v)`, `u ≠ v`, lies in exactly one block (`pairs_sum`); a block of
type `AAB` contains `cnt_X · cnt_Y` ordered pairs of labels `(X, Y)` (minus the diagonal when
`X = Y`), with `cnt_A = 2`, `cnt_B = 1`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- Points of class `X` in a block. -/
def cnt (lab : V → Fin k) (X : Fin k) (T : Finset V) : ℕ := #(T.filter fun v => lab v = X)

/-- Ordered pairs of distinct points with labels `(X, Y)`. -/
def opairs (lab : V → Fin k) (X Y : Fin k) (S : Finset V) : Finset (V × V) :=
  S.offDiag.filter fun p => (lab p.1, lab p.2) = (X, Y)

theorem pairs_sum (lab : V → Fin k) {D : Finset (Finset V)}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) (X Y : Fin k) :
    ∑ T ∈ D, #(opairs lab X Y T) = #(opairs lab X Y univ) := by
  have hset : opairs lab X Y univ = D.biUnion (opairs lab X Y) := by
    ext ⟨u, v⟩
    simp only [opairs, mem_filter, mem_offDiag, mem_univ, true_and, mem_biUnion]
    constructor
    · rintro ⟨huv, hl⟩
      have he0 : s(u, v) ∈ edges (kHost lab) := mem_edges_kHost lab huv
      have he := (Finset.ext_iff.1 hD.2.2 s(u, v)).2 he0
      simp only [Finset.mem_biUnion] at he
      obtain ⟨T, hT, he⟩ := he
      simp only [triEdges, mem_filter, mk_mem_sym2_iff] at he
      exact ⟨T, hT, ⟨he.1.1, he.1.2, huv⟩, hl⟩
    · rintro ⟨T, -, ⟨-, -, huv⟩, hl⟩
      exact ⟨huv, hl⟩
  rw [hset, card_biUnion]
  intro T hT T' hT' hne
  rw [Function.onFun, disjoint_left]
  rintro ⟨u, v⟩ h1 h2
  simp only [opairs, mem_filter, mem_offDiag] at h1 h2
  have e1 : s(u, v) ∈ triEdges T := by
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨h1.1.1, h1.1.2.1⟩, h1.1.2.2⟩
  have e2 : s(u, v) ∈ triEdges T' := by
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨h2.1.1, h2.1.2.1⟩, h2.1.2.2⟩
  exact disjoint_left.mp (hD.2.1 hT hT' hne) e1 e2

theorem card_opairs_ne (lab : V → Fin k) {X Y : Fin k} (h : X ≠ Y) (S : Finset V) :
    #(opairs lab X Y S) = cnt lab X S * cnt lab Y S := by
  rw [cnt, cnt, ← card_product]
  congr 1
  ext ⟨u, v⟩
  simp only [opairs, mem_filter, mem_offDiag, mem_product, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hu, hv, -⟩, h1, h2⟩; exact ⟨⟨hu, h1⟩, ⟨hv, h2⟩⟩
  · rintro ⟨⟨hu, h1⟩, ⟨hv, h2⟩⟩
    exact ⟨⟨hu, hv, fun e => h (by rw [← h1, ← h2, e])⟩, h1, h2⟩

theorem card_opairs_eq (lab : V → Fin k) (X : Fin k) (S : Finset V) :
    #(opairs lab X X S) = cnt lab X S * cnt lab X S - cnt lab X S := by
  rw [cnt, ← offDiag_card]
  congr 1
  ext ⟨u, v⟩
  simp only [opairs, mem_filter, mem_offDiag, Prod.mk.injEq]
  tauto

/-- Class counts of a bicoloured block. -/
theorem cnt_of_type (lab : V → Fin k) {T : Finset V} {A B : Fin k}
    (hm : T.val.map lab = {A, A, B}) (hAB : A ≠ B) (X : Fin k) :
    cnt lab X T = (if X = A then 2 else 0) + (if X = B then 1 else 0) := by
  rw [cnt, ← count_lab, hm]
  by_cases hA : X = A
  · subst hA; simp [hAB]
  · by_cases hB : X = B
    · subst hB; simp [Ne.symm hAB]
    · simp [hA, hB]

theorem type_of_allowed (lab : V → Fin k) {T : Finset V}
    (hT : IsAllowed (kHost lab) (bicF k) T) : ∃ A B, A ≠ B ∧ T.val.map lab = {A, A, B} := by
  obtain ⟨A, B, hAB, hm⟩ := bicF_cases hT.2.2
  exact ⟨A, B, hAB, hm⟩

theorem ind_type (lab : V → Fin k) {T : Finset V} {A B X Y : Fin k}
    (hm : T.val.map lab = {A, A, B}) (hAB : A ≠ B) (hXY : X ≠ Y) :
    (if T.val.map lab = {X, X, Y} then 1 else 0) = (if X = A ∧ Y = B then 1 else 0) := by
  rw [hm]
  by_cases h : X = A ∧ Y = B
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg (fun e => h (by
      obtain ⟨h1, h2⟩ := xxy_inj hAB hXY e; exact ⟨h1.symm, h2.symm⟩))]

/-- **Pair identity.** -/
theorem typeCount_pair (lab : V → Fin k) {D : Finset (Finset V)}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) {X Y : Fin k}
    (hXY : X ≠ Y) :
    2 * (kTypeCount lab D X Y + kTypeCount lab D Y X) = ksz lab X * ksz lab Y := by
  have h1 := pairs_sum lab hD X Y
  have hall : #(opairs lab X Y univ) = ksz lab X * ksz lab Y := by
    rw [card_opairs_ne lab hXY]; rfl
  have hT : ∀ T ∈ D, #(opairs lab X Y T) =
      2 * ((if T.val.map lab = {X, X, Y} then 1 else 0) +
        (if T.val.map lab = {Y, Y, X} then 1 else 0)) := by
    intro T hTD
    obtain ⟨A, B, hAB, hm⟩ := type_of_allowed lab (hD.1 T hTD)
    rw [card_opairs_ne lab hXY, cnt_of_type lab hm hAB, cnt_of_type lab hm hAB,
      ind_type lab hm hAB hXY, ind_type lab hm hAB (Ne.symm hXY)]
    by_cases h1 : X = A <;> by_cases h2 : Y = B <;> by_cases h3 : X = B <;>
      by_cases h4 : Y = A <;> simp_all
  rw [sum_congr rfl hT, ← mul_sum, sum_add_distrib, sum_boole, sum_boole, hall] at h1
  unfold kTypeCount
  simpa using h1

/-- **Row identity.** -/
theorem typeCount_row (lab : V → Fin k) {D : Finset (Finset V)}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) (X : Fin k) :
    2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), kTypeCount lab D X Y =
      ksz lab X * (ksz lab X - 1) := by
  have h1 := pairs_sum lab hD X X
  have hall : #(opairs lab X X univ) = ksz lab X * (ksz lab X - 1) := by
    rw [card_opairs_eq, Nat.mul_sub_one]; rfl
  have hT : ∀ T ∈ D, #(opairs lab X X T) =
      2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), (if T.val.map lab = {X, X, Y} then 1 else 0) := by
    intro T hTD
    obtain ⟨A, B, hAB, hm⟩ := type_of_allowed lab (hD.1 T hTD)
    have hs : ∑ Y ∈ univ.filter (fun Y => Y ≠ X), (if T.val.map lab = {X, X, Y} then 1 else 0) =
        if X = A then 1 else 0 := by
      rw [sum_congr rfl fun Y hY => ind_type lab hm hAB (Ne.symm (mem_filter.1 hY).2)]
      by_cases hXA : X = A
      · subst hXA
        rw [if_pos rfl, sum_eq_single B]
        · simp
        · intro b _ hb; simp [hb]
        · intro hB; simp_all
      · rw [if_neg hXA]
        exact sum_eq_zero fun Y _ => by simp [hXA]
    rw [hs, card_opairs_eq, cnt_of_type lab hm hAB]
    by_cases h1 : X = A <;> by_cases h2 : X = B <;> simp_all
  rw [sum_congr rfl hT, ← mul_sum, sum_comm, hall] at h1
  unfold kTypeCount
  rw [← h1]
  congr 1
  refine sum_congr rfl fun Y _ => ?_
  rw [sum_boole]
  simp

end CDRBicolour.KBicolor
