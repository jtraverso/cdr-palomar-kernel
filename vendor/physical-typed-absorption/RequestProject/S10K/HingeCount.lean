/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10.PhysicalAdapter

@[expose] public section

/-!
# V23 / S05 §§2–3: fresh hinge counts

Pure finite counting on the ORIGINAL hinge objects of `SparseEdgeDefs.lean`: a hinge is an
EDGE SET `J` (distinct edge sets are distinct objects; decompositions are not counted).

* `card_le_of_support` : edge sets without loops whose support has exactly `i` vertices and
  contains a fixed set `X` number at most `2^(i choose 2) · n^(i-|X|)`, and none if
  `|X| > i`. (With `X` = the four roots plus `r` forced free vertices, `r = 1, 2, 3`, this is
  the S05 count `2^M n^(i-4-r)`.)
* `card_fresh_ge` : hinges of order `i` whose support avoids a set `Z` of non-root vertices
  number at least `|hinges| − |Z| 2^(i choose 2) n^(i-5)`.
* `fresh_ratio` : the S05 (8) ratio for a hinge query.

No geometric hypothesis is used in this file (H4 enters only through the caller).
-/

open Finset

noncomputable section

namespace S10V23

open TypedTriangle.SparseEdge S10V22

variable {V I : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
omit [DecidableEq V] in
/-- An edge set without loops lies in the edges of its support. -/
lemma subset_triEdges_support [Fintype V] {J : Finset (Sym2 V)} (hJ : ∀ e ∈ J, ¬ e.IsDiag) :
    J ⊆ triEdges (support J) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  have hxy : x ≠ y := fun h => hJ _ he (by simp [h])
  exact mem_triEdges.2 ⟨mem_support_of_mem he (by simp), mem_support_of_mem he (by simp), hxy⟩

/-- Number of `i`-subsets of `V` containing `X`. -/
lemma card_supersets_le (X : Finset V) (i : ℕ) :
    ((univ.powersetCard i).filter (fun S => X ⊆ S)).card ≤
      (Fintype.card V) ^ (i - X.card) := by
  have h1 : ((univ.powersetCard i).filter (fun S => X ⊆ S)).card ≤
      ((univ \ X).powersetCard (i - X.card)).card := by
    refine Finset.card_le_card_of_injOn (fun S => S \ X) ?_ ?_
    · intro S hS
      simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard, subset_univ, true_and] at hS
      simp only [mem_coe, mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff (subset_univ _) (subset_refl _), ?_⟩
      rw [Finset.card_sdiff_of_subset hS.2, hS.1]
    · intro S hS S' hS' heq
      simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard, subset_univ, true_and] at hS hS'
      have : S = (S \ X) ∪ X := (Finset.sdiff_union_of_subset hS.2).symm
      rw [this, show S \ X = S' \ X from heq, Finset.sdiff_union_of_subset hS'.2]
  refine h1.trans ?_
  rw [Finset.card_powersetCard]
  refine (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ?_ _)
  exact (Finset.card_le_card (subset_univ _)).trans (by simp)

/-- **Counting edge sets with a prescribed part of their support.** -/
theorem card_le_of_support (𝓙 : Finset (Finset (Sym2 V))) (X : Finset V) (i : ℕ)
    (hdiag : ∀ J ∈ 𝓙, ∀ e ∈ J, ¬ e.IsDiag) (hcard : ∀ J ∈ 𝓙, (support J).card = i)
    (hX : ∀ J ∈ 𝓙, X ⊆ support J) :
    (𝓙.card : ℝ) ≤ 2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - X.card) := by
  set 𝓢 := (univ.powersetCard i).filter (fun S => X ⊆ S) with h𝓢
  have hsub : 𝓙 ⊆ 𝓢.biUnion (fun S => (triEdges S).powerset) := by
    intro J hJ
    refine Finset.mem_biUnion.2 ⟨support J, ?_, Finset.mem_powerset.2
      (subset_triEdges_support (hdiag J hJ))⟩
    simp [h𝓢, hcard J hJ, hX J hJ]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ S ∈ 𝓢, ((triEdges S).powerset).card = 𝓢.card * 2 ^ (i.choose 2) := by
    rw [Finset.sum_const_nat]
    intro S hS
    rw [Finset.card_powerset, triEdges_eq_edgesOf, card_edgesOf]
    simp only [h𝓢, mem_filter, mem_powersetCard] at hS
    rw [hS.1.2]
  rw [h2] at h1
  have h3 := card_supersets_le X i
  have : (𝓙.card : ℝ) ≤ (𝓢.card : ℝ) * 2 ^ (i.choose 2) := by exact_mod_cast h1
  refine this.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast h3

omit [DecidableEq V] in
/-- No edge set has a support of size `i` containing more than `i` prescribed vertices. -/
lemma card_eq_zero_of_support (𝓙 : Finset (Finset (Sym2 V))) (X : Finset V) (i : ℕ)
    (hcard : ∀ J ∈ 𝓙, (support J).card = i) (hX : ∀ J ∈ 𝓙, X ⊆ support J)
    (hlt : i < X.card) : 𝓙 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun J hJ => ?_
  have := Finset.card_le_card (hX J hJ)
  rw [hcard J hJ] at this
  omega

/-- The four roots lie in the support (restated with the ambient `DecidableEq`). -/
lemma roots_subset_support' {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b) :
    ({u, v, a, b} : Finset V) ⊆ support J := by
  convert hJ.roots_subset_support huv hua hva hub hvb

omit [DecidableEq V] in
/-- Hinges have no loops. -/
lemma hinge_no_diag {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J) : ∀ e ∈ J, ¬ e.IsDiag :=
  fun _ he => not_isDiag_of_mem_edges (hJ.1 he)

/-- Hinges of order `i` with four distinct roots and `W` (disjoint from the roots) inside their
support: at most `2^(i choose 2) n^(i-4-|W|)`. -/
theorem card_hinges_forced {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hab : a ≠ b) (i : ℕ) (W : Finset V) (hW : Disjoint W {u, v, a, b})
    (𝓙 : Finset (Finset (Sym2 V))) (h𝓙 : 𝓙 ⊆ hinges G lab F u v a b i)
    (hWJ : ∀ J ∈ 𝓙, W ⊆ support J) :
    (𝓙.card : ℝ) ≤ 2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - (4 + W.card)) := by
  have hR : ({u, v, a, b} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, hua, hub]),
      Finset.card_insert_of_notMem (by simp [hva, hvb]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have hmem : ∀ J ∈ 𝓙, IsHinge G lab F u v a b J ∧ (support J).card = i := fun J hJ => by
    have := h𝓙 hJ
    simp only [hinges, mem_filter, mem_univ, true_and] at this
    exact this
  have := card_le_of_support 𝓙 ({u, v, a, b} ∪ W) i
    (fun J hJ => hinge_no_diag (hmem J hJ).1) (fun J hJ => (hmem J hJ).2)
    (fun J hJ => Finset.union_subset (roots_subset_support' (hmem J hJ).1 huv hua hva hub hvb)
      (hWJ J hJ))
  rwa [Finset.card_union_of_disjoint hW.symm, hR] at this

/-- **Fresh hinges.** Hinges of order `i` whose support avoids `Z` (disjoint from the roots)
number at least `|hinges| − |Z| · 2^(i choose 2) · n^(i-5)`. -/
theorem card_fresh_ge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hab : a ≠ b) (i : ℕ) (Z : Finset V) (hZ : Disjoint Z {u, v, a, b}) :
    ((hinges G lab F u v a b i).card : ℝ) - Z.card * (2 ^ (i.choose 2) *
        (Fintype.card V : ℝ) ^ (i - 5)) ≤
      (((hinges G lab F u v a b i).filter (fun J => Disjoint (support J) Z)).card : ℝ) := by
  set 𝓗 := hinges G lab F u v a b i
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := 𝓗) (fun J => Disjoint (support J) Z)
  have hbad : 𝓗.filter (fun J => ¬ Disjoint (support J) Z) ⊆
      Z.biUnion (fun z => 𝓗.filter (fun J => z ∈ support J)) := by
    intro J hJ
    simp only [mem_filter] at hJ
    obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 hJ.2
    exact Finset.mem_biUnion.2 ⟨z, hz2, mem_filter.2 ⟨hJ.1, hz1⟩⟩
  have hz : ∀ z ∈ Z, ((𝓗.filter (fun J => z ∈ support J)).card : ℝ) ≤
      2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5) := by
    intro z hzZ
    have hd : Disjoint ({z} : Finset V) {u, v, a, b} :=
      Finset.disjoint_singleton_left.2 (Finset.disjoint_left.1 hZ hzZ)
    have := card_hinges_forced (G := G) (lab := lab) (F := F) huv hua hva hub hvb hab i {z} hd _ (Finset.filter_subset _ _)
      (fun J hJ => Finset.singleton_subset_iff.2 (mem_filter.1 hJ).2)
    simpa using this
  have h1 : ((𝓗.filter (fun J => ¬ Disjoint (support J) Z)).card : ℝ) ≤
      Z.card * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) := by
    have := (Finset.card_le_card hbad).trans Finset.card_biUnion_le
    have h2 : ((𝓗.filter (fun J => ¬ Disjoint (support J) Z)).card : ℝ) ≤
        ∑ z ∈ Z, ((𝓗.filter (fun J => z ∈ support J)).card : ℝ) := by exact_mod_cast this
    refine h2.trans ?_
    have := Finset.sum_le_sum hz
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have h3 : ((𝓗.filter (fun J => Disjoint (support J) Z)).card : ℝ) +
      ((𝓗.filter (fun J => ¬ Disjoint (support J) Z)).card : ℝ) = 𝓗.card := by
    exact_mod_cast hsplit
  linarith

/-- **The S05 (8) ratio for one hinge query.** If a hinge option set `O ⊆ hinges(i)` has
`|O| ≥ (α/2) n^(i-4)` and `K ≥ max 1 (2^(M+1)/α)` with `i ≤ h`, `M = h choose 2`, then a fixed
nonempty `W` disjoint from the roots lies in the support of the chosen hinge with
probability `≤ (K/n)^|W|`. -/
theorem fresh_ratio {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hab : a ≠ b) {i h : ℕ} (hih : i ≤ h) (hi4 : 4 ≤ i) {α K : ℝ} (hα : 0 < α)
    (hK1 : 1 ≤ K) (hK : 2 ^ (h.choose 2 + 1) / α ≤ K) (hn : 0 < (Fintype.card V : ℝ))
    (O : Finset (Finset (Sym2 V))) (hO : O ⊆ hinges G lab F u v a b i)
    (hOc : α / 2 * (Fintype.card V : ℝ) ^ (i - 4) ≤ O.card)
    (W : Finset V) (hW0 : W.Nonempty) (hW : Disjoint W {u, v, a, b}) :
    ((O.filter (fun J => W ⊆ support J)).card : ℝ) ≤
      (K / Fintype.card V) ^ W.card * O.card := by
  set n := (Fintype.card V : ℝ)
  set r := W.card
  have hr : 1 ≤ r := hW0.card_pos
  by_cases hri : i < 4 + r
  · have : O.filter (fun J => W ⊆ support J) = ∅ := by
      refine card_eq_zero_of_support _ ({u, v, a, b} ∪ W) i ?_ ?_ ?_
      · intro J hJ
        have := hO (mem_filter.1 hJ).1
        simp only [hinges, mem_filter, mem_univ, true_and] at this
        exact this.2
      · intro J hJ
        have := hO (mem_filter.1 hJ).1
        simp only [hinges, mem_filter, mem_univ, true_and] at this
        exact Finset.union_subset (roots_subset_support' this.1 huv hua hva hub hvb)
          (mem_filter.1 hJ).2
      · rw [Finset.card_union_of_disjoint hW.symm]
        have : ({u, v, a, b} : Finset V).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [huv, hua, hub]),
            Finset.card_insert_of_notMem (by simp [hva, hvb]),
            Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
        omega
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity
  · push_neg at hri
    have h1 := card_hinges_forced huv hua hva hub hvb hab i W hW _
      ((Finset.filter_subset _ _).trans hO) (fun J hJ => (mem_filter.1 hJ).2)
    refine h1.trans ?_
    have hM : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (h.choose 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
    have hpow : n ^ (i - 4) = n ^ (i - (4 + r)) * n ^ r := by
      rw [← pow_add]; congr 1; omega
    have hKr : K ≤ K ^ r := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ r := pow_le_pow_right₀ hK1 hr
    have hKα : 2 ^ (h.choose 2) * 2 ≤ K ^ r * α := by
      have := (div_le_iff₀ hα).1 hK
      rw [pow_succ] at this
      nlinarith
    calc (2 : ℝ) ^ (i.choose 2) * n ^ (i - (4 + r))
        ≤ 2 ^ (h.choose 2) * n ^ (i - (4 + r)) := by gcongr
      _ = (2 ^ (h.choose 2) * 2) * n ^ (i - (4 + r)) / 2 := by ring
      _ ≤ (K ^ r * α) * n ^ (i - (4 + r)) / 2 := by gcongr
      _ = (K / n) ^ r * (α / 2 * n ^ (i - 4)) := by
          rw [hpow, div_pow]; field_simp
      _ ≤ (K / n) ^ r * O.card := by gcongr

end S10V23
