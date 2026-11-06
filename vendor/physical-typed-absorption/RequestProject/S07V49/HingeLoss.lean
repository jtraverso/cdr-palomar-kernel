/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.CompHinge
public import RequestProject.TypedTriangle.SparseEdgeLattice
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §4 — B-degree and forbidden-vertex losses for ORIGINAL hinges with fixed roots

`good_hinges_ge`: among the original hinges of order `i ≥ 6` for `(u v c₁ c₂)` with free
vertices in `U`, those that use no edge of `B` and avoid a forbidden vertex set `X` (disjoint
from the roots) number at least

  `#{free ⊆ U} − (5 d + |X|) · 2^C(i,2) · n^(i-5)`,

provided `c₁c₂ ∉ B` (the only pair of roots a hinge may use). A `B`-edge of a hinge has an
endpoint `y` outside the roots: if the other endpoint is a root, `y ∈ N_B(root)` (`≤ 4d`
choices, one forced vertex, `≤ 2^C n^(i-5)` hinges each); otherwise both endpoints are forced
(`≤ n d` ordered pairs, `≤ 2^C n^(i-6)` hinges each).
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge S07V24

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- hinges forced through a set `Y` disjoint from the roots -/
lemma card_forced_le {u v c1 c2 : V} (hd : u ≠ v ∧ u ≠ c1 ∧ v ≠ c1 ∧ u ≠ c2 ∧ v ≠ c2 ∧ c1 ≠ c2)
    (i : ℕ) (Y : Finset V) (hY : Disjoint Y {u, v, c1, c2}) :
    (((hinges G lab F u v c1 c2 i).filter fun J => Y ⊆ support J).card : ℝ) ≤
      2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - (4 + Y.card)) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  exact S10V23.card_hinges_forced huv hua hva hub hvb hab i Y hY _ (filter_subset _ _)
    (fun J hJ => (mem_filter.1 hJ).2)

set_option maxHeartbeats 1000000 in
/-- **loss of original hinges using a `B`-edge or a forbidden vertex** -/
theorem good_hinges_ge {u v c1 c2 : V}
    (hd : u ≠ v ∧ u ≠ c1 ∧ v ≠ c1 ∧ u ≠ c2 ∧ v ≠ c2 ∧ c1 ≠ c2)
    (i : ℕ) (hi : 6 ≤ i) (U X : Finset V) (hX : Disjoint X {u, v, c1, c2})
    (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ) (hB : ∀ x, B.degree x ≤ d)
    (hc : ¬ B.Adj c1 c2) :
    (((hinges G lab F u v c1 c2 i).filter fun J => freeV u v c1 c2 J ⊆ U).card : ℝ) -
        (5 * d + X.card) * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) ≤
      ((hinges G lab F u v c1 c2 i).filter fun J => freeV u v c1 c2 J ⊆ U ∧
        (∀ e ∈ J, e ∉ B.edgeSet) ∧ Disjoint (support J) X).card := by
  set n := Fintype.card V with hn
  set H := hinges G lab F u v c1 c2 i with hH
  set R : Finset V := {u, v, c1, c2} with hR
  set K : ℝ := 2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5) with hK
  set K' : ℝ := 2 ^ (i.choose 2) * (n : ℝ) ^ (i - 6) with hK'
  have hKpos : 0 ≤ K := by positivity
  have hK'pos : 0 ≤ K' := by positivity
  have hnK : (n : ℝ) * K' = K := by
    rw [hK, hK']
    have : (n : ℝ) ^ (i - 5) = n * (n : ℝ) ^ (i - 6) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  set A := H.filter fun J => freeV u v c1 c2 J ⊆ U
  set Good := H.filter fun J => freeV u v c1 c2 J ⊆ U ∧ (∀ e ∈ J, e ∉ B.edgeSet) ∧
    Disjoint (support J) X
  set BadX := X.biUnion fun x => H.filter fun J => ({x} : Finset V) ⊆ support J
  set Bad1 := R.biUnion fun x => (B.neighborFinset x \ R).biUnion fun y =>
    H.filter fun J => ({y} : Finset V) ⊆ support J
  set Bad2 := (univ \ R).biUnion fun x => (B.neighborFinset x \ R).biUnion fun y =>
    H.filter fun J => ({x, y} : Finset V) ⊆ support J
  -- covering
  have hcov : A ⊆ Good ∪ BadX ∪ Bad1 ∪ Bad2 := by
    intro J hJA
    have hJH : J ∈ H := (mem_filter.1 hJA).1
    have hfree := (mem_filter.1 hJA).2
    have hJ : IsHinge G lab F u v c1 c2 J := (mem_filter.1 hJH).2.1
    by_cases hgood : (∀ e ∈ J, e ∉ B.edgeSet) ∧ Disjoint (support J) X
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _
        (mem_filter.2 ⟨hJH, hfree, hgood⟩)))
    rw [not_and_or] at hgood
    rcases hgood with hBe | hXs
    · push_neg at hBe
      obtain ⟨e, he, heB⟩ := hBe
      induction e using Sym2.ind with
      | _ x y =>
      obtain ⟨hxy, hx, hy⟩ := hinge_edge_ends hJ he
      have hBxy : B.Adj x y := heB
      by_cases hxR : x ∈ R <;> by_cases hyR : y ∈ R
      · exfalso
        by_cases he12 : s(x, y) = s(c1, c2)
        · rw [Sym2.eq_iff] at he12
          rcases he12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hc hBxy
          · exact hc hBxy.symm
        · exact Finset.disjoint_left.1 hJ.2.1 he
            (mem_triEdges_union_of_roots hxy hxR hyR he12)
      · refine mem_union_left _ (mem_union_right _ ?_)
        refine mem_biUnion.2 ⟨x, hxR, mem_biUnion.2 ⟨y, ?_, mem_filter.2 ⟨hJH, by simpa using hy⟩⟩⟩
        rw [mem_sdiff, SimpleGraph.mem_neighborFinset]; exact ⟨hBxy, hyR⟩
      · refine mem_union_left _ (mem_union_right _ ?_)
        refine mem_biUnion.2 ⟨y, hyR, mem_biUnion.2 ⟨x, ?_, mem_filter.2 ⟨hJH, by simpa using hx⟩⟩⟩
        rw [mem_sdiff, SimpleGraph.mem_neighborFinset]; exact ⟨hBxy.symm, hxR⟩
      · refine mem_union_right _ ?_
        refine mem_biUnion.2 ⟨x, by simpa using hxR, mem_biUnion.2 ⟨y, ?_, mem_filter.2 ⟨hJH, ?_⟩⟩⟩
        · rw [mem_sdiff, SimpleGraph.mem_neighborFinset]; exact ⟨hBxy, hyR⟩
        · intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl; exacts [hx, hy]
    · rw [Finset.not_disjoint_iff] at hXs
      obtain ⟨x, hxs, hxX⟩ := hXs
      exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_biUnion.2 ⟨x, hxX, mem_filter.2 ⟨hJH, by simpa using hxs⟩⟩)))
  -- card bounds
  have hR' : ∀ y, y ∉ R → Disjoint ({y} : Finset V) R := fun y hy =>
    Finset.disjoint_singleton_left.2 hy
  have hsingle : ∀ y, y ∉ R →
      (((H.filter fun J => ({y} : Finset V) ⊆ support J)).card : ℝ) ≤ K := by
    intro y hy
    have := card_forced_le (G := G) (lab := lab) (F := F) hd i {y} (hR' y hy)
    simpa [hK] using this
  have hpair : ∀ x y, x ∉ R → y ∉ R → x ≠ y →
      (((H.filter fun J => ({x, y} : Finset V) ⊆ support J)).card : ℝ) ≤ K' := by
    intro x y hx hy hxy
    have hdj : Disjoint ({x, y} : Finset V) R := by
      rw [Finset.disjoint_left]; intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl; exacts [hx, hy]
    have := card_forced_le (G := G) (lab := lab) (F := F) hd i {x, y} hdj
    rw [card_pair hxy] at this
    have e : i - (4 + 2) = i - 6 := by omega
    rw [e] at this; simpa [hK'] using this
  have hnb : ∀ x, ((B.neighborFinset x \ R).card : ℝ) ≤ d := by
    intro x
    have h1 := card_le_card (sdiff_subset : B.neighborFinset x \ R ⊆ B.neighborFinset x)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
    exact_mod_cast h1.trans (hB x)
  have hBadX : (BadX.card : ℝ) ≤ X.card * K := by
    have h1 : BadX.card ≤ ∑ x ∈ X, (H.filter fun J => ({x} : Finset V) ⊆ support J).card :=
      card_biUnion_le
    have h2 : (BadX.card : ℝ) ≤ ∑ x ∈ X,
        ((H.filter fun J => ({x} : Finset V) ⊆ support J).card : ℝ) := by exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ x ∈ X, ((H.filter fun J => ({x} : Finset V) ⊆ support J).card : ℝ)
        ≤ ∑ _x ∈ X, K := sum_le_sum fun x hx =>
          hsingle x (fun hxR => Finset.disjoint_left.1 hX hx hxR)
      _ = X.card * K := by rw [sum_const, nsmul_eq_mul]
  have hinner : ∀ x, (((B.neighborFinset x \ R).biUnion fun y =>
      H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℝ) ≤ d * K := by
    intro x
    have h1 := card_biUnion_le (s := B.neighborFinset x \ R)
      (t := fun y => H.filter fun J => ({y} : Finset V) ⊆ support J)
    have h2 : ((((B.neighborFinset x \ R).biUnion fun y =>
        H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℕ) : ℝ) ≤
        ∑ y ∈ B.neighborFinset x \ R,
          ((H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℝ) := by exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ y ∈ B.neighborFinset x \ R,
          ((H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℝ)
        ≤ ∑ _y ∈ B.neighborFinset x \ R, K :=
          sum_le_sum fun y hy => hsingle y (mem_sdiff.1 hy).2
      _ = (B.neighborFinset x \ R).card * K := by rw [sum_const, nsmul_eq_mul]
      _ ≤ d * K := mul_le_mul_of_nonneg_right (hnb x) hKpos
  have hBad1 : (Bad1.card : ℝ) ≤ 4 * (d * K) := by
    have h1 := card_biUnion_le (s := R) (t := fun x => (B.neighborFinset x \ R).biUnion
      fun y => H.filter fun J => ({y} : Finset V) ⊆ support J)
    have h2 : (Bad1.card : ℝ) ≤ ∑ x ∈ R, ((((B.neighborFinset x \ R).biUnion
        fun y => H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ x ∈ R, ((((B.neighborFinset x \ R).biUnion
          fun y => H.filter fun J => ({y} : Finset V) ⊆ support J).card : ℕ) : ℝ)
        ≤ ∑ _x ∈ R, (d * K) := sum_le_sum fun x _ => hinner x
      _ = R.card * (d * K) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 4 * (d * K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : R.card ≤ 4 := card_le_four
          exact_mod_cast this
  have hinner2 : ∀ x, x ∉ R → (((B.neighborFinset x \ R).biUnion fun y =>
      H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℝ) ≤ d * K' := by
    intro x hx
    have h1 := card_biUnion_le (s := B.neighborFinset x \ R)
      (t := fun y => H.filter fun J => ({x, y} : Finset V) ⊆ support J)
    have h2 : ((((B.neighborFinset x \ R).biUnion fun y =>
        H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℕ) : ℝ) ≤
        ∑ y ∈ B.neighborFinset x \ R,
          ((H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℝ) := by exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ y ∈ B.neighborFinset x \ R,
          ((H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℝ)
        ≤ ∑ _y ∈ B.neighborFinset x \ R, K' := sum_le_sum fun y hy => by
          rw [mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
          exact hpair x y hx hy.2 hy.1.ne
      _ = (B.neighborFinset x \ R).card * K' := by rw [sum_const, nsmul_eq_mul]
      _ ≤ d * K' := mul_le_mul_of_nonneg_right (hnb x) hK'pos
  have hBad2 : (Bad2.card : ℝ) ≤ d * K := by
    have h1 := card_biUnion_le (s := univ \ R) (t := fun x => (B.neighborFinset x \ R).biUnion
      fun y => H.filter fun J => ({x, y} : Finset V) ⊆ support J)
    have h2 : (Bad2.card : ℝ) ≤ ∑ x ∈ univ \ R, ((((B.neighborFinset x \ R).biUnion
        fun y => H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ x ∈ univ \ R, ((((B.neighborFinset x \ R).biUnion
          fun y => H.filter fun J => ({x, y} : Finset V) ⊆ support J).card : ℕ) : ℝ)
        ≤ ∑ _x ∈ univ \ R, (d * K') :=
          sum_le_sum fun x hx => hinner2 x (mem_sdiff.1 hx).2
      _ = (univ \ R).card * (d * K') := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * (d * K') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (univ \ R).card ≤ n := (card_le_card sdiff_subset).trans (by simp [hn])
          exact_mod_cast this
      _ = d * K := by rw [← hnK]; ring
  have htot := card_le_card hcov
  have hu1 := card_union_le (Good ∪ BadX ∪ Bad1) Bad2
  have hu2 := card_union_le (Good ∪ BadX) Bad1
  have hu3 := card_union_le Good BadX
  have : (A.card : ℝ) ≤ Good.card + BadX.card + Bad1.card + Bad2.card := by
    have : A.card ≤ Good.card + BadX.card + Bad1.card + Bad2.card := by omega
    exact_mod_cast this
  nlinarith

end S07V49
