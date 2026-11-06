/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V31.ModeGluing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Universal terminal absorber on a fixed small vertex set (V31)

Visible V28 `SparseEdge` interface throughout.

* `physSubsets G lab F U`: ALL physical edge subsets of the complete non-diagonal edge set
  `triEdges U` on `U` (subsets whose integer indicator lies in the physical lattice).
* `TerminalSupply G lab F U s D σ`: the V28 robust single-piece supply
  (`RobustAbsorberSupply`) for every NONEMPTY physical subset of `triEdges U`. This is an
  intermediate input (derived elsewhere from H3/H4 by the author's local work); it is NOT a new
  hypothesis of T.
* `universal_terminal_absorber`: constants `ε, n₀` are fixed from `t, s, β` only. For every host
  with `n ≥ n₀`, every `U` with `|U| ≤ t` and every forbidden `B` with `Δ(B) ≤ b ≤ ε n`, there is
  ONE edge set `R`, chosen before the residual, with `R ∩ B = ∅`, `R ∩ triEdges U = ∅`,
  `|R| ≤ s · 2^(t·t)`, `Δ(R) ≤ s · 2^(t·t)`, `R` decomposable, and `R ∪ L` decomposable for EVERY
  physical `L` supported on `U` (including `L = ∅`).

Proof: `simultaneous_absorbers` (V28) applied to the finite subtype of physical subsets, with
forbidden set `B ∪ triEdges U` and local incidence bounded by the number `≤ 2^(t·t)` of
subsets; then `mode_gluing`: the absorber of `L` is activated, all others stay in their empty
modes. The candidate pieces are NOT assumed pairwise disjoint.
-/

open Finset

noncomputable section
open Classical

namespace S07V31

open TypedTriangle.SparseEdge S07V28

variable {V I : Type*} [Fintype V]

/-- All physical edge subsets of the complete non-diagonal edge set on `U`. -/
def physSubsets (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (U : Finset V) :
    Finset (Finset (Sym2 V)) :=
  (triEdges U).powerset.filter (fun P => ind P ∈ lattice G lab F)

/-- **Terminal supply (intermediate input).** The V28 robust single-piece supply, with
absorber size `≤ s` and avoidance budgets `D` (edge degree) and `σ` (vertices), for every
nonempty physical edge subset of `triEdges U`. -/
def TerminalSupply (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (U : Finset V)
    (s D σ : ℕ) : Prop :=
  ∀ P ∈ physSubsets G lab F U, P ≠ ∅ → RobustAbsorberSupply G lab F P s D σ

omit [Fintype V] in
lemma ind_empty : ind (∅ : Finset (Sym2 V)) = 0 := by
  funext e; simp [ind]

omit [Fintype V] in
lemma mem_physSubsets {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {U : Finset V}
    {P : Finset (Sym2 V)} : P ∈ physSubsets G lab F U ↔ P ⊆ triEdges U ∧ ind P ∈ lattice G lab F := by
  simp [physSubsets]

omit [Fintype V] in
lemma empty_mem_physSubsets (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (U : Finset V) : ∅ ∈ physSubsets G lab F U :=
  mem_physSubsets.2 ⟨empty_subset _, by rw [ind_empty]; exact Submodule.zero_mem _⟩

omit [Fintype V] in
lemma card_triEdges_le (U : Finset V) : (triEdges U).card ≤ U.card * U.card := by
  have : triEdges U ⊆ (U ×ˢ U).image (fun p => s(p.1, p.2)) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hx, hy, -⟩ := mem_triEdges.1 he
      exact mem_image.2 ⟨(x, y), mem_product.2 ⟨hx, hy⟩, rfl⟩
  exact (card_le_card this).trans (card_image_le.trans (card_product U U).le)

omit [Fintype V] in
lemma card_physSubsets_le (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    {U : Finset V} {t : ℕ} (hU : U.card ≤ t) : (physSubsets G lab F U).card ≤ 2 ^ (t * t) := by
  refine (card_filter_le _ _).trans ?_
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by norm_num)
    ((card_triEdges_le U).trans (Nat.mul_le_mul hU hU))

lemma support_mono {X Y : Finset (Sym2 V)} (h : X ⊆ Y) : support X ⊆ support Y := by
  intro x hx
  simp only [support, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, h he, hxe⟩

lemma support_triEdges_subset (U : Finset V) : support (triEdges U) ⊆ U := by
  intro x hx
  simp only [support, mem_filter, mem_univ, true_and] at hx
  obtain ⟨e, he, hxe⟩ := hx
  exact mem_of_mem_triEdges he hxe

lemma degIn_triEdges_le (U : Finset V) (v : V) : degIn (triEdges U) v ≤ U.card :=
  (degIn_le_card_support _ v).trans (card_le_card (support_triEdges_subset U))

/-- A physical edge set supported on `U` consists of terminal edges of `U`. -/
lemma subset_triEdges_of_physical {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {U : Finset V} {L : Finset (Sym2 V)} (hL : ind L ∈ lattice G lab F)
    (hLU : support L ⊆ U) : L ⊆ triEdges U := by
  intro e he
  have heG : e ∈ edges G := by
    by_contra h
    have := lattice_le_supportedOn G lab F hL e h
    simp [ind, he] at this
  have hnd := not_isDiag_of_mem_edges heG
  induction e using Sym2.ind with
  | h x y =>
    refine mem_triEdges.2 ⟨hLU (mem_support_of_mem he (Sym2.mem_mk_left x y)),
      hLU (mem_support_of_mem he (Sym2.mem_mk_right x y)), ?_⟩
    rintro rfl
    exact hnd (Sym2.mk_isDiag_iff.2 rfl)

universe u v

/-- **Universal terminal absorber on a fixed small vertex set.** Constants `ε, n₀` are fixed
from `t, s, β` before the host. Given the terminal supply (an intermediate input), one edge set
`R`, chosen before the residual, absorbs EVERY physical residual `L` supported on `U`. -/
theorem universal_terminal_absorber (t s : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
    ∀ {V : Type u} [Fintype V] {I : Type v}
      (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
      (U : Finset V) (B : Finset (Sym2 V)) (b : ℕ),
      n₀ ≤ Fintype.card V → U.card ≤ t →
      (∀ v, degIn B v ≤ b) → (b : ℝ) ≤ ε * Fintype.card V →
      TerminalSupply G lab F U s ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊ →
      ∃ R : Finset (Sym2 V),
        Disjoint R B ∧ Disjoint R (triEdges U) ∧
        R.card ≤ s * 2 ^ (t * t) ∧ (∀ v, degIn R v ≤ s * 2 ^ (t * t)) ∧
        (∃ D, IsDecomposition G lab F R D) ∧
        ∀ L : Finset (Sym2 V), ind L ∈ lattice G lab F → support L ⊆ U →
          ∃ D, IsDecomposition G lab F (R ∪ L) D := by
  obtain ⟨ε', hε', K, n₀', q, -, hsim⟩ := simultaneous_absorbers.{u, v, u} t s hβ
  refine ⟨ε' / 2, by positivity, n₀' + ⌈2 * ((2 : ℝ) ^ (t * t) + t) / ε'⌉₊, ?_⟩
  intro V _ I G lab F U B b hn hU hB hb hsup
  set n := Fintype.card V with hndef
  let ι := {P // P ∈ physSubsets G lab F U}
  let P : ι → Finset (Sym2 V) := fun i => i.1
  have hcardι : Fintype.card ι ≤ 2 ^ (t * t) := by
    simp only [ι, Fintype.card_coe]
    exact card_physSubsets_le G lab F hU
  have hlarge : 2 * ((2 : ℝ) ^ (t * t) + t) ≤ ε' * n := by
    have h1 : 2 * ((2 : ℝ) ^ (t * t) + t) / ε' ≤ n := by
      have := Nat.le_ceil (2 * ((2 : ℝ) ^ (t * t) + t) / ε')
      have h2 : ((⌈2 * ((2 : ℝ) ^ (t * t) + t) / ε'⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_add_left _ _).trans hn
      linarith
    rw [div_le_iff₀ hε'] at h1; linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (t * t) := by positivity
  have hr : ((2 ^ (t * t) : ℕ) : ℝ) ≤ ε' * n := by push_cast; linarith
  have hb' : ((b + t : ℕ) : ℝ) ≤ ε' * n := by push_cast; linarith
  have hk : ∀ i, (support (P i)).card ≤ t := fun i =>
    (card_le_card ((support_mono (mem_physSubsets.1 i.2).1).trans
      (support_triEdges_subset U))).trans hU
  have hinc : ∀ v, rootInc P v ≤ 2 ^ (t * t) := fun v =>
    (card_filter_le _ _).trans (by rw [card_univ]; exact hcardι)
  have hB' : ∀ v, degIn (B ∪ triEdges U) v ≤ b + t := fun v =>
    (degIn_union_le _ _ v).trans (Nat.add_le_add (hB v) ((degIn_triEdges_le U v).trans hU))
  have hsup' : ∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s ⌊β * n⌋₊ ⌊β * n⌋₊ :=
    fun i hi => hsup i.1 i.2 hi
  obtain ⟨A, -, habs, hdisj, hAB, hAP, hcard, -, -⟩ :=
    hsim G lab F P (B ∪ triEdges U) (2 ^ (t * t)) (b + t)
      ((Nat.le_add_right _ _).trans hn) hr hb' hk hinc hB' hsup'
  have hRcard : (univ.biUnion A).card ≤ s * 2 ^ (t * t) := by
    refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ s (fun i _ => hcard i)).trans ?_)
    rw [smul_eq_mul, card_univ, mul_comm]
    exact Nat.mul_le_mul_left s hcardι
  have hglue : ∀ L, L ∈ physSubsets G lab F U →
      ∃ D, IsDecomposition G lab F (univ.biUnion A ∪ L) D := fun L hL =>
    mode_gluing P A habs hdisj ⟨L, hL⟩ (fun j => hAP j ⟨L, hL⟩)
  refine ⟨univ.biUnion A, ?_, ?_, hRcard, fun v => (degIn_le_card _ v).trans hRcard, ?_, ?_⟩
  · exact (disjoint_biUnion_left _ _ _).2 fun i _ => (hAB i).mono_right subset_union_left
  · exact (disjoint_biUnion_left _ _ _).2 fun i _ => (hAB i).mono_right subset_union_right
  · simpa using hglue ∅ (empty_mem_physSubsets G lab F U)
  · intro L hL hLU
    exact hglue L (mem_physSubsets.2 ⟨subset_triEdges_of_physical hL hLU, hL⟩)

end S07V31
