/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Step

/-!
# L181, bounded variants (proved)

Same statements as `L181_NoAnchor` / `L181_Star`, with the global inequality `N ≥ 6ρ` replaced
by the per-row room inequality `|miss j| + 4(m+1) < |C|` (which holds in both stages of the P2
prefix).  With it the clean colours of the completion exist at every step, and the
maximum-matching count of the paper is not needed.
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

universe u

/-- **L181, no-anchor version, bounded rows.** -/
def L181_NoAnchorB : Prop :=
  ∀ (Rw Cl : Type u) [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (m : ℕ),
    ProperOn G.edgeFinset χ →
    (∀ j, Even (miss G χ j).card ∧ 4 ≤ (miss G χ j).card) →
    (∀ v, mult G χ v = m ∨ mult G χ v = m + 2) →
    (∀ j, (miss G χ j).card + 4 * (m + 1) < Fintype.card Cl) →
    ∃ χ' : Sym2 Rw → Cl, ProperOn G.edgeFinset χ' ∧
      (∀ v, mult G χ' v = m ∨ mult G χ' v = m + 2) ∧
      (univ.filter fun v => mult G χ' v = m + 2).card =
        (univ.filter fun v => mult G χ v = m + 2).card ∧
      ∃ M : Rw → Finset (Sym2 Cl), (∀ j, IsPerfectPairing (M j) (miss G χ' j)) ∧ PairDisjoint M

/-- **L181, star version, bounded rows.** -/
def L181_StarB : Prop :=
  ∀ (Rw Cl : Type u) [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (m : ℕ) (w : Cl) (t : Rw → Cl),
    ProperOn G.edgeFinset χ → (∀ e ∈ G.edgeFinset, χ e ≠ w) →
    Function.Injective t → (∀ j, t j ∈ miss G χ j ∧ t j ≠ w) →
    (∀ j, Even (miss G χ j).card ∧ 6 ≤ (miss G χ j).card) →
    (∀ v, v ≠ w → mult G χ v = m ∨ mult G χ v = m + 2) →
    (∀ j, (miss G χ j).card + 4 * (m + 1) < Fintype.card Cl) →
    ∃ χ' : Sym2 Rw → Cl, ProperOn G.edgeFinset χ' ∧ (∀ e ∈ G.edgeFinset, χ' e ≠ w) ∧
      (∀ v, v ≠ w → mult G χ' v = m ∨ mult G χ' v = m + 2) ∧
      (univ.filter fun v => v ≠ w ∧ mult G χ' v = m + 2).card =
        (univ.filter fun v => v ≠ w ∧ mult G χ v = m + 2).card ∧
      ∃ M : Rw → Finset (Sym2 Cl), (∀ j, IsPerfectPairing (M j) (miss G χ' j)) ∧ PairDisjoint M

section Initial

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj]

theorem cover_empty : cover (∅ : Finset (Sym2 Cl)) = ∅ := by simp [cover]

/-- Initial state, no anchor: all rows empty. -/
theorem rowState_noAnchor {χ : Sym2 Rw → Cl} {m : ℕ} (hχ : ProperOn G.edgeFinset χ)
    (hsz : ∀ j, Even (miss G χ j).card ∧ 4 ≤ (miss G χ j).card)
    (htwo : ∀ v, mult G χ v = m ∨ mult G χ v = m + 2) :
    RowState G ∅ m (univ.filter fun v => v ∉ (∅ : Finset Cl) ∧ mult G χ v = m + 2).card 0
      (fun j => (miss G χ j).card) ∅ χ (fun _ => ∅) := by
  refine ⟨⟨hχ, by simp, fun j => isPartialPairing_empty _,
    fun j j' _ => disjoint_empty_left _, fun v _ => htwo v⟩, rfl, by simp, fun j _ => by simp,
    fun j _ => by simp [cover_empty], fun j _ => by simpa [cover_empty] using (hsz j).2,
    fun j => rfl⟩

/-- Initial state, star version: every row holds its star pair `w t_j`. -/
theorem rowState_star {χ : Sym2 Rw → Cl} {m : ℕ} {w : Cl} {t : Rw → Cl}
    (hχ : ProperOn G.edgeFinset χ) (hav : ∀ e ∈ G.edgeFinset, χ e ≠ w)
    (ht : Function.Injective t) (htm : ∀ j, t j ∈ miss G χ j ∧ t j ≠ w)
    (hsz : ∀ j, Even (miss G χ j).card ∧ 6 ≤ (miss G χ j).card)
    (htwo : ∀ v, v ≠ w → mult G χ v = m ∨ mult G χ v = m + 2) :
    RowState G {w} m (univ.filter fun v => v ∉ ({w} : Finset Cl) ∧ mult G χ v = m + 2).card 2
      (fun j => (miss G χ j).card) ∅ χ (fun j => {s(w, t j)}) := by
  have hwm : ∀ j, w ∈ miss G χ j := by
    intro j; rw [mem_miss]; intro e he
    exact hav e (SimpleGraph.incidenceFinset_subset _ _ he)
  have hpp : ∀ j, IsPartialPairing {s(w, t j)} (miss G χ j) := by
    intro j
    refine ⟨?_, ?_, ?_⟩
    · intro e he; rw [mem_singleton] at he; subst he
      rw [Sym2.mk_isDiag_iff]; exact (htm j).2.symm
    · intro e he v hv; rw [mem_singleton] at he; subst he
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hwm j
      · exact (htm j).1
    · intro e he f hf _ _ _
      rw [mem_singleton] at he hf; rw [he, hf]
  have hcov : ∀ j, (cover {s(w, t j)}).card = 2 := by
    intro j; rw [card_cover_eq (hpp j), card_singleton]
  refine ⟨⟨hχ, fun e he h => hav e he (mem_singleton.1 h), hpp, ?_, ?_⟩, rfl, by simp,
    fun j _ => ?_, fun j _ => (hcov j).le, fun j _ => by rw [hcov]; exact (hsz j).2,
    fun j => rfl⟩
  · intro j j' hne
    rw [disjoint_singleton]
    intro h
    exact hne (ht (Sym2.congr_right.1 h))
  · intro v hv; exact htwo v (fun h => hv (mem_singleton.2 h))
  · intro v hv
    rw [mem_singleton] at hv; subst hv
    exact mem_cover.2 ⟨_, mem_singleton_self _, Sym2.mem_mk_left _ _⟩

end Initial

theorem l181_noAnchorB : L181_NoAnchorB.{u} := by
  intro Rw Cl _ _ _ _ G _ χ m hχ hsz htwo hroom
  classical
  obtain ⟨χ', M', hg, hhigh, hperf⟩ := l181_core (W := ∅) (c₀ := 0)
    (fun D χ M j₀ T _ _ _ _ _ => hroom j₀) (fun j => (hsz j).1)
    (rowState_noAnchor hχ hsz htwo)
  refine ⟨χ', hg.proper, fun v => hg.two v (notMem_empty v), ?_, M', hperf, hg.disj⟩
  simpa using hhigh

theorem l181_starB : L181_StarB.{u} := by
  intro Rw Cl _ _ _ _ G _ χ m w t hχ hav ht htm hsz htwo hroom
  classical
  obtain ⟨χ', M', hg, hhigh, hperf⟩ := l181_core (W := {w}) (c₀ := 2)
    (fun D χ M j₀ T _ _ _ _ _ => hroom j₀) (fun j => (hsz j).1)
    (rowState_star hχ hav ht htm hsz htwo)
  refine ⟨χ', hg.proper, fun e he h => hg.avoid e he (mem_singleton.2 h),
    fun v hv => hg.two v (fun h => hv (mem_singleton.1 h)), ?_, M', hperf, hg.disj⟩
  simpa using hhigh

end CDRBicolour.L181
