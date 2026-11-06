/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.CCb

/-!
# Chen–Cao Theorem 1.3 (variant), assuming the kite lemmas

`overfull_of_kites`: a `Δ`-critical graph with `3n + 7δ ≤ 4Δ + 10` is overfull, given `Kite0Prop`
and `BroomProp`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace MainSetupCC

variable {c : PEC G (Fin G.maxDegree)} {a b cc : V} {k : ℕ} {β : Fin G.maxDegree}
  (S : MainSetupCC G c a b cc k β)
include S

open Classical in
theorem card_A : #(univ.filter fun θ => InA c a b θ) + k = G.maxDegree + 2 := by
  have h1 := S.cm.card_nonA S.crit.2.1
  have h2 := S.cm.card_missing_end (Or.inl rfl)
  have h3 := S.cm.card_missing_end (Or.inr rfl)
  have hk := S.nonA_eq
  have hΔ := S.kΔ
  rw [S.da] at h2
  rw [S.db] at h3
  have hu : (univ.filter fun θ => InA c a b θ) ∪ nonA c a b = univ := by
    ext θ; simp only [mem_union, mem_filter, mem_univ, true_and, mem_nonA, iff_true]; tauto
  have hd : Disjoint (univ.filter fun θ => InA c a b θ) (nonA c a b) :=
    disjoint_left.2 fun θ h1 h2 => (mem_nonA.1 h2) (mem_filter.1 h1).2
  have := card_union_of_disjoint hd
  rw [hu, card_univ, Fintype.card_fin] at this
  omega

open Classical in
/-- Two colours of `A` that are not missing at `t`. -/
theorem two_not_free {t : V} (hta : t ≠ a) (htb : t ≠ b) :
    ∃ α₁ α₂, α₁ ≠ α₂ ∧ InA c a b α₁ ∧ InA c a b α₂ ∧ ¬ c.IsFree t α₁ ∧ ¬ c.IsFree t α₂ := by
  have hA := S.card_A
  have hm := S.cm.card_missing_other hta htb
  have hd := S.hmin t
  have hΔ := S.kΔ
  have hsub : (univ.filter fun θ => InA c a b θ) ⊆
      ((univ.filter fun θ => InA c a b θ).filter fun θ => ¬ c.IsFree t θ) ∪ missing c t := by
    intro θ hθ
    by_cases h : c.IsFree t θ
    · exact mem_union_right _ (mem_missing.2 h)
    · exact mem_union_left _ (mem_filter.2 ⟨hθ, h⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  obtain ⟨α₁, h1, α₂, h2, hne⟩ := one_lt_card.1
    (show 1 < #((univ.filter fun θ => InA c a b θ).filter fun θ => ¬ c.IsFree t θ) by omega)
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  exact ⟨α₁, α₂, hne, h1.1, h2.1, h1.2, h2.2⟩

open Classical in
theorem free_card_ge_one {θ : Fin G.maxDegree} (hA : InA c a b θ) :
    1 ≤ #(univ.filter fun v => c.IsFree v θ) := by
  rcases hA with h | h
  · exact card_pos.2 ⟨a, by simp [h]⟩
  · exact card_pos.2 ⟨b, by simp [h]⟩

/-- A vertex outside `{a, b, t}` missing `θ`, for `θ ∈ A` and suitable parity. -/
theorem other_vertex {θ : Fin G.maxDegree} (hA : InA c a b θ) {t : V}
    (hpar : Even (Fintype.card V) ∧ ¬ c.IsFree t θ ∨ Odd (Fintype.card V) ∧ c.IsFree t θ)
    (hta : t ≠ a) (htb : t ≠ b) : ∃ v, v ≠ a ∧ v ≠ b ∧ v ≠ t ∧ c.IsFree v θ := by
  classical
  have h1 := S.free_card_ge_one hA
  rcases hpar with ⟨he, hnt⟩ | ⟨ho, ht⟩
  · obtain ⟨r, hr⟩ := even_card_free_of_even c he θ
    exact S.exists_other_free hA (by omega) (fun h => absurd h hnt)
  · have hodd : Odd #(univ.filter fun v => c.IsFree v θ) := by
      obtain ⟨r, hr⟩ := even_card_not_free c θ
      obtain ⟨m, hm⟩ := ho
      have := card_free_add_not_free c θ
      exact ⟨m - r, by omega⟩
    have h2 : 2 ≤ #(univ.filter fun v => c.IsFree v θ) := by
      have hsub : ({t, if c.IsFree a θ then a else b} : Finset V) ⊆
          univ.filter fun v => c.IsFree v θ := by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · simpa using ht
        · split_ifs with h
          · simpa using h
          · simpa using hA.resolve_left h
      have hne : t ≠ (if c.IsFree a θ then a else b) := by
        split_ifs
        · exact hta
        · exact htb
      have := card_le_card hsub
      rw [card_insert_of_notMem (by simpa using hne), card_singleton] at this
      exact this
    obtain ⟨r, hr⟩ := hodd
    exact S.exists_other_free hA (by omega) (fun _ => by omega)

end MainSetupCC

end Overfull
