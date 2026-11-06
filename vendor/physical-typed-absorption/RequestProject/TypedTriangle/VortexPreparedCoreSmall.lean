/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PreparedCoreConstruction
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A prepared core with user-chosen small deletion rate. This is the same
first-entry construction as in PreparedCoreConstruction, with its internal
budget retained in the conclusion. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle
theorem preparedCore_with_small_geometry_of_H3H4 (α τ : ℝ) (h N : ℕ) (hα : 0 < α) (hτ : 0 < τ) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ τ * Fintype.card V ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab
            F (α / 4) h N β := by
  obtain ⟨ε, hε, d, T, nEntry, hT, hentry⟩ :=
    physical_vertex_first_entry_lattice α h hα
  obtain ⟨δ₀, hδ₀, hδ₀half, hbudget₀⟩ := original_geometry_vertex_budget hα h
  obtain ⟨δ₁, hδ₁, hδ₁half, hbudget₁⟩ :=
    original_geometry_vertex_budget (by positivity : 0 < α / 2) h
  let L := d + (d + 1) * Nat.log 2 T
  let η : ℝ := min (min ε δ₀) (min (1 / 2) τ)
  let β : ℝ := min (η / (2 * (L + 1))) δ₁
  have hη : 0 < η := lt_min (lt_min hε hδ₀) (lt_min (by norm_num) hτ)
  have hβ : 0 < β := lt_min (by positivity) hδ₁
  have hηε : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hηhalf : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hητ : η ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hβδ : β ≤ δ₁ := min_le_right _ _
  have hβscale : (L + 1 : ℝ) * β ≤ η / 2 := by
    have hb : β ≤ η / (2 * (L + 1)) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ L + 1 by positivity)
    have heq : (L + 1 : ℝ) * (η / (2 * (L + 1))) = η / 2 := by field_simp
    linarith
  have hβquarter : β ≤ 1 / 4 := by
    have : β ≤ (L + 1 : ℝ) * β := by nlinarith [show (0 : ℝ) ≤ L by positivity]
    linarith
  refine ⟨β, hβ, max nEntry (4 * N + 1), ?_⟩
  intro V I _ H F hn hH3 hH4
  let n := Fintype.card V
  let b := ⌊β * n⌋₊
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hb : (b : ℝ) ≤ β * n := Nat.floor_le (by positivity)
  have hscale : ((L + 1 : ℕ) : ℝ) * b ≤ η * n / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (L + 1 : ℕ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hβscale hn0
    push_cast at h1 ⊢
    nlinarith
  have hentryBudget : (((L + 1) * b : ℕ) : ℝ) ≤ ε * n := by
    push_cast
    have := mul_le_mul_of_nonneg_right hηε hn0
    nlinarith
  obtain ⟨A, hA, hp⟩ := hentry H F ((le_max_left _ _).trans hn) hH3 hH4 b hentryBudget
  letI : DecidableEq (Survivors A) := Classical.decEq _
  have hAR : (A.card : ℝ) ≤ η * n / 2 := by
    have hAN : A.card ≤ (L + 1) * b := hA.trans (Nat.mul_le_mul_right b (Nat.le_succ L))
    have hANR : (A.card : ℝ) ≤ (((L + 1) * b : ℕ) : ℝ) := by exact_mod_cast hAN
    push_cast at hANR hscale
    exact hANR.trans hscale
  have hAquart : (A.card : ℝ) ≤ (n : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hηhalf hn0
    linarith
  have hAτ : (A.card : ℝ) ≤ τ * n := by
    have := mul_le_mul_of_nonneg_right hητ hn0
    nlinarith
  have hAδ : (A.card : ℝ) ≤ δ₀ * n := by
    have := mul_le_mul_of_nonneg_right hηδ hn0
    nlinarith
  obtain ⟨hA3, hA4⟩ := hbudget₀ hn0 hAδ
  have hg := original_geometry_restrictedHost hα.le hH3 hH4 A hA3 hA4
  have hcard := card_survivors_add_card A
  have hcardR : (Fintype.card (Survivors A) : ℝ) + A.card = n := by exact_mod_cast hcard
  have hnA : (Fintype.card (Survivors A) : ℝ) ≤ n := by
    nlinarith [show (0 : ℝ) ≤ A.card by positivity]
  refine ⟨A, hAτ, hg.1, hg.2, ?_⟩
  have hzδ (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β * Fintype.card (Survivors A)) :
      (Z.card : ℝ) ≤ δ₁ * Fintype.card (Survivors A) :=
    hZ.trans (mul_le_mul_of_nonneg_right hβδ (by positivity))
  have hgeom (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β * Fintype.card (Survivors A)) :=
    original_geometry_restrictedHost (by positivity : 0 ≤ α / 2) hg.1 hg.2 Z
      (hbudget₁ (by positivity) (hzδ Z hZ)).1
      (hbudget₁ (by positivity) (hzδ Z hZ)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z hZ
    rw [← restrictedHost_G_eq_dispersal (restrictedHost H A) Z]
    rw [← restrictedHost_lab_eq_dispersal (restrictedHost H A) Z]
    apply (prepared_commonNbrCond_iff _ _ _).mp
    convert (hgeom Z hZ).1 using 1 <;> ring
  · intro Z hZ
    rw [← restrictedHost_G_eq_dispersal (restrictedHost H A) Z]
    rw [← restrictedHost_lab_eq_dispersal (restrictedHost H A) Z]
    apply (prepared_hingeCond_iff _ _ _ _).mp
    convert (hgeom Z hZ).2 using 1 <;> ring
  · intro Z hZ
    have hZquart : (Z.card : ℝ) ≤ (Fintype.card (Survivors A) : ℝ) / 4 := by
      have := mul_le_mul_of_nonneg_right hβquarter
        (show (0 : ℝ) ≤ Fintype.card (Survivors A) by positivity)
      linarith
    have hcardZ := card_survivors_add_card Z
    have hcardZR : (Fintype.card (Survivors Z) : ℝ) + Z.card =
        Fintype.card (Survivors A) := by
      simp only [← Nat.card_eq_fintype_card] at hcardZ ⊢
      exact_mod_cast hcardZ
    have hlarge : 4 * N + 1 ≤ n := (le_max_right _ _).trans hn
    have hlargeR : (4 : ℝ) * N + 1 ≤ n := by exact_mod_cast hlarge
    have horder : (N : ℝ) ≤ Fintype.card (Survivors Z) := by linarith
    have horderN : N ≤ Fintype.card (Survivors Z) := by exact_mod_cast horder
    simpa only [← Nat.card_eq_fintype_card] using horderN
  · intro Z hZ y hy hz
    have hzN : Z.card ≤ b := by
      apply Nat.le_floor
      exact hZ.trans (mul_le_mul_of_nonneg_left hnA hβ.le)
    exact induced_lattice_persistence H F A b hp Z hzN hy hz


#print axioms preparedCore_with_small_geometry_of_H3H4

end TypedTriangle

