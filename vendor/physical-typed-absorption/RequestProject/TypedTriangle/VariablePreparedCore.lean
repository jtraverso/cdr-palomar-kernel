/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VariableFirstEntry
public import RequestProject.TypedTriangle.PreparedCoreConstruction
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A prepared core at one of finitely many preselected robustness radii.
Earlier extractions pay only earlier radii. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle
theorem preparedCore_at_variable_radius (α τ : ℝ) (h : ℕ)
    (hα : 0 < α) (hτ : 0 < τ) :
    ∃ η δ₁ : ℝ, 0 < η ∧ 0 < δ₁ ∧ ∃ L : ℕ,
      ∀ N : ℕ, ∃ n₀ : ℕ, ∀ β : ℕ → ℝ,
        (∀ j ≤ L, 0 < β j ∧ β j ≤ min (1 / 4) δ₁) →
        ∑ j ∈ range (L + 1), β j ≤ η / 2 →
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
          n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          ∃ r ≤ L, ∃ A : Finset V,
            A.card ≤ priorBudget (fun j => ⌊β j * Fintype.card V⌋₊) r ∧
            (A.card : ℝ) ≤ τ * Fintype.card V ∧
            CommonNbrCond (restrictedHost H A) F (α / 2) ∧
            HingeCond (restrictedHost H A) F (α / 2) h ∧
            Dispersal.PreparedCore (restrictedHost H A).G
              (restrictedHost H A).lab F (α / 4) h N (β r) := by
  obtain ⟨ε, hε, d, T, nEntry, hT, hentry⟩ :=
    physical_vertex_first_entry_lattice_variable α h hα
  obtain ⟨δ₀, hδ₀, hδ₀half, hbudget₀⟩ := original_geometry_vertex_budget hα h
  obtain ⟨δ₁, hδ₁, hδ₁half, hbudget₁⟩ :=
    original_geometry_vertex_budget (by positivity : 0 < α / 2) h
  let L := d + (d + 1) * Nat.log 2 T
  let η : ℝ := min (min ε δ₀) (min (1 / 2) τ)
  have hη : 0 < η := lt_min (lt_min hε hδ₀) (lt_min (by norm_num) hτ)
  have hηε : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hηhalf : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hητ : η ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, δ₁, hη, hδ₁, L, ?_⟩
  intro N
  refine ⟨max nEntry (4 * N + 1), ?_⟩
  intro β hβ hβsum V I _ H F hn hH3 hH4
  let n := Fintype.card V
  let b : ℕ → ℕ := fun j => ⌊β j * n⌋₊
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hfloor (j : ℕ) (hj : j ≤ L) : (b j : ℝ) ≤ β j * n :=
    Nat.floor_le (mul_nonneg (hβ j hj).1.le hn0)
  have hscale : (priorBudget b (L + 1) : ℝ) ≤ η * n / 2 := by
    have hs : (∑ j ∈ range (L + 1), (b j : ℝ)) ≤
        ∑ j ∈ range (L + 1), β j * n := by
      apply sum_le_sum
      intro j hj
      exact hfloor j (Nat.le_of_lt_succ (mem_range.mp hj))
    simp only [← Finset.sum_mul, ← Nat.cast_sum] at hs
    change (priorBudget b (L + 1) : ℝ) ≤
      (∑ j ∈ range (L + 1), β j) * n at hs
    have ht := mul_le_mul_of_nonneg_right hβsum hn0
    nlinarith [hs]
  have hentryBudget : (priorBudget b (L + 1) : ℝ) ≤ ε * n := by
    have ht := mul_le_mul_of_nonneg_right hηε hn0
    nlinarith [hscale]
  obtain ⟨r, hr, A, hA, hp⟩ := hentry H F
    ((le_max_left _ _).trans hn) hH3 hH4 b hentryBudget
  letI : DecidableEq (Survivors A) := Classical.decEq _
  have hAR : (A.card : ℝ) ≤ η * n / 2 := by
    have hAN : A.card ≤ priorBudget b (L + 1) :=
      hA.trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : r ≤ L + 1)) (by simp))
    exact (show (A.card : ℝ) ≤ priorBudget b (L + 1) by
      exact_mod_cast hAN).trans hscale
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
  refine ⟨r, hr, A, hA, hAτ, hg.1, hg.2, ?_⟩
  have hβr : 0 < β r ∧ β r ≤ min (1 / 4) δ₁ := hβ r hr
  have hβδ : β r ≤ δ₁ := hβr.2.trans (min_le_right _ _)
  have hβquarter : β r ≤ 1 / 4 := hβr.2.trans (min_le_left _ _)
  have hzδ (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β r * Fintype.card (Survivors A)) :
      (Z.card : ℝ) ≤ δ₁ * Fintype.card (Survivors A) :=
    hZ.trans (mul_le_mul_of_nonneg_right hβδ (by positivity))
  have hgeom (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β r * Fintype.card (Survivors A)) :=
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
    have hzN : Z.card ≤ b r := by
      apply Nat.le_floor
      exact hZ.trans (mul_le_mul_of_nonneg_left hnA hβr.1.le)
    exact induced_lattice_persistence H F A (b r) hp Z hzN hy hz


#print axioms preparedCore_at_variable_radius

end TypedTriangle

