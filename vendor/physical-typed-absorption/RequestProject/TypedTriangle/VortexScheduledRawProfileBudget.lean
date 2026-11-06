/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalRawProfileBudget
public import RequestProject.TypedTriangle.VortexAnchoredChildInverseBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- One terminal-order threshold pays the genuine finite agenda's reference
precision and inverse budget for every index. No rate bound for an existential
reference threshold is needed: its finite precision list is already fixed. -/
theorem exists_scheduled_raw_profile_budget
    (C E b : ℝ) (β K εRef : ℕ → ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hE : 0 ≤ E) (hEb : E ≤ b)
    (hβ : ∀ j, 0 ≤ β j) (hK : ∀ j ≤ L, 0 < K j)
    (hε : ∀ j ≤ L, 0 < εRef j)
    (hAgenda : ∀ r ≤ L,
      K r * (2 * b * (∑ j ∈ range r, β j)) ≤ 1 / (16 * C) ∧
      2 * b * (∑ j ∈ range r, β j) ≤ εRef r / 8) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ r ≤ L,
      globalRawProfileError 4 E β n r ≤ εRef r ∧
      K r * globalRawProfileError 4 E β n r ≤ 1 / (16 * C) ∧
      ∀ (ζ : ℝ) (d : ℕ), 0 ≤ ζ → (d : ℝ) ≤ ζ * n →
        K r * (8 * C * ζ) ≤ 1 / (16 * C) →
        K r * (globalRawProfileError 4 E β n r + (5 * C / 2) * d / n) ≤ 1 / (4 * C) := by
  have hCpos : 0 < C := by linarith
  let cap : Fin (L + 1) → ℝ := fun j => min (εRef j / 8) (1 / (128 * C * K j))
  have hcap : ∀ j, 0 < cap j := by
    intro j
    have hKj := hK j (Nat.le_of_lt_succ j.isLt)
    have hεj := hε j (Nat.le_of_lt_succ j.isLt)
    exact lt_min (by positivity) (by positivity)
  let s : Finset ℝ := (univ : Finset (Fin (L + 1))).image cap
  have hs : s.Nonempty := by simp [s]
  let δ := s.min' hs
  have hδ : 0 < δ := by
    obtain ⟨j,_,hj⟩ := mem_image.mp (Finset.min'_mem s hs)
    have hp := hcap j
    rw [hj] at hp
    exact hp
  have hδcap : ∀ j : Fin (L + 1), δ ≤ cap j := fun j =>
    Finset.min'_le s (cap j) (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  let N : ℕ := max 1 ⌈(δ⁻¹) ^ 4⌉₊
  refine ⟨N,le_max_left _ _,?_⟩
  intro n hn r hr
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hCeil : (⌈(δ⁻¹) ^ 4⌉₊ : ℝ) ≤ n := by
    exact_mod_cast ((le_max_right 1 ⌈(δ⁻¹) ^ 4⌉₊).trans hn)
  have hPower : (δ⁻¹) ^ 4 ≤ (n : ℝ) := (Nat.le_ceil _).trans hCeil
  have hAuto : automaticRelativeError n ≤ δ := by
    simpa only [inv_inv] using automaticRelativeError_le_of_power_bound δ⁻¹ n (by positivity) hPower
  let j : Fin (L + 1) := ⟨r,by omega⟩
  have hAutoRef : automaticRelativeError n ≤ εRef r / 8 :=
    hAuto.trans ((hδcap j).trans (min_le_left _ _))
  have hAutoInv : automaticRelativeError n ≤ 1 / (128 * C * K r) :=
    hAuto.trans ((hδcap j).trans (min_le_right _ _))
  have hKpos := hK r hr
  have hSum0 : 0 ≤ ∑ j ∈ range r, β j := sum_nonneg (by intro j _; exact hβ j)
  have hDebt := mul_le_mul_of_nonneg_right hEb hSum0
  have hDebtRef : E * (∑ j ∈ range r, β j) ≤ εRef r / 16 := by
    have hBound := (hAgenda r hr).2
    nlinarith
  have hDebtInv : K r * (E * (∑ j ∈ range r, β j)) ≤ 1 / (32 * C) := by
    have hScaled := mul_le_mul_of_nonneg_left hDebt hKpos.le
    have hBound := (hAgenda r hr).1
    rw [show 1 / (16 * C) = 2 * (1 / (32 * C)) by ring] at hBound
    nlinarith
  have hAutomaticInv : K r * (4 * automaticRelativeError n) ≤ 1 / (32 * C) := by
    calc
      K r * (4 * automaticRelativeError n) ≤ K r * (4 * (1 / (128 * C * K r))) := by
        gcongr
      _ = 1 / (32 * C) := by field_simp; ring
  have hProfile : globalRawProfileError 4 E β n r ≤ εRef r := by
    have hεpos := hε r hr
    dsimp [globalRawProfileError]
    nlinarith
  have hInverse : K r * globalRawProfileError 4 E β n r ≤ 1 / (16 * C) := by
    dsimp [globalRawProfileError]
    calc
      K r * (4 * automaticRelativeError n + E * (∑ j ∈ range r, β j)) =
          K r * (4 * automaticRelativeError n) + K r * (E * (∑ j ∈ range r, β j)) := by ring
      _ ≤ 1 / (32 * C) + 1 / (32 * C) := add_le_add hAutomaticInv hDebtInv
      _ = 1 / (16 * C) := by ring
  refine ⟨hProfile,hInverse,?_⟩
  intro ζ d hζ hd hHoles
  have hBudget := anchored_child_inverse_budget C (K r)
    (globalRawProfileError 4 E β n r) (1 / 4) ζ n d
    hC hKpos.le hnpos (by norm_num) le_rfl hζ hd hInverse hHoles
  convert hBudget using 1 <;> ring

#print axioms exists_scheduled_raw_profile_budget
end TypedTriangle.Vortex
