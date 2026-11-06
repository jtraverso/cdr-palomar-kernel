/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexExplicitDecidableExactSeed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S10V22
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

variable {V I : Type*} [Fintype V] [DecidableEq V]

private theorem realOp_eq_bdry (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (e : Sym2 V) :
    realOp (triMat (allowedTri H.G H.lab F)) μ e = bdry H F μ e := by
  have hsets : allowedTri H.G H.lab F = allowed H F := by
    ext T
    rw [S10V22.mem_allowedTri]
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hsets]
  simp only [realOp_apply, bdry]
  change (∑ T ∈ (univ : Finset (Finset V)),
      (triMat (allowed H F) e T : ℝ) * μ T) =
    ∑ T ∈ (univ : Finset (Finset V)).filter (IsAllowed H F),
      μ T * indR (triEdges T) e
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hA : IsAllowed H F T
  · have hA' : T ∈ allowed H F := by simpa [allowed] using hA
    simp [triMat, hA', hA, indR, S10V22.edgesOf, triEdges, mul_comm]
  · have hA' : T ∉ allowed H F := by simpa [allowed] using hA
    simp [triMat, hA', hA]

/-- Exactification with the actual correction size, without replacing a
small relative loss by a fixed factor in the diffuse-seed constant. -/
theorem exact_seed_on_fixed_host_with_coefficient_margin
    (J : Host V I) (F : Set (Multiset I)) (Cnext K ξ a b : ℝ)
    (hξ : 0 ≤ ξ) (hS : NativeSmooth.Smooth J F K)
    (hPhysical : IsPhysical J F (edges J)) (μ : Finset V → ℝ)
    (hWeights : ∀ T, IsAllowed J F T →
      a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V)
    (hLoad : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (hLower : 1 / Cnext + K * ξ ≤ a)
    (hUpper : b + K * ξ ≤ Cnext) :
    ∃ ψ : Finset V → ℝ, IsDiffuseSeed J F Cnext ψ ∧
      ∀ T, |ψ T - μ T| ≤ K * ξ / Fintype.card V := by
  let target : Sym2 V → ℝ := castV (ind (edges J))
  have hTarget : target ∈ realImage (triMat (allowedTri J.G J.lab F)) :=
    S10V22.castV_mem_realImage_of_lattice
      (G := J.G) (lab := J.lab) (F := F) hPhysical
  let M := triMat (allowedTri J.G J.lab F)
  have hμImage : realOp M μ ∈ realImage M := ⟨μ, rfl⟩
  have hDefect : target - realOp M μ ∈ realImage M :=
    (realImage M).sub_mem hTarget hμImage
  have hDefectBound : ∀ e, |(target - realOp M μ) e| ≤ ξ := by
    intro e
    by_cases he : e ∈ edges J
    · have := hLoad e he
      simpa [target, M, castV, ind, he, Pi.sub_apply, realOp_eq_bdry,
        abs_sub_comm] using this
    · have hz : bdry J F μ e = 0 := bdry_eq_zero_of_not_mem J F μ he
      simp [target, M, castV, ind, he, Pi.sub_apply, realOp_eq_bdry, hz, hξ]
  obtain ⟨w, _, hwBoundary, hwBound⟩ :=
    hS (target - realOp M μ) hDefect ξ hξ hDefectBound
  let ψ := μ + w
  have hBoundary : realOp M ψ = target := by
    dsimp only [ψ]
    rw [map_add, hwBoundary]
    abel
  have hClose : ∀ T, |ψ T - μ T| ≤ K * ξ / Fintype.card V := by
    intro T
    simpa only [ψ, Pi.add_apply, add_sub_cancel_left] using hwBound T
  refine ⟨ψ, ⟨?_, ?_⟩, hClose⟩
  · intro T hT
    have hRaw := hWeights T hT
    have hCorrection := abs_le.mp (hwBound T)
    have hLow := div_le_div_of_nonneg_right hLower (Nat.cast_nonneg (Fintype.card V))
    have hHigh := div_le_div_of_nonneg_right hUpper (Nat.cast_nonneg (Fintype.card V))
    rw [add_div] at hLow hHigh
    have hBounds : (1 / Cnext) / Fintype.card V ≤ μ T + w T ∧
        μ T + w T ≤ Cnext / Fintype.card V := by
      constructor <;> linarith
    simpa only [ψ, Pi.add_apply, div_div] using hBounds
  · intro e he
    have he' : e ∈ edges J := by simpa [edges] using he
    have hvalue := congrFun hBoundary e
    change (∑ T ∈ triOn J F e, ψ T) = 1
    rw [← bdry_eq_sum_triOn]
    simpa [target, M, castV, ind, he', realOp_eq_bdry] using hvalue

/-- A relative raw coefficient error and correction of at most η/C only
increase the diffuse constant by the relative factor 1+4η. -/
theorem exact_seed_on_fixed_host_with_relative_loss
    (J : Host V I) (F : Set (Multiset I)) (C K ξ η : ℝ)
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hηQuarter : η ≤ 1 / 4) (hξ : 0 ≤ ξ)
    (hS : NativeSmooth.Smooth J F K)
    (hPhysical : IsPhysical J F (edges J)) (μ : Finset V → ℝ)
    (hWeights : ∀ T, IsAllowed J F T →
      ((1 - η) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + η) * C) / Fintype.card V)
    (hLoad : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (hBudget : K * ξ ≤ η / C) :
    ∃ ψ : Finset V → ℝ, IsDiffuseSeed J F ((1 + 4 * η) * C) ψ ∧
      ∀ T, |ψ T - μ T| ≤ K * ξ / Fintype.card V := by
  have hCpos : 0 < C := by linarith
  have hFactor : 0 < 1 + 4 * η := by linarith
  have hLower : 1 / ((1 + 4 * η) * C) + K * ξ ≤ (1 - η) / C := by
    have hInv : 1 / (1 + 4 * η) ≤ 1 - 2 * η := by
      apply (div_le_iff₀ hFactor).2
      nlinarith
    have hScaled := div_le_div_of_nonneg_right hInv hCpos.le
    have hScaled' : 1 / ((1 + 4 * η) * C) ≤ (1 - 2 * η) / C := by
      simpa only [div_div] using hScaled
    have hSum := add_le_add hScaled' hBudget
    calc
      1 / ((1 + 4 * η) * C) + K * ξ ≤ (1 - 2 * η) / C + η / C := hSum
      _ = (1 - η) / C := by ring
  have hUpper : (1 + η) * C + K * ξ ≤ (1 + 4 * η) * C := by
    have hInvC : 1 / C ≤ C := by
      apply (div_le_iff₀ hCpos).2
      nlinarith
    have hηC : η / C ≤ η * C := by
      convert mul_le_mul_of_nonneg_left hInvC hη using 1 <;> ring
    nlinarith [hBudget, hηC]
  exact exact_seed_on_fixed_host_with_coefficient_margin J F
    ((1 + 4 * η) * C) K ξ ((1 - η) / C) ((1 + η) * C)
    hξ hS hPhysical μ hWeights hLoad hLower hUpper

#print axioms exact_seed_on_fixed_host_with_coefficient_margin
#print axioms exact_seed_on_fixed_host_with_relative_loss

end TypedTriangle.Vortex
