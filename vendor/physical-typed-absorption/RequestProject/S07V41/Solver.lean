/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V38.RealKernel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V41 §1 — a uniformly bounded real solver for bounded integer row sets

For a finite SET `T` of integer row vectors in `Fin d → ℤ` and a real right-hand side `b`
annihilated by every integer linear relation among the rows (`RelCompat`), there is a real
`u : Fin d → ℝ` with `dotZ u t = b t` for every row `t ∈ T`.

* `solver_fixed` — for one fixed row set `T` the solution can be chosen with
  `|u i| ≤ C_T * a` whenever `|b t| ≤ a` on `T`. Proof: integer relations span the real
  relations (`S07V38.realKer_mem_span`), so `b` lies in the range of `u ↦ (dotZ u t)_t`
  (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`); a linear right inverse on that range is
  continuous (finite dimension) and its operator norm is `C_T`.
* `bounded_solver` — the constant is UNIFORM over all row sets inside the box
  `[-K, K]^d`: there are finitely many such sets, and the sum of their constants works.
  The constant depends only on `d` and `K`.
-/

open Finset

noncomputable section

namespace S07V41

open S10V22

variable {d : ℕ}

/-- Real dot product of a real vector with an integer row. -/
def dotZ (u : Fin d → ℝ) (t : Fin d → ℤ) : ℝ := ∑ i, u i * (t i : ℝ)

/-- Every integer linear relation among the rows of `T` annihilates `b`. -/
def RelCompat (T : Finset (Fin d → ℤ)) (b : (Fin d → ℤ) → ℝ) : Prop :=
  ∀ z : T → ℤ, ∑ t : T, z t • (t : Fin d → ℤ) = 0 → ∑ t : T, (z t : ℝ) * b t = 0

/-- Solvability (without bound) of a compatible system. -/
theorem exists_solution (T : Finset (Fin d → ℤ)) (b : (Fin d → ℤ) → ℝ)
    (hb : RelCompat T b) : ∃ u : Fin d → ℝ, ∀ t : T, dotZ u t = b t := by
  classical
  -- the transposed map `y ↦ ∑ t, y t • t`
  let Bmap : (T → ℝ) →ₗ[ℝ] (Fin d → ℝ) := realOp (fun i (t : T) => (t : Fin d → ℤ) i)
  let ℓ : Module.Dual ℝ (T → ℝ) :=
    { toFun := fun y => ∑ t, y t * b t
      map_add' := fun y y' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c y => by simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker Bmap ≤ LinearMap.ker ℓ := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hspan := S07V38.realKer_mem_span (fun i (t : T) => (t : Fin d → ℤ) i) y
      (fun i => by have := congrFun hy i; simpa [Bmap, realOp] using this)
    refine Submodule.span_le.mpr ?_ hspan
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    show ∑ t, (z t : ℝ) * b t = 0
    apply hb z
    funext i
    have := hz i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hmem : ℓ ∈ (LinearMap.ker Bmap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    exact hker hy
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨fun i => φ (Pi.single i 1), fun t => ?_⟩
  have h1 : ℓ (Pi.single t 1) = b t := by
    simp [ℓ, Pi.single_apply]
  rw [← h1, ← hφ, LinearMap.dualMap_apply]
  have h2 : Bmap (Pi.single t 1) = ∑ i, ((t : Fin d → ℤ) i : ℝ) • (Pi.single i 1 : Fin d → ℝ) := by
    funext j
    simp [Bmap, realOp, Pi.single_apply]
  rw [h2, map_sum]
  simp only [map_smul, smul_eq_mul, dotZ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Bounded solver for one fixed row set.** -/
theorem solver_fixed (T : Finset (Fin d → ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : (Fin d → ℤ) → ℝ) (a : ℝ), 0 ≤ a → (∀ t ∈ T, |b t| ≤ a) →
      RelCompat T b → ∃ u : Fin d → ℝ, (∀ t ∈ T, dotZ u t = b t) ∧ ∀ i, |u i| ≤ C * a := by
  classical
  let Φ : (Fin d → ℝ) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun u t => dotZ u t
      map_add' := fun u v => by funext t; simp [dotZ, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c u => by funext t; simp [dotZ, Finset.mul_sum, mul_assoc] }
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Φ.rangeRestrict
    (LinearMap.range_rangeRestrict Φ)
  let gC := LinearMap.toContinuousLinearMap g
  refine ⟨‖gC‖, gC.opNorm_nonneg, fun b a ha hba hb => ?_⟩
  obtain ⟨u0, hu0⟩ := exists_solution T b hb
  have hmem : (fun t : T => b t) ∈ LinearMap.range Φ := ⟨u0, funext fun t => hu0 t⟩
  let w : LinearMap.range Φ := ⟨fun t : T => b t, hmem⟩
  have hgw : Φ (g w) = fun t : T => b t := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg w)
    simpa using this
  refine ⟨g w, fun t ht => ?_, fun i => ?_⟩
  · have := congrFun hgw ⟨t, ht⟩
    simpa [Φ] using this
  · have hw : ‖w‖ ≤ a := by
      show ‖(fun t : T => b t)‖ ≤ a
      exact (pi_norm_le_iff_of_nonneg ha).mpr fun t => by
        simpa [Real.norm_eq_abs] using hba t t.2
    calc |g w i| = ‖(g w) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖g w‖ := norm_le_pi_norm _ i
      _ = ‖gC w‖ := rfl
      _ ≤ ‖gC‖ * ‖w‖ := gC.le_opNorm w
      _ ≤ ‖gC‖ * a := mul_le_mul_of_nonneg_left hw gC.opNorm_nonneg

/-- The box `[-K, K]^d` of integer rows. -/
def rowBox (d : ℕ) (K : ℤ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-K) K

lemma mem_rowBox {K : ℤ} {t : Fin d → ℤ} : t ∈ rowBox d K ↔ ∀ i, |t i| ≤ K := by
  simp [rowBox, Fintype.mem_piFinset, abs_le]

/-- **Uniform bounded solver.** The constant `C` depends only on `d` and the row bound `K`;
it serves every finite row set inside the box `[-K, K]^d`. -/
theorem bounded_solver (d : ℕ) (K : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Finset (Fin d → ℤ)), (∀ t ∈ T, ∀ i, |t i| ≤ K) →
      ∀ (b : (Fin d → ℤ) → ℝ) (a : ℝ), 0 ≤ a → (∀ t ∈ T, |b t| ≤ a) →
      RelCompat T b → ∃ u : Fin d → ℝ, (∀ t ∈ T, dotZ u t = b t) ∧ ∀ i, |u i| ≤ C * a := by
  classical
  choose CT hCT0 hCT using fun T : Finset (Fin d → ℤ) => solver_fixed T
  refine ⟨∑ T ∈ (rowBox d K).powerset, CT T, Finset.sum_nonneg fun T _ => hCT0 T,
    fun T hT b a ha hba hb => ?_⟩
  obtain ⟨u, hu, hub⟩ := hCT T b a ha hba hb
  have hTmem : T ∈ (rowBox d K).powerset :=
    Finset.mem_powerset.mpr fun t ht => mem_rowBox.mpr (hT t ht)
  have hle : CT T ≤ ∑ T ∈ (rowBox d K).powerset, CT T :=
    Finset.single_le_sum (fun T _ => hCT0 T) hTmem
  exact ⟨u, hu, fun i => (hub i).trans (mul_le_mul_of_nonneg_right hle ha)⟩

end S07V41
