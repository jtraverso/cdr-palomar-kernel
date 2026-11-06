/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V22 / S10 §4: corrected conditioned-pivot cancellation (exact identities)

Abstract setting: a real linear map `A : (ι → ℝ) →ₗ[ℝ] M` (for the physical case,
`S10V22.realOp` of an integer matrix), columns `col A T = A δ_T`, for each edge `e` a finite
set `tri e` of triangles on `e` (`d_e = |tri e| ≥ 2`), for each source `T` its edge set
`es T`, and `p_e = unifVec (tri e)` (`1/d_e` on `tri e`).

For EACH source `T` separately there is a finite probability space `Ω T` (weights `μ T`), with
pivots `P T e : Ω T → ι` whose marginal is uniform on `tri e ∖ {T}` (pivots conditioned on
being distinct from `T`), and a random certificate `c T ω` with
`A (c T ω) = χ_T − Σ_(e ∈ es T) χ_(P T e ω)`. Nothing is assumed about a global pivot shared
by different sources.

Results (all exact, no estimates):

* `pivot_mean_identity`: `E χ_(P_e) = A(β_e p_e) − χ_T/(d_e − 1)`, `β_e = d_e/(d_e − 1)`;
* `mean_cert_identity` (4.1): `A cbar_T = α_T χ_T − Σ_(e∈T) A(β_e p_e)`,
  `α_T = 1 + Σ_(e∈T) 1/(d_e−1)`;
* `one_le_alpha`: `α_T ≥ 1`;
* `corrected_identity` (4.2): with `h_e = Σ_(T∋e) z_T/α_T` and
  `w = Σ_T (z_T/α_T) cbar_T + Σ_e β_e h_e p_e`, `A w = A z`;
* `corrected_pivot_boundary`: the combination for the per-source random data: if `A z = x`
  then `A w = x` exactly.

The random certificates `c T ω` themselves (the geometric constructor of S10 §3) are INPUTS;
they are not constructed here.
-/

open Finset

noncomputable section

namespace S10V22

section PivotIdentity

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℝ M]

/-- Column `χ_T = A δ_T` of a linear map `A`. -/
def col (A : (ι → ℝ) →ₗ[ℝ] M) (T : ι) : M := A (Pi.single T 1)

lemma apply_eq_sum_col (A : (ι → ℝ) →ₗ[ℝ] M) (z : ι → ℝ) : A z = ∑ T, z T • col A T := by
  have hz : z = ∑ T, z T • (Pi.single T (1 : ℝ) : ι → ℝ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  simp [map_sum, map_smul, col]

/-- Uniform vector `p_e`: `1/d_e` on each triangle of `tri`, zero elsewhere. -/
def unifVec (tri : Finset ι) : ι → ℝ := fun S => if S ∈ tri then 1 / (tri.card : ℝ) else 0

/-- `β_e = d_e/(d_e − 1)`. -/
def betaE (tri : Finset ι) : ℝ := (tri.card : ℝ) / ((tri.card : ℝ) - 1)

/-- `α_T = 1 + Σ_(e ∈ es) 1/(d_e − 1)`. -/
def alphaT {Ed : Type*} (es : Finset Ed) (tri : Ed → Finset ι) : ℝ :=
  1 + ∑ e ∈ es, 1 / (((tri e).card : ℝ) - 1)

lemma apply_unifVec (A : (ι → ℝ) →ₗ[ℝ] M) (tri : Finset ι) :
    A (unifVec tri) = (1 / (tri.card : ℝ)) • ∑ S ∈ tri, col A S := by
  rw [apply_eq_sum_col, Finset.smul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ tri)]
  · refine Finset.sum_congr rfl fun S hS => ?_
    simp [unifVec, hS]
  · intro S _ hS
    simp [unifVec, hS]

/-- **Mean of the conditioned pivot.** If `T ∈ tri` and `d = |tri| ≥ 2`, the mean of `χ_S`
over `S ∈ tri ∖ {T}` is `A(β p) − χ_T/(d−1)`. -/
theorem pivot_mean_identity (A : (ι → ℝ) →ₗ[ℝ] M) {tri : Finset ι} {T : ι} (hT : T ∈ tri)
    (hd : 2 ≤ tri.card) :
    (1 / ((tri.card : ℝ) - 1)) • ∑ S ∈ tri.erase T, col A S =
      A (betaE tri • unifVec tri) - (1 / ((tri.card : ℝ) - 1)) • col A T := by
  have hd' : (2 : ℝ) ≤ tri.card := by exact_mod_cast hd
  have h1 : (tri.card : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (tri.card : ℝ) ≠ 0 := by linarith
  rw [betaE, map_smul, apply_unifVec, smul_smul, ← Finset.add_sum_erase _ _ hT, smul_add]
  rw [show (tri.card : ℝ) / ((tri.card : ℝ) - 1) * (1 / (tri.card : ℝ)) =
    1 / ((tri.card : ℝ) - 1) by field_simp]
  abel

/-- **(4.1) for one source.** Let `μ` be a finite probability on `Ω`. If for each `ω`,
`A c(ω) = χ_T − Σ_(e ∈ es) χ_(P_e(ω))` and each pivot `P_e` has uniform marginal on
`tri e ∖ {T}`, then `cbar = Σ_ω μ(ω) c(ω)` satisfies
`A cbar = α_T χ_T − Σ_(e∈es) A(β_e p_e)`. -/
theorem mean_cert_identity {Ω Ed : Type*} [Fintype Ω] (A : (ι → ℝ) →ₗ[ℝ] M)
    (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (T : ι) (es : Finset Ed) (tri : Ed → Finset ι)
    (hT : ∀ e ∈ es, T ∈ tri e) (hd : ∀ e ∈ es, 2 ≤ (tri e).card)
    (P : Ed → Ω → ι)
    (hP : ∀ e ∈ es, ∀ S, ∑ ω ∈ univ.filter (fun ω => P e ω = S), μ ω =
      if S ∈ (tri e).erase T then 1 / (((tri e).card : ℝ) - 1) else 0)
    (c : Ω → ι → ℝ) (hc : ∀ ω, A (c ω) = col A T - ∑ e ∈ es, col A (P e ω)) :
    A (∑ ω, μ ω • c ω) =
      alphaT es tri • col A T - ∑ e ∈ es, A (betaE (tri e) • unifVec (tri e)) := by
  have hmean : ∀ e ∈ es, ∑ ω, μ ω • col A (P e ω) =
      (1 / (((tri e).card : ℝ) - 1)) • ∑ S ∈ (tri e).erase T, col A S := by
    intro e he
    rw [← Finset.sum_fiberwise univ (P e) (fun ω => μ ω • col A (P e ω))]
    rw [Finset.smul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ ((tri e).erase T))]
    · refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.sum_congr rfl (g := fun ω => μ ω • col A S) (fun ω hω => by
        rw [(Finset.mem_filter.1 hω).2])]
      rw [← Finset.sum_smul, hP e he S, if_pos hS]
    · intro S _ hS
      rw [Finset.sum_congr rfl (g := fun ω => μ ω • col A S) (fun ω hω => by
        rw [(Finset.mem_filter.1 hω).2])]
      rw [← Finset.sum_smul, hP e he S, if_neg hS, zero_smul]
  rw [map_sum]
  simp_rw [map_smul, hc, smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, hμ, one_smul]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun e he => hmean e he)]
  rw [Finset.sum_congr rfl (fun e he => pivot_mean_identity A (hT e he) (hd e he))]
  rw [Finset.sum_sub_distrib, alphaT, add_smul, one_smul, Finset.sum_smul]
  simp only [map_smul]
  abel

omit [Fintype ι] [DecidableEq ι] in
/-- `α_T ≥ 1` as soon as every `d_e ≥ 2`. -/
lemma one_le_alpha {Ed : Type*} (es : Finset Ed) (tri : Ed → Finset ι)
    (hd : ∀ e ∈ es, 2 ≤ (tri e).card) : 1 ≤ alphaT es tri := by
  unfold alphaT
  have : 0 ≤ ∑ e ∈ es, 1 / (((tri e).card : ℝ) - 1) := by
    refine Finset.sum_nonneg fun e he => ?_
    have : (2 : ℝ) ≤ (tri e).card := by exact_mod_cast hd e he
    exact div_nonneg zero_le_one (by linarith)
  linarith

/-- **(4.2), exact.** Assume (4.1) for every `T` with `z_T ≠ 0`:
`A cbar_T = α_T χ_T − Σ_(e ∈ es T) A(β_e p_e)` with `α_T ≠ 0`. With
`h_e = Σ_(T : e ∈ es T) z_T/α_T` and `w = Σ_T (z_T/α_T) cbar_T + Σ_e β_e h_e p_e`, one has
`A w = A z`. -/
theorem corrected_identity {Ed : Type*} [Fintype Ed] [DecidableEq Ed] (A : (ι → ℝ) →ₗ[ℝ] M)
    (es : ι → Finset Ed) (α : ι → ℝ) (β : Ed → ℝ) (p : Ed → ι → ℝ)
    (cbar : ι → ι → ℝ) (z : ι → ℝ) (hα : ∀ T, z T ≠ 0 → α T ≠ 0)
    (hcbar : ∀ T, z T ≠ 0 → A (cbar T) = α T • col A T - ∑ e ∈ es T, A (β e • p e)) :
    A (∑ T, (z T / α T) • cbar T +
        ∑ e, (β e * ∑ T ∈ univ.filter (fun T => e ∈ es T), z T / α T) • p e) = A z := by
  rw [map_add, map_sum, map_sum, apply_eq_sum_col A z]
  have hstep : ∀ T, A ((z T / α T) • cbar T) =
      (z T / α T) • (α T • col A T - ∑ e ∈ es T, A (β e • p e)) := by
    intro T
    by_cases hz : z T = 0
    · simp [hz]
    · rw [map_smul, hcbar T hz]
  simp_rw [hstep, smul_sub, smul_smul, Finset.sum_sub_distrib]
  have h1 : ∀ T, z T / α T * α T = z T := by
    intro T
    by_cases hz : z T = 0
    · simp [hz]
    · exact div_mul_cancel₀ _ (hα T hz)
  simp_rw [h1]
  have h2 : ∑ T, (z T / α T) • ∑ e ∈ es T, A (β e • p e) =
      ∑ e, (β e * ∑ T ∈ univ.filter (fun T => e ∈ es T), z T / α T) • A (p e) := by
    simp_rw [Finset.smul_sum, map_smul, smul_smul]
    rw [Finset.sum_comm' (t' := univ) (s' := fun e => univ.filter (fun T => e ∈ es T))]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun T _ => by ring_nf
    · intro T e
      simp
  rw [h2]
  simp only [map_smul]
  abel

end PivotIdentity

/-! ## Per-source random pivot data and the exact boundary -/

section PerSource

variable {ι M Ed : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ed] [DecidableEq Ed]
  [AddCommGroup M] [Module ℝ M]

/-- **Per-source conditioned-pivot data (INPUT for S10 §3).** For each source `T` in the
support set `src`, a finite probability space `Ω T`, pivots `P T e` with uniform marginal on
`tri e ∖ {T}`, and certificates `c T ω` with `A (c T ω) = χ_T − Σ_(e∈es T) χ_(P T e ω)`.
The spaces are separate for each source (fresh choices). -/
structure PivotData (A : (ι → ℝ) →ₗ[ℝ] M) (src : Finset ι) (es : ι → Finset Ed)
    (tri : Ed → Finset ι) where
  /-- sample space of source `T` -/
  Ω : ι → Type
  [fin : ∀ T, Fintype (Ω T)]
  /-- probability weights -/
  μ : ∀ T, Ω T → ℝ
  μ_nonneg : ∀ T ω, 0 ≤ μ T ω
  μ_sum : ∀ T, ∑ ω, μ T ω = 1
  /-- pivots -/
  P : ∀ T, Ed → Ω T → ι
  /-- random certificates -/
  c : ∀ T, Ω T → ι → ℝ
  mem_tri : ∀ T ∈ src, ∀ e ∈ es T, T ∈ tri e
  two_le : ∀ T ∈ src, ∀ e ∈ es T, 2 ≤ (tri e).card
  marginal : ∀ T ∈ src, ∀ e ∈ es T, ∀ S,
    ∑ ω ∈ univ.filter (fun ω => P T e ω = S), μ T ω =
      if S ∈ (tri e).erase T then 1 / (((tri e).card : ℝ) - 1) else 0
  boundary : ∀ T ∈ src, ∀ ω, A (c T ω) = col A T - ∑ e ∈ es T, col A (P T e ω)

attribute [instance] PivotData.fin

namespace PivotData

variable {A : (ι → ℝ) →ₗ[ℝ] M} {src : Finset ι} {es : ι → Finset Ed} {tri : Ed → Finset ι}

/-- The mean certificate `cbar_T = E c_T`. -/
def cbar (D : PivotData A src es tri) (T : ι) : ι → ℝ := ∑ ω, D.μ T ω • D.c T ω

omit [Fintype Ed] [DecidableEq Ed] in
/-- (4.1) for every source of `src`. -/
theorem cbar_identity (D : PivotData A src es tri) {T : ι} (hT : T ∈ src) :
    A (D.cbar T) = alphaT (es T) tri • col A T -
      ∑ e ∈ es T, A (betaE (tri e) • unifVec (tri e)) :=
  mean_cert_identity A (D.μ T) (D.μ_sum T) T (es T) tri (D.mem_tri T hT) (D.two_le T hT)
    (D.P T) (D.marginal T hT) (D.c T) (D.boundary T hT)

/-- The corrected certificate (4.2): `w = Σ_T (z_T/α_T) cbar_T + Σ_e β_e h_e p_e`. -/
def corrected (D : PivotData A src es tri) (z : ι → ℝ) : ι → ℝ :=
  ∑ T, (z T / alphaT (es T) tri) • D.cbar T +
    ∑ e, (betaE (tri e) * ∑ T ∈ univ.filter (fun T => e ∈ es T),
      z T / alphaT (es T) tri) • unifVec (tri e)

/-- **Exact boundary of the corrected certificate.** If `z` is supported on `src` and
`A z = x`, then `A w = x` exactly. -/
theorem corrected_boundary (D : PivotData A src es tri) {z : ι → ℝ}
    (hz : ∀ T, z T ≠ 0 → T ∈ src) {x : M} (hx : A z = x) : A (D.corrected z) = x := by
  rw [← hx]
  refine corrected_identity A es (fun T => alphaT (es T) tri) (fun e => betaE (tri e))
    (fun e => unifVec (tri e)) D.cbar z (fun T hT => ?_) (fun T hT => D.cbar_identity (hz T hT))
  exact (lt_of_lt_of_le one_pos (one_le_alpha _ _ (D.two_le T (hz T hT)))).ne'

end PivotData

end PerSource

end S10V22
