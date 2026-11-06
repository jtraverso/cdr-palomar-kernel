/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.GenSeed

/-!
# Residual H1 from a bounded right inverse on the common kernel of several functionals

`Refined.gen_residual_seed'` with the single functional `ℓ_w` replaced by a family `(ℓ_{W i})_i`,
each vanishing on every allowed triangle.  The bounded right inverse is only required on the common
kernel (`BRIM`), and the packing hypothesis is replaced by the balance of the residual edge set:
`ℓ_{W i}(𝟏_{E \ L}) = 0` for every `i` (the leave `L` need not be a packing of allowed triangles).
This is the form used for the majority-type host at the corners of the type spectrum (item 3).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Corners

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined

section Gen

variable {V I ι : Type*} [Fintype V] [DecidableEq V] (lab : V → I) (F : Set (Multiset I))
  (W : ι → Sym2 V → ℝ)

/-- A bounded right inverse of the incidence operator on the common kernel of the `ℓ_{W i}`. -/
structure BRIM (K : ℝ) where
  Φ : (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ)
  exact : ∀ d, (∀ i, ellG' (W i) d = 0) → MincG lab F (Φ d) = d
  bound : ∀ d, (∀ i, ellG' (W i) d = 0) → ∀ T, |Φ d T| ≤ K / Fintype.card V * ‖d‖

end Gen

section Reduction

variable {V I ι : Type*} [Fintype V] [DecidableEq V] {lab : V → I} {F : Set (Multiset I)}
  {W : ι → Sym2 V → ℝ} (L : Finset (Sym2 V))

/-- **Residual H1, several functionals**, with the form
of the seed: `μ = gm L (μ₀ + ψ)` and `|ψ| ≤ (K/n)·2(2Δ C₀/n + η)`. -/
theorem multi_residual_seed' (hw : ∀ i, ∀ T ∈ triG lab F, ∑ f ∈ triEdges T, W i f = 0)
    {K C₀ η : ℝ} (hK : 0 ≤ K) (hC₀ : 1 ≤ C₀) (hη : 0 ≤ η) (B : BRIM lab F W K)
    (hres : ∀ i, ellG' (W i) (fun e : E0 V => if e.1 ∈ L then 0 else 1) = 0)
    {μ₀ : Finset V → ℝ}
    (hμ₀ : ∀ T ∈ triG lab F, 1 / (C₀ * Fintype.card V) ≤ μ₀ T ∧ μ₀ T ≤ C₀ / Fintype.card V)
    (hdef : ∀ e : E0 V, |MincG lab F μ₀ e - 1| ≤ η)
    {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hV : 0 < Fintype.card V)
    (hΔ : 8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * Fintype.card V ≤ Fintype.card V) :
    ∃ μ ψ : Finset V → ℝ, IsDiffuseSeed (gHost lab L) F (2 * C₀) μ ∧ μ = gm L (μ₀ + ψ) ∧
      ∀ T, |ψ T| ≤ K / Fintype.card V * (2 * (2 * Δ * (C₀ / Fintype.card V) + η)) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := Nat.cast_pos.mpr hV
  have hC0 : 0 < C₀ := by linarith
  have hμ₀b : ∀ T ∈ triG lab F, |μ₀ T| ≤ C₀ / n := by
    intro T hT
    obtain ⟨h1, h2⟩ := hμ₀ T hT
    rw [abs_of_nonneg (le_trans (by positivity) h1)]
    exact h2
  -- the deficit
  set d0 : E0 V → ℝ := MincG lab F (bm L μ₀) + ((fun e : E0 V => if e.1 ∈ L then 0 else 1) -
    MincG lab F μ₀) with hd0
  have hd0ell : ∀ i, ellG' (W i) d0 = 0 := by
    intro i
    rw [hd0]; simp only [map_add, map_sub, gell_M (hw i), hres i]; ring
  have hd0L : ∀ e : E0 V, e.1 ∈ L → d0 e = 0 := by
    intro e he
    simp only [hd0, Pi.add_apply, Pi.sub_apply]
    rw [gMinc_bm_of_mem L μ₀ e he, if_pos he]; ring
  have hd0G : ∀ e : E0 V, e.1 ∉ L →
      d0 e = MincG lab F (bm L μ₀) e + (1 - MincG lab F μ₀ e) := by
    intro e he
    simp only [hd0, Pi.add_apply, Pi.sub_apply]
    rw [if_neg he]
  have hd0n : ‖d0‖ ≤ 2 * Δ * (C₀ / n) + η := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hd0L e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs, hd0G e he]
      have h1 := gbad_sum_le L hdeg μ₀ (by positivity) hμ₀b e he
      have h2 := hdef e
      rw [abs_sub_comm] at h2
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- the subspace and the operator
  let W0 : Submodule ℝ (E0 V → ℝ) :=
    { carrier := {x | (∀ i, ellG' (W i) x = 0) ∧ ∀ e : E0 V, e.1 ∈ L → x e = 0}
      add_mem' := fun {x y} hx hy => ⟨fun i => by rw [map_add, hx.1 i, hy.1 i, add_zero],
        fun e he => by simp [hx.2 e he, hy.2 e he]⟩
      zero_mem' := ⟨fun i => map_zero _, fun e _ => rfl⟩
      smul_mem' := fun r x hx => ⟨fun i => by rw [map_smul, hx.1 i, smul_zero],
        fun e he => by simp [hx.2 e he]⟩ }
  let R : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := MincG lab F ∘ₗ bm L ∘ₗ B.Φ
  have hRL : ∀ x ∈ W0, ∀ e : E0 V, e.1 ∈ L → R x e = 0 := by
    intro x hx e he
    show MincG lab F (bm L (B.Φ x)) e = 0
    rw [gMinc_bm_of_mem L _ e he, B.exact x hx.1]
    exact hx.2 e he
  have hW : ∀ x ∈ W0, R x ∈ W0 := fun x hx => ⟨fun i => gell_M (hw i) _, hRL x hx⟩
  have hΔR : (8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * n : ℝ) ≤ n := by
    simp only [hn]; exact_mod_cast hΔ
  have hKΔ : 0 ≤ K * Δ := by positivity
  have hKη : 0 ≤ K * C₀ * η * n := by positivity
  have h4 : 4 * K * Δ ≤ n := by
    have h1 : (1 : ℝ) ≤ C₀ ^ 2 := by nlinarith
    have h2 : K * Δ ≤ K * Δ * C₀ ^ 2 := le_mul_of_one_le_right hKΔ h1
    nlinarith
  have hR : ∀ x ∈ W0, ‖R x‖ ≤ ‖x‖ / 2 := by
    intro x hx
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hRL x hx e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs]
      have hb := gbad_sum_le (lab := lab) (F := F) L hdeg (B.Φ x) (r := K / n * ‖x‖)
        (by positivity) (fun T _ => B.bound x hx.1 T) e he
      calc |R x e| = |MincG lab F (bm L (B.Φ x)) e| := rfl
        _ ≤ 2 * Δ * (K / n * ‖x‖) := hb
        _ = (4 * K * Δ / n) * (‖x‖ / 2) := by ring
        _ ≤ 1 * (‖x‖ / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one hn0]; exact h4
        _ = ‖x‖ / 2 := one_mul _
  obtain ⟨x, hxW, hxe, hxn⟩ := solve_contraction W0 R hW hR (d := d0) ⟨hd0ell, hd0L⟩
  have hΦx : ∀ T, |B.Φ x T| ≤ 1 / (2 * C₀ * n) := by
    intro T
    have hb := B.bound x hxW.1 T
    have h2 : ‖x‖ ≤ 2 * (2 * Δ * (C₀ / n) + η) := hxn.trans (by linarith)
    have : K / n * ‖x‖ ≤ K / n * (2 * (2 * Δ * (C₀ / n) + η)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    refine hb.trans (this.trans ?_)
    rw [show K / n * (2 * (2 * Δ * (C₀ / n) + η)) =
        (8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * n) / (2 * C₀ * n * n) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hΔR (by positivity : (0 : ℝ) ≤ 2 * C₀ * n)
    linarith [this, show (1 : ℝ) * (2 * C₀ * n * n) = n * (2 * C₀ * n) by ring]
  -- the seed
  refine ⟨gm L (μ₀ + B.Φ x), B.Φ x, ⟨fun T hT => ?_, fun e he => ?_⟩, rfl, fun T => ?_⟩
  · obtain ⟨hTt, hD⟩ := (gallowed_iff L).mp hT
    obtain ⟨h1, h2⟩ := hμ₀ T hTt
    have hv : gm L (μ₀ + B.Φ x) T = μ₀ T + B.Φ x T := by
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk, if_pos hD, Pi.add_apply]
    rw [hv]
    obtain ⟨hp, hp'⟩ := abs_le.mp (hΦx T)
    have e1 : 1 / (2 * C₀ * n) = 1 / (C₀ * n) - 1 / (2 * C₀ * n) := by field_simp; ring
    have e2 : 1 / (2 * C₀ * n) ≤ C₀ / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      have h2C : (1 : ℝ) ≤ 2 * C₀ * C₀ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2C hn0.le]
    constructor
    · rw [show 1 / (2 * C₀ * n) = 1 / ((2 * C₀) * n) by ring] at e1 hp; linarith
    · have : 2 * C₀ / n = C₀ / n + C₀ / n := by ring
      linarith
  · have hnd : ¬ e.IsDiag := by
      induction e using Sym2.ind with
      | _ u v => rw [Sym2.mk_isDiag_iff]; exact (rG_adj.mp he).2
    have heL : e ∉ L := by
      induction e using Sym2.ind with
      | _ u v => exact (rG_adj.mp he).1
    set e' : E0 V := ⟨e, hnd⟩
    have hkey : MincG lab F (gm L (μ₀ + B.Φ x)) e' = 1 := by
      have hg : ∀ c, MincG lab F (gm L c) e' = MincG lab F c e' - MincG lab F (bm L c) e' := by
        intro c
        have := congrArg (fun c => MincG lab F c e') (gm_add_bm L c)
        simp only [map_add, Pi.add_apply] at this
        linarith
      rw [map_add, map_add, Pi.add_apply, hg, hg]
      have hx1 : MincG lab F (B.Φ x) e' = x e' := by rw [B.exact x hxW.1]
      have hx2 : x e' - R x e' = d0 e' := by rw [← hxe]; rfl
      have hx3 : R x e' = MincG lab F (bm L (B.Φ x)) e' := rfl
      rw [hx1, ← hx3, hx2, hd0G e' heL]
      ring
    rw [← hkey]
    simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
    apply sum_subset
    · intro T hT
      simp only [mem_filter] at hT ⊢
      exact ⟨((gallowed_iff L).mp ((gmem_allowed L).mp hT.1)).1, hT.2⟩
    · intro T hT hTn
      simp only [mem_filter] at hT hTn
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk]
      rw [if_neg]
      intro hD
      exact hTn ⟨(gmem_allowed L).mpr ((gallowed_iff L).mpr ⟨hT.1, hD⟩), hT.2⟩
  · exact (B.bound x hxW.1 T).trans
      (mul_le_mul_of_nonneg_left (hxn.trans (by linarith)) (by positivity))

/-- **Residual H1, several functionals.** -/
theorem multi_residual_seed (hw : ∀ i, ∀ T ∈ triG lab F, ∑ f ∈ triEdges T, W i f = 0)
    {K C₀ η : ℝ} (hK : 0 ≤ K) (hC₀ : 1 ≤ C₀) (hη : 0 ≤ η) (B : BRIM lab F W K)
    (hres : ∀ i, ellG' (W i) (fun e : E0 V => if e.1 ∈ L then 0 else 1) = 0)
    {μ₀ : Finset V → ℝ}
    (hμ₀ : ∀ T ∈ triG lab F, 1 / (C₀ * Fintype.card V) ≤ μ₀ T ∧ μ₀ T ≤ C₀ / Fintype.card V)
    (hdef : ∀ e : E0 V, |MincG lab F μ₀ e - 1| ≤ η)
    {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hV : 0 < Fintype.card V)
    (hΔ : 8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * Fintype.card V ≤ Fintype.card V) :
    ∃ μ, IsDiffuseSeed (gHost lab L) F (2 * C₀) μ := by
  obtain ⟨μ, -, hμ, -, -⟩ := multi_residual_seed' L hw hK hC₀ hη B hres hμ₀ hdef hdeg hV hΔ
  exact ⟨μ, hμ⟩

end Reduction

end CDRBicolour.Absorption.Corners
