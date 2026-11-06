/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V38.RealKernel
@[expose] public section

/-!
# V38 §1 — bounded REAL extension of an integer charge functional on an actual subgroup

Let `E` be finite, `M ≤ ℤ^E` an ACTUAL integer submodule (no saturation, finite index or rank
hypothesis) and `f : M → ℝ` additive (`ℤ`-linear) with `|f x| ≤ A ∑ e |x e|`, `A ≥ 0`.
Then there are REAL edge coefficients `λ_e` with `|λ_e| ≤ A` (the SAME constant `A`, independent
of `|E|`) and `∑ e, λ_e x_e = f x` for every `x ∈ M` (`bounded_extension`; the integer-valued
version is `bounded_extension_int`).

Proof (finite-dimensional Hahn–Banach):
* `M` is finitely generated (`ℤ^E` is Noetherian); fix generators `m_i`;
* `genOp a = ∑ a_i m_i` (real), `valOp a = ∑ a_i f(m_i)`;
* `ker_genOp_le` — every REAL relation among the generators annihilates the `f`-values: by
  `realKer_mem_span` the real relations are spanned by integer relations, on which the
  bound forces `f = 0` (no rational approximation of real relations needed);
* `valOp_bound` — `|valOp a| ≤ A ‖genOp a‖₁` for rational `a` by clearing denominators and
  homogeneity, then for all real `a` by density of `ℚ^ι` and continuity;
* the functional `ψ` on `range genOp` (from `range_dualMap_eq_dualAnnihilator_ker`) is
  dominated by the sublinear `A‖·‖₁`, and `exists_extension_of_le_sublinear` extends it;
* `λ_e = g(δ_e)` gives `|λ_e| ≤ A ‖δ_e‖₁ = A`.

No provider of a bounded real extension is assumed.
-/

open Finset Topology

noncomputable section

namespace S07V38

open S10V22

variable {E : Type*} [Fintype E]

section Generators

variable {ι : Type*} [Fintype ι] (m : ι → E → ℤ) (fv : ι → ℝ)

/-- Real combination of the integer generators: `a ↦ ∑ i, a i • m i`. -/
def genOp : (ι → ℝ) →ₗ[ℝ] (E → ℝ) := realOp (fun e i => m i e)

/-- Real combination of the values: `a ↦ ∑ i, a i * fv i`. -/
def valOp : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i * fv i
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_assoc]

omit [Fintype E] in
lemma genOp_apply (a : ι → ℝ) (e : E) : genOp m a e = ∑ i, (m i e : ℝ) * a i := rfl

lemma valOp_apply (a : ι → ℝ) : valOp fv a = ∑ i, a i * fv i := rfl

omit [Fintype E] in
lemma genOp_castV (z : ι → ℤ) : genOp m (castV z) = castV (fun e => ∑ i, z i * m i e) := by
  funext e
  simp [genOp_apply, castV, mul_comm]

lemma valOp_castV (z : ι → ℤ) : valOp fv (castV z) = ∑ i, (z i : ℝ) * fv i := rfl

/-- Bound on integer combinations (the hypothesis of the generator form). -/
def IntBound (A : ℝ) : Prop :=
  ∀ z : ι → ℤ, |∑ i, (z i : ℝ) * fv i| ≤ A * l1 (castV (fun e => ∑ i, z i * m i e))

variable {m fv}

/-- **Real relations annihilate the values.** -/
theorem ker_genOp_le {A : ℝ} (hb : IntBound m fv A) :
    LinearMap.ker (genOp m) ≤ LinearMap.ker (valOp fv) := by
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  have hspan := realKer_mem_span (fun e i => m i e) a (fun e => by
    have := congrFun ha e
    rw [genOp_apply] at this
    simpa using this)
  have hle : Submodule.span ℝ (castV '' intKer (fun e i => m i e)) ≤
      LinearMap.ker (valOp fv) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, valOp_castV]
    have h0 : (fun e => ∑ i, z i * m i e) = 0 := by
      funext e
      have := hz e
      simp only [Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := hb z
    rw [h0] at this
    simp only [l1, castV, Pi.zero_apply, Int.cast_zero, abs_zero, Finset.sum_const_zero,
      mul_zero] at this
    exact abs_nonpos_iff.1 this
  exact hle hspan

/-- **The `ℓ¹` bound for all real combinations** (rational case by clearing denominators,
real case by density and continuity). -/
theorem valOp_bound {A : ℝ} (hb : IntBound m fv A) (a : ι → ℝ) :
    |valOp fv a| ≤ A * l1 (genOp m a) := by
  have hdense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hdense.induction_on a ?_ ?_
  · exact isClosed_le ((LinearMap.continuous_of_finiteDimensional _).abs)
      (continuous_const.mul (continuous_l1.comp (LinearMap.continuous_of_finiteDimensional _)))
  · intro q
    obtain ⟨D, z, hD, hz⟩ := clear_den q
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hq : (fun i => (q i : ℝ)) = (1 / (D : ℝ)) • castV z := by
      funext i
      have : (z i : ℝ) = D * q i := by exact_mod_cast hz i
      simp only [Pi.smul_apply, castV, smul_eq_mul, this]
      field_simp
    show |valOp fv (fun i => (q i : ℝ))| ≤ A * l1 (genOp m (fun i => (q i : ℝ)))
    rw [hq, map_smul, map_smul, l1_smul, smul_eq_mul, abs_mul, valOp_castV, genOp_castV,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / D)]
    have := hb z
    calc 1 / (D : ℝ) * |∑ i, (z i : ℝ) * fv i|
        ≤ 1 / D * (A * l1 (castV (fun e => ∑ i, z i * m i e))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = A * (1 / D * l1 (castV (fun e => ∑ i, z i * m i e))) := by ring

lemma l1_add_le (x y : E → ℝ) : l1 (x + y) ≤ l1 x + l1 y := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => abs_add_le _ _

lemma l1_delta [DecidableEq E] (e : E) : l1 (fun j : E => if e = j then (1 : ℝ) else 0) = 1 := by
  unfold l1
  simp [apply_ite]

/-- **Bounded extension, generator form.** If every integer combination of the generators
satisfies `|∑ z_i fv_i| ≤ A ‖∑ z_i m_i‖₁`, there are real `λ` with `|λ_e| ≤ A` and
`∑ e, λ_e (∑ z_i m_i)_e = ∑ z_i fv_i` for every integer `z`. -/
theorem bounded_extension_gen {A : ℝ} (hA : 0 ≤ A) (hb : IntBound m fv A) :
    ∃ lam : E → ℝ, (∀ e, |lam e| ≤ A) ∧
      ∀ z : ι → ℤ, ∑ e, lam e * ((∑ i, z i * m i e : ℤ) : ℝ) = ∑ i, (z i : ℝ) * fv i := by
  classical
  -- functional on the range
  have hann : valOp fv ∈ (LinearMap.ker (genOp m)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro a ha
    exact ker_genOp_le hb ha
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨ψ, hψ⟩ := hann
  have hψa : ∀ a, ψ (genOp m a) = valOp fv a := fun a => by
    rw [← hψ]; rfl
  -- Hahn–Banach
  let f' : (E → ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range (genOp m), ψ.domRestrict _⟩
  obtain ⟨g, hg, hgN⟩ := exists_extension_of_le_sublinear f' (fun x => A * l1 x)
    (fun c hc x => by show A * l1 (c • x) = c * (A * l1 x); rw [l1_smul, abs_of_pos hc]; ring)
    (fun x y => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (l1_add_le x y) hA)
    (fun x => by
      obtain ⟨a, ha⟩ := x.2
      show ψ (x : E → ℝ) ≤ A * l1 (x : E → ℝ)
      rw [← ha, hψa]
      exact (le_abs_self _).trans (valOp_bound hb a))
  have hgr : ∀ a, g (genOp m a) = valOp fv a := fun a => by
    rw [← hψa]
    exact hg ⟨genOp m a, LinearMap.mem_range_self _ a⟩
  refine ⟨fun e => g (fun j => if e = j then 1 else 0), fun e => ?_, fun z => ?_⟩
  · rw [abs_le]
    constructor
    · have h := hgN (-(fun j : E => if e = j then (1 : ℝ) else 0))
      rw [map_neg] at h
      have hl : l1 (-(fun j : E => if e = j then (1 : ℝ) else 0)) = 1 := by
        rw [show -(fun j : E => if e = j then (1 : ℝ) else 0) =
          (-1 : ℝ) • (fun j : E => if e = j then (1 : ℝ) else 0) by simp, l1_smul, l1_delta]
        simp
      rw [hl] at h
      linarith
    · have h := hgN (fun j : E => if e = j then (1 : ℝ) else 0)
      rw [l1_delta] at h
      linarith
  · rw [← valOp_castV, ← hgr, genOp_castV, LinearMap.pi_apply_eq_sum_univ g]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [castV, smul_eq_mul, mul_comm]

end Generators

/-- **V38 §1: bounded real extension from an actual integer subgroup.** `E` finite,
`M ≤ ℤ^E` any submodule, `f : M → ℝ` additive with `|f x| ≤ A ∑ e |x e|` and `A ≥ 0`.
Then real coefficients `λ` exist with `|λ_e| ≤ A` and `∑ e, λ_e x_e = f x` for every `x ∈ M`. -/
theorem bounded_extension (M : Submodule ℤ (E → ℤ)) (f : M →ₗ[ℤ] ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x : M, |f x| ≤ A * ∑ e, |(((x : E → ℤ) e : ℤ) : ℝ)|) :
    ∃ lam : E → ℝ, (∀ e, |lam e| ≤ A) ∧
      ∀ x : M, ∑ e, lam e * (((x : E → ℤ) e : ℤ) : ℝ) = f x := by
  classical
  obtain ⟨s, hs⟩ : M.FG := IsNoetherian.noetherian M
  let m : s → E → ℤ := fun i => (i : E → ℤ)
  have hmM : ∀ i, m i ∈ M := fun i => hs ▸ Submodule.subset_span i.2
  let fv : s → ℝ := fun i => f ⟨m i, hmM i⟩
  have hcomb : ∀ z : s → ℤ, ∑ i, z i • (⟨m i, hmM i⟩ : M) =
      ⟨fun e => ∑ i, z i * m i e, by
        have : (fun e => ∑ i, z i * m i e) = ∑ i, z i • m i := by
          funext e; simp [Finset.sum_apply]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmM i)⟩ := by
    intro z
    apply Subtype.ext
    funext e
    simp [Finset.sum_apply]
  have hfz : ∀ z : s → ℤ, ∑ i, (z i : ℝ) * fv i =
      f ⟨fun e => ∑ i, z i * m i e, by
        have : (fun e => ∑ i, z i * m i e) = ∑ i, z i • m i := by
          funext e; simp [Finset.sum_apply]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmM i)⟩ := by
    intro z
    rw [← hcomb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  have hb : IntBound m fv A := by
    intro z
    rw [hfz]
    exact hf _
  obtain ⟨lam, hlam, hext⟩ := bounded_extension_gen hA hb
  refine ⟨lam, hlam, fun x => ?_⟩
  -- write `x` as an integer combination of the generators
  have hx : (x : E → ℤ) ∈ Submodule.span ℤ (Set.range m) := by
    have : Set.range m = (s : Set (E → ℤ)) := Subtype.range_coe
    rw [this, hs]; exact x.2
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hxe : ∀ e, (x : E → ℤ) e = ∑ i, z i * m i e := fun e => by
    rw [← hz]; simp [Finset.sum_apply]
  have hxeq : x = ⟨fun e => ∑ i, z i * m i e, by
        have : (fun e => ∑ i, z i * m i e) = ∑ i, z i • m i := by
          funext e; simp [Finset.sum_apply]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmM i)⟩ :=
    Subtype.ext (funext hxe)
  rw [hxeq, ← hfz, ← hext z]

/-- Integer-valued version of `bounded_extension`: `f : M → ℤ` additive with
`|f x| ≤ A ∑ e |x e|` has a real extension with `|λ_e| ≤ A`. -/
theorem bounded_extension_int (M : Submodule ℤ (E → ℤ)) (f : M →ₗ[ℤ] ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x : M, |((f x : ℤ) : ℝ)| ≤ A * ∑ e, |(((x : E → ℤ) e : ℤ) : ℝ)|) :
    ∃ lam : E → ℝ, (∀ e, |lam e| ≤ A) ∧
      ∀ x : M, ∑ e, lam e * (((x : E → ℤ) e : ℤ) : ℝ) = f x :=
  bounded_extension M ((Int.castAddHom ℝ).toIntLinearMap.comp f) hA hf

end S07V38
