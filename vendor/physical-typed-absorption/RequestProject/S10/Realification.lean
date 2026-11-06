/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V22 / S10 §2: realification of integer certificates for a general finite integer matrix

Setting (Mathlib only, no host module):

* `A : E → ι → ℤ` is an arbitrary finite integer matrix (rows `E`, columns `ι`);
* `intOp A z e = Σ_i A e i * z i` (integer), `realOp A z e = Σ_i A e i * z i` (real, linear);
* `intImage A = range (intOp A)` is the ACTUAL integer image (no saturation);
* `realImage A = range (realOp A)`, which equals `span_ℝ` of the integer columns
  (`realImage_eq_span`);
* `l1 z = Σ_i |z i|`;
* vertex loads with FIXED incidence weights: `load tw v z = Σ_i tw v i * |z i|` and
  `inLoad ew v x = Σ_e ew v e * |x e|`. (No sign condition on the weights is needed for the
  results of this file; in the intended use they are `0/1` incidence weights.)

Input (`IntCertProvider A tw ew K n`): for every `y` in the integer image there is an integer
`z` with `A z = y`, `‖z‖₁ ≤ K‖y‖₁` and, for every vertex `v`,
`load_v(z) ≤ K (inLoad_v(y) + ‖y‖₁/n + 1)`.

Output (`RealCert A tw ew K n x`): a REAL `z` with `A z = x`, `‖z‖₁ ≤ K‖x‖₁` and, for every
`v` simultaneously, `load_v(z) ≤ K (inLoad_v(x) + ‖x‖₁/n)`: the SAME homogeneous bounds and
NO additive constant.

* `realCert_of_intImage`: for each integer `y` of the integer image (apply the provider to
  `(m+1) y`, divide by `m+1`, extract a convergent subsequence in a compact box).
* `realCert_of_rat`: for every rational combination of the integer columns (clear
  denominators, use the integer case, rescale).
* `realCert_of_realImage`: for every `x` in the real image / real span (rational
  approximation by floors + finite-dimensional compactness).

The real certificates are existential; they are NOT claimed integer, and no linear choice is
claimed. Nothing is claimed for `x` outside the real image.
-/

open Finset Filter Topology

noncomputable section

namespace S10V22

variable {E ι W : Type*} [Fintype E] [Fintype ι]

/-! ## Definitions -/

/-- Integer action of the matrix. -/
def intOp (A : E → ι → ℤ) (z : ι → ℤ) : E → ℤ := fun e => ∑ i, A e i * z i

/-- Real action of the matrix, as a linear map. -/
def realOp (A : E → ι → ℤ) : (ι → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun z e := ∑ i, (A e i : ℝ) * z i
  map_add' z z' := by funext e; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c z := by funext e; simp [Finset.mul_sum, mul_left_comm]

/-- The actual integer image `A_ℤ(ℤ^ι)`. -/
def intImage (A : E → ι → ℤ) : Set (E → ℤ) := Set.range (intOp A)

/-- The real image `A(ℝ^ι)`. -/
def realImage (A : E → ι → ℤ) : Submodule ℝ (E → ℝ) := LinearMap.range (realOp A)

/-- Real column `i` of `A`. -/
def colR (A : E → ι → ℤ) (i : ι) : E → ℝ := fun e => (A e i : ℝ)

/-- Cast of integer vectors. -/
def castV {α : Type*} (y : α → ℤ) : α → ℝ := fun e => (y e : ℝ)

/-- `ℓ¹` norm. -/
def l1 {α : Type*} [Fintype α] (z : α → ℝ) : ℝ := ∑ i, |z i|

/-- Load of vertex `v` for coefficient vector `z`, with fixed incidence weights `tw`. -/
def load (tw : W → ι → ℝ) (v : W) (z : ι → ℝ) : ℝ := ∑ i, tw v i * |z i|

/-- Input load of vertex `v` for the boundary `x`, with fixed incidence weights `ew`. -/
def inLoad (ew : W → E → ℝ) (v : W) (x : E → ℝ) : ℝ := ∑ e, ew v e * |x e|

/-- **Integer certificate provider (INPUT, not constructed here).** -/
def IntCertProvider (A : E → ι → ℤ) (tw : W → ι → ℝ) (ew : W → E → ℝ) (K n : ℝ) : Prop :=
  ∀ y ∈ intImage A, ∃ z : ι → ℤ, intOp A z = y ∧ l1 (castV z) ≤ K * l1 (castV y) ∧
    ∀ v, load tw v (castV z) ≤ K * (inLoad ew v (castV y) + l1 (castV y) / n + 1)

/-- **Real certificate with homogeneous bounds (no additive constant).** -/
def RealCert (A : E → ι → ℤ) (tw : W → ι → ℝ) (ew : W → E → ℝ) (K n : ℝ) (x : E → ℝ) :
    Prop :=
  ∃ z : ι → ℝ, realOp A z = x ∧ l1 z ≤ K * l1 x ∧
    ∀ v, load tw v z ≤ K * (inLoad ew v x + l1 x / n)

/-! ## Basic lemmas -/

omit [Fintype E] in
lemma realOp_apply (A : E → ι → ℤ) (z : ι → ℝ) (e : E) :
    realOp A z e = ∑ i, (A e i : ℝ) * z i := rfl

omit [Fintype E] in
lemma realOp_eq_sum_col (A : E → ι → ℤ) (z : ι → ℝ) : realOp A z = ∑ i, z i • colR A i := by
  funext e
  simp [realOp_apply, colR, Finset.sum_apply, mul_comm]

omit [Fintype E] in
lemma castV_intOp (A : E → ι → ℤ) (z : ι → ℤ) : castV (intOp A z) = realOp A (castV z) := by
  funext e
  simp [castV, intOp, realOp_apply]

omit [Fintype E] in
/-- The real image is the real span of the integer columns. -/
lemma realImage_eq_span (A : E → ι → ℤ) :
    realImage A = Submodule.span ℝ (Set.range (colR A)) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    rw [realOp_eq_sum_col]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    classical
    refine ⟨Pi.single i 1, ?_⟩
    rw [realOp_eq_sum_col]
    simp [Pi.single_apply]

omit [Fintype E] in
lemma castV_mem_realImage (A : E → ι → ℤ) {y : E → ℤ} (hy : y ∈ intImage A) :
    castV y ∈ realImage A := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨castV z, (castV_intOp A z).symm⟩

lemma l1_smul {α : Type*} [Fintype α] (c : ℝ) (z : α → ℝ) : l1 (c • z) = |c| * l1 z := by
  simp [l1, abs_mul, Finset.mul_sum]

omit [Fintype E] in
lemma load_smul (tw : W → ι → ℝ) (v : W) (c : ℝ) (z : ι → ℝ) :
    load tw v (c • z) = |c| * load tw v z := by
  simp only [load, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype ι] in
lemma inLoad_smul (ew : W → E → ℝ) (v : W) (c : ℝ) (x : E → ℝ) :
    inLoad ew v (c • x) = |c| * inLoad ew v x := by
  simp only [inLoad, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma continuous_l1 {α : Type*} [Fintype α] : Continuous (l1 : (α → ℝ) → ℝ) :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).abs

omit [Fintype E] in
lemma continuous_load (tw : W → ι → ℝ) (v : W) : Continuous (load tw v) :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i).abs

omit [Fintype ι] in
lemma continuous_inLoad (ew : W → E → ℝ) (v : W) : Continuous (inLoad ew v) :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i).abs

omit [Fintype E] in
lemma continuous_realOp (A : E → ι → ℤ) : Continuous (realOp A) :=
  LinearMap.continuous_of_finiteDimensional _

lemma norm_le_l1 {α : Type*} [Fintype α] (z : α → ℝ) : ‖z‖ ≤ l1 z := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |z i|) (fun j _ => abs_nonneg _) (mem_univ i)

/-- Positive homogeneity of real certificates. -/
lemma RealCert.smul {A : E → ι → ℤ} {tw : W → ι → ℝ} {ew : W → E → ℝ} {K n : ℝ}
    {x : E → ℝ} (hx : RealCert A tw ew K n x) {c : ℝ} (hc : 0 ≤ c) :
    RealCert A tw ew K n (c • x) := by
  obtain ⟨z, hz, h1, h2⟩ := hx
  refine ⟨c • z, by rw [map_smul, hz], ?_, fun v => ?_⟩
  · rw [l1_smul, l1_smul, abs_of_nonneg hc]
    calc c * l1 z ≤ c * (K * l1 x) := mul_le_mul_of_nonneg_left h1 hc
      _ = K * (c * l1 x) := by ring
  · rw [load_smul, inLoad_smul, l1_smul, abs_of_nonneg hc]
    calc c * load tw v z ≤ c * (K * (inLoad ew v x + l1 x / n)) :=
          mul_le_mul_of_nonneg_left (h2 v) hc
      _ = K * (c * inLoad ew v x + c * l1 x / n) := by ring

/-! ## The compactness (limit) step -/

/-- **Limit step.** If `xs k → x`, `ε k → 0` and each `xs k` has a real certificate with
the bounds `K‖xs k‖₁` and `K(inLoad_v(xs k) + ‖xs k‖₁/n + ε k)` (all `v` simultaneously),
then `x` has a real certificate with the homogeneous bounds. A convergent subsequence is
extracted in a compact box of the finite coefficient space. -/
theorem realCert_of_limit (A : E → ι → ℤ) (tw : W → ι → ℝ) (ew : W → E → ℝ) {K n : ℝ}
    {x : E → ℝ} {xs : ℕ → E → ℝ} (hxs : Tendsto xs atTop (𝓝 x))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (zs : ℕ → ι → ℝ) (hA : ∀ k, realOp A (zs k) = xs k)
    (h1 : ∀ k, l1 (zs k) ≤ K * l1 (xs k))
    (hc : ∀ k v, load tw v (zs k) ≤ K * (inLoad ew v (xs k) + l1 (xs k) / n + ε k)) :
    RealCert A tw ew K n x := by
  have hl1x : Tendsto (fun k => K * l1 (xs k)) atTop (𝓝 (K * l1 x)) :=
    ((continuous_l1.tendsto x).comp hxs).const_mul K
  obtain ⟨R, hR⟩ := hl1x.bddAbove_range
  have hmem : ∀ k, zs k ∈ Metric.closedBall (0 : ι → ℝ) R := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_l1 _).trans ((h1 k).trans (hR ⟨k, rfl⟩))
  obtain ⟨z, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hxφ : Tendsto (xs ∘ φ) atTop (𝓝 x) := hxs.comp hφ.tendsto_atTop
  have hεφ : Tendsto (ε ∘ φ) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  refine ⟨z, ?_, ?_, fun v => ?_⟩
  · have h1 : Tendsto (fun k => realOp A (zs (φ k))) atTop (𝓝 (realOp A z)) :=
      ((continuous_realOp A).tendsto z).comp hlim
    have h2 : (fun k => realOp A (zs (φ k))) = xs ∘ φ := by
      funext k; exact hA (φ k)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hxφ
  · exact le_of_tendsto_of_tendsto' ((continuous_l1.tendsto z).comp hlim)
      (((continuous_l1.tendsto x).comp hxφ).const_mul K) fun k => h1 (φ k)
  · have hD : Tendsto (fun k => K * (inLoad ew v (xs (φ k)) + l1 (xs (φ k)) / n + ε (φ k)))
        atTop (𝓝 (K * (inLoad ew v x + l1 x / n + 0))) :=
      (((((continuous_inLoad ew v).tendsto x).comp hxφ).add
        (((continuous_l1.tendsto x).comp hxφ).div_const n)).add hεφ).const_mul K
    rw [add_zero] at hD
    exact le_of_tendsto_of_tendsto' (((continuous_load tw v).tendsto z).comp hlim) hD
      fun k => hc (φ k) v

/-! ## Integer vectors of the actual integer image -/

/-- **S10 §2, integer case.** For every `y` in the ACTUAL integer image, the provider applied
to `(m+1)·y`, divided by `m+1`, gives certificates with additive term `1/(m+1)`; a limit in a
compact box gives a REAL certificate of `y` with the homogeneous bounds and no `+1`. -/
theorem realCert_of_intImage {A : E → ι → ℤ} {tw : W → ι → ℝ} {ew : W → E → ℝ} {K n : ℝ}
    (hprov : IntCertProvider A tw ew K n) {y : E → ℤ} (hy : y ∈ intImage A) :
    RealCert A tw ew K n (castV y) := by
  have hmy : ∀ m : ℕ, ((m : ℤ) + 1) • y ∈ intImage A := by
    intro m
    obtain ⟨z, rfl⟩ := hy
    refine ⟨((m : ℤ) + 1) • z, ?_⟩
    funext e
    simp [intOp, Finset.mul_sum, mul_left_comm]
  choose zs hzs using fun m : ℕ => hprov _ (hmy m)
  have hcast : ∀ m : ℕ, castV (((m : ℤ) + 1) • y) = ((m : ℝ) + 1) • castV y := by
    intro m; funext e; simp [castV]
  refine realCert_of_limit A tw ew tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    (fun m => (1 / ((m : ℝ) + 1)) • castV (zs m)) (fun m => ?_) (fun m => ?_) (fun m v => ?_)
  · have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [map_smul, ← castV_intOp, (hzs m).1, hcast, smul_smul,
      one_div_mul_cancel hpos.ne', one_smul]
  · have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h := (hzs m).2.1
    rw [hcast, l1_smul, abs_of_pos hpos] at h
    rw [l1_smul, abs_of_pos (by positivity)]
    calc 1 / ((m : ℝ) + 1) * l1 (castV (zs m))
        ≤ 1 / ((m : ℝ) + 1) * (K * (((m : ℝ) + 1) * l1 (castV y))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * l1 (castV y) := by field_simp
  · have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h := (hzs m).2.2 v
    rw [hcast, inLoad_smul, l1_smul, abs_of_pos hpos] at h
    rw [load_smul, abs_of_pos (by positivity)]
    calc 1 / ((m : ℝ) + 1) * load tw v (castV (zs m))
        ≤ 1 / ((m : ℝ) + 1) * (K * (((m : ℝ) + 1) * inLoad ew v (castV y) +
            ((m : ℝ) + 1) * l1 (castV y) / n + 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * (inLoad ew v (castV y) + l1 (castV y) / n + 1 / ((m : ℝ) + 1)) := by
          field_simp

/-! ## Rational combinations of the integer columns -/

/-- Clearing denominators: some positive integer multiple of a rational vector is integral. -/
lemma exists_int_multiple (q : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : ι → ℤ, ∀ i, (m i : ℚ) = (N : ℚ) * q i := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).den_pos, ?_⟩
  have hdvd : ∀ i, (q i).den ∣ ∏ j, (q j).den := fun i =>
    Finset.dvd_prod_of_mem _ (mem_univ i)
  choose c hc using hdvd
  refine ⟨fun i => (c i : ℤ) * (q i).num, fun i => ?_⟩
  have h := Rat.mul_den_eq_num (q i)
  rw [hc i]
  push_cast
  rw [← h]
  ring

/-- **S10 §2, rational case.** Every rational combination `Σ_i q_i χ_i` of the integer columns
has a real certificate with the homogeneous bounds. -/
theorem realCert_of_rat {A : E → ι → ℤ} {tw : W → ι → ℝ} {ew : W → E → ℝ} {K n : ℝ}
    (hprov : IntCertProvider A tw ew K n) (q : ι → ℚ) :
    RealCert A tw ew K n (realOp A (fun i => (q i : ℝ))) := by
  obtain ⟨N, hN, m, hm⟩ := exists_int_multiple q
  have hy : intOp A m ∈ intImage A := ⟨m, rfl⟩
  have hcert := (realCert_of_intImage hprov hy).smul (c := 1 / (N : ℝ)) (by positivity)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : castV m = (N : ℝ) • (fun i => (q i : ℝ)) := by
    funext i
    have := congrArg (fun r : ℚ => (r : ℝ)) (hm i)
    simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
    simp [castV, this]
  rw [castV_intOp, hmR, map_smul, smul_smul, one_div_mul_cancel hNpos.ne', one_smul] at hcert
  exact hcert

/-! ## The real image (real span) -/

/-- Floor approximation `⌊(k+1) r⌋ / (k+1) → r`. -/
lemma tendsto_floor_div (r : ℝ) :
    Tendsto (fun k : ℕ => (⌊((k : ℝ) + 1) * r⌋ : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 r) := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hlow : Tendsto (fun k : ℕ => r - 1 / ((k : ℝ) + 1)) atTop (𝓝 r) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub r
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun k => ?_)
    (fun k => ?_)
  · have h := Int.sub_one_lt_floor (((k : ℝ) + 1) * r)
    rw [le_div_iff₀ (hpos k)]
    have : (r - 1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = ((k : ℝ) + 1) * r - 1 := by
      field_simp
    linarith
  · have h := Int.floor_le (((k : ℝ) + 1) * r)
    rw [div_le_iff₀ (hpos k)]
    linarith

/-- **S10 §2, real case (main realification theorem).** Under the integer provider, EVERY
`x` in the real image `A(ℝ^ι) = span_ℝ{columns}` has a REAL certificate `z` with `A z = x`,
`‖z‖₁ ≤ K‖x‖₁` and `load_v(z) ≤ K(inLoad_v(x) + ‖x‖₁/n)` for every `v` simultaneously.
Proof: approximate the coefficients by rationals `⌊(k+1)r⌋/(k+1)`, use the rational case and
pass to the limit by compactness. -/
theorem realCert_of_realImage {A : E → ι → ℤ} {tw : W → ι → ℝ} {ew : W → E → ℝ} {K n : ℝ}
    (hprov : IntCertProvider A tw ew K n) {x : E → ℝ} (hx : x ∈ realImage A) :
    RealCert A tw ew K n x := by
  obtain ⟨r, rfl⟩ := hx
  set q : ℕ → ι → ℚ := fun k i => (⌊((k : ℝ) + 1) * r i⌋ : ℚ) / ((k : ℚ) + 1) with hq
  have hqR : ∀ k i, ((q k i : ℚ) : ℝ) = (⌊((k : ℝ) + 1) * r i⌋ : ℝ) / ((k : ℝ) + 1) := by
    intro k i; simp [hq]
  choose zk hzk using fun k => realCert_of_rat hprov (q k)
  have hlim : Tendsto (fun k => realOp A (fun i => (q k i : ℝ))) atTop (𝓝 (realOp A r)) := by
    have hc : Tendsto (fun k => (fun i => (q k i : ℝ))) atTop (𝓝 r) := by
      rw [tendsto_pi_nhds]
      intro i
      simp_rw [hqR]
      exact tendsto_floor_div (r i)
    exact ((continuous_realOp A).tendsto r).comp hc
  refine realCert_of_limit A tw ew hlim (tendsto_const_nhds (x := (0 : ℝ))) zk
    (fun k => (hzk k).1) (fun k => (hzk k).2.1) (fun k v => ?_)
  rw [add_zero]
  exact (hzk k).2.2 v

/-- Same theorem, phrased with the real span of the integer columns. -/
theorem realCert_of_mem_span {A : E → ι → ℤ} {tw : W → ι → ℝ} {ew : W → E → ℝ} {K n : ℝ}
    (hprov : IntCertProvider A tw ew K n) {x : E → ℝ}
    (hx : x ∈ Submodule.span ℝ (Set.range (colR A))) :
    RealCert A tw ew K n x :=
  realCert_of_realImage hprov (by rwa [realImage_eq_span])

/-! ## The first inequality of (2.1): total mass from vertex loads -/

/-- Double counting: if every column has total incidence weight `c`, the vertex loads sum to
`c · ‖z‖₁`. -/
lemma sum_load_eq [Fintype W] {tw : W → ι → ℝ} {c : ℝ} (hc : ∀ i, ∑ v, tw v i = c)
    (z : ι → ℝ) : ∑ v, load tw v z = c * l1 z := by
  unfold load l1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hc i]

/-- (2.1), first inequality: with column weight `c > 0` and all vertex loads `≤ a`,
`‖z‖₁ ≤ |W| · a / c` (for triangles, `c = 3`: `‖z‖₁ ≤ n a / 3`). -/
lemma l1_le_of_load_le [Fintype W] {tw : W → ι → ℝ} {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ i, ∑ v, tw v i = c) {z : ι → ℝ} {a : ℝ} (ha : ∀ v, load tw v z ≤ a) :
    l1 z ≤ (Fintype.card W : ℝ) * a / c := by
  have h := sum_load_eq hc z
  have hle : ∑ v, load tw v z ≤ (Fintype.card W : ℝ) * a := by
    calc ∑ v, load tw v z ≤ ∑ _v : W, a := Finset.sum_le_sum fun v _ => ha v
      _ = (Fintype.card W : ℝ) * a := by rw [sum_const, card_univ, nsmul_eq_mul]
  rw [le_div_iff₀ hc0]
  linarith

end S10V22
