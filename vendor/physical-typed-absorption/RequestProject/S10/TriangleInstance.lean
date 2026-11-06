/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10.Realification
public import RequestProject.S10.CoeffBound

@[expose] public section

/-!
# V22 / S10: instantiation for the finite triangle incidence matrix

* `triMat Tri`: the integer triangle–edge incidence matrix of the permitted triangles `Tri`
  (columns indexed by `Finset V`, zero outside `Tri`), `triTw` the vertex–triangle
  incidence weights and `edgeEw` the vertex–edge incidence weights. With these,
  `load triTw v z = Σ_(T∋v) |z_T|` and `inLoad edgeEw v x = Σ_(e∋v) |x_e|`, so
  `IntCertProvider (triMat Tri) triTw edgeEw K n` is exactly the form of the signed
  congestion input (1.1)/P05-CERT, with the per-vertex load `d_abs`-type term.
* `realCert_triangle`: realification (S10 §2) for the triangle matrix.
* `smooth_inverse_of_kernel`: S10 (1.2), CONDITIONAL. From
  (i) the integer congestion provider, (ii) the third-vertex degree condition `d_e ≥ n/C`,
  `n ≥ 2C`, and (iii) the LOCAL KERNEL (3.1) (`LocalKernel`, NOT constructed here),
  every `x` in the real image has a real certificate `w`, `A w = x`, with
  `|w_S| ≤ K∞ xmax / n` for all `S`, whenever `|x_e| ≤ xmax` for all `e`,
  `K∞ = 6C + (3K/2)(L(3Dc² + Dc³/3) + 36C²)`.

This is NOT an unconditional S10: the kernel (3.1) is an explicit structure hypothesis that
still has to be realized from the original hinges; the provider is the separately
kernel-checked P05-CERT (outside this tree). Nothing is claimed for `x` outside the real
image, nor a linear choice of `w`, nor integrality of `w`.
-/

open Finset

noncomputable section

namespace S10V22

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integer triangle–edge incidence matrix of the permitted triangles. -/
def triMat (Tri : Finset (Finset V)) : Sym2 V → Finset V → ℤ :=
  fun e T => if T ∈ Tri ∧ e ∈ edgesOf T then 1 else 0

/-- Vertex–triangle incidence weights (permitted triangles only). -/
def triTw (Tri : Finset (Finset V)) : V → Finset V → ℝ :=
  fun v T => if T ∈ Tri ∧ v ∈ T then 1 else 0

/-- Vertex–edge incidence weights (non-diagonal pairs only). -/
def edgeEw : V → Sym2 V → ℝ := fun v e => if v ∈ e ∧ ¬ e.IsDiag then 1 else 0

/-- **Realification for the triangle matrix (S10 §2, CONDITIONAL on the provider).** -/
theorem realCert_triangle {Tri : Finset (Finset V)} {K n : ℝ}
    (hprov : IntCertProvider (triMat Tri) (triTw Tri) edgeEw K n) {x : Sym2 V → ℝ}
    (hx : x ∈ realImage (triMat Tri)) :
    RealCert (triMat Tri) (triTw Tri) edgeEw K n x :=
  realCert_of_realImage hprov hx

/-! ## Auxiliary facts about the triangle matrix -/

/-- Restriction to permitted triangles. -/
def restrictTri (Tri : Finset (Finset V)) (z : Finset V → ℝ) : Finset V → ℝ :=
  fun T => if T ∈ Tri then z T else 0

lemma realOp_restrictTri (Tri : Finset (Finset V)) (z : Finset V → ℝ) :
    realOp (triMat Tri) (restrictTri Tri z) = realOp (triMat Tri) z := by
  funext e
  simp only [realOp_apply, triMat, restrictTri]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T ∈ Tri <;> simp [hT]

lemma load_restrictTri (Tri : Finset (Finset V)) (z : Finset V → ℝ) (v : V) :
    load (triTw Tri) v (restrictTri Tri z) = load (triTw Tri) v z := by
  simp only [load, triTw, restrictTri]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T ∈ Tri <;> simp [hT]

lemma star_eq_load (Tri : Finset (Finset V)) (z : Finset V → ℝ) (v : V) :
    ∑ T ∈ univ.filter (fun T => v ∈ T), |restrictTri Tri z T| =
      load (triTw Tri) v (restrictTri Tri z) := by
  simp only [load, triTw, restrictTri, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T ∈ Tri <;> by_cases hv : v ∈ T <;> simp [hT, hv]

lemma realOp_triMat_eq (Tri : Finset (Finset V)) {z : Finset V → ℝ}
    (hz : ∀ T, z T ≠ 0 → T ∈ Tri) (e : Sym2 V) :
    realOp (triMat Tri) z e = ∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T := by
  simp only [realOp_apply, triMat, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hzT : z T = 0
  · simp [hzT]
  · have hT := hz T hzT
    by_cases he : e ∈ edgesOf T <;> simp [hT, he]

lemma realImage_diag_eq_zero (Tri : Finset (Finset V)) {x : Sym2 V → ℝ}
    (hx : x ∈ realImage (triMat Tri)) {e : Sym2 V} (he : e.IsDiag) : x e = 0 := by
  obtain ⟨z, rfl⟩ := hx
  simp only [realOp_apply, triMat]
  refine Finset.sum_eq_zero fun T _ => ?_
  have : e ∉ edgesOf T := by simp [edgesOf, he]
  simp [this]

lemma inLoad_edgeEw_le {x : Sym2 V → ℝ} {xmax : ℝ} (hxmax : ∀ e, |x e| ≤ xmax) (v : V) :
    inLoad edgeEw v x ≤ (Fintype.card V : ℝ) * xmax := by
  have hx0 : 0 ≤ xmax := le_trans (abs_nonneg _) (hxmax s(v, v))
  have h1 : inLoad edgeEw v x ≤
      ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e ∧ ¬ e.IsDiag), xmax := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    unfold edgeEw
    split_ifs
    · rw [one_mul]; exact hxmax e
    · rw [zero_mul]
  have hsub : univ.filter (fun e : Sym2 V => v ∈ e ∧ ¬ e.IsDiag) ⊆
      univ.image (fun w => s(v, w)) := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2.1
    exact mem_image_of_mem _ (mem_univ w)
  have hcard : ((univ.filter (fun e : Sym2 V => v ∈ e ∧ ¬ e.IsDiag)).card : ℝ) ≤
      (Fintype.card V : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_image_le
  rw [sum_const, nsmul_eq_mul] at h1
  nlinarith

lemma l1_le_of_diag {x : Sym2 V → ℝ} (hdiag : ∀ e : Sym2 V, e.IsDiag → x e = 0) {xmax : ℝ}
    (hxmax : ∀ e, |x e| ≤ xmax) (hx0 : 0 ≤ xmax) :
    l1 x ≤ (Fintype.card V : ℝ) ^ 2 / 2 * xmax := by
  have h1 : l1 x ≤ ∑ e ∈ univ.filter (fun e : Sym2 V => ¬ e.IsDiag), xmax := by
    unfold l1
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases h : e.IsDiag
    · simp [h, hdiag e h]
    · simp [h, hxmax e]
  have hcard : (univ.filter (fun e : Sym2 V => ¬ e.IsDiag)).card =
      (Fintype.card V).choose 2 := by
    rw [← Sym2.card_subtype_not_diag, Fintype.card_subtype]
  have hch : ((Fintype.card V).choose 2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
    have := Nat.choose_le_pow_div (α := ℝ) 2 (Fintype.card V)
    simpa using this
  rw [sum_const, nsmul_eq_mul, hcard] at h1
  nlinarith

/-! ## The conditional smooth inverse -/

/-- **S10 (1.2), CONDITIONAL on the provider (1.1), the degree condition and the local
kernel (3.1).** For every `x` in the real image of the triangle matrix and every
`xmax ≥ max_e |x_e|`, there is a real `w` with `A w = x` and
`|w_S| ≤ K∞ · xmax / n` for every `S`, with
`K∞ = 6C + (3K/2)(L(3Dc² + Dc³/3) + 36C²)`. The certificate `w` is the corrected average
(4.2) of the kernel's certificates, built from a realified certificate `z` of `x`. -/
theorem smooth_inverse_of_kernel {Tri : Finset (Finset V)} (hTri : ∀ T ∈ Tri, T.card = 3)
    {C K L Dc : ℝ} (hC : 0 < C) (hn : 2 * C ≤ (Fintype.card V : ℝ)) (hdeg : DegreeCond Tri C)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hDc : 0 ≤ Dc)
    (hprov : IntCertProvider (triMat Tri) (triTw Tri) edgeEw K (Fintype.card V : ℝ))
    (Ker : LocalKernel (realOp (triMat Tri)) Tri L Dc)
    {x : Sym2 V → ℝ} (hx : x ∈ realImage (triMat Tri)) {xmax : ℝ}
    (hxmax : ∀ e, |x e| ≤ xmax) :
    ∃ w : Finset V → ℝ, realOp (triMat Tri) w = x ∧
      ∀ S, |w S| ≤ (6 * C + 3 * K / 2 * (L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2)) *
        xmax / (Fintype.card V : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn0 : 0 < n := by linarith
  have hV : Nonempty V := by
    have h := hn0
    rw [hn_def] at h
    exact Fintype.card_pos_iff.1 (by exact_mod_cast h)
  obtain ⟨v₀⟩ := hV
  have hx0 : 0 ≤ xmax := le_trans (abs_nonneg _) (hxmax s(v₀, v₀))
  -- realification
  obtain ⟨z₀, hz₀A, -, hz₀L⟩ := realCert_triangle hprov hx
  set z := restrictTri Tri z₀ with hz_def
  have hzA : realOp (triMat Tri) z = x := by rw [hz_def, realOp_restrictTri, hz₀A]
  have hzsupp : ∀ T, z T ≠ 0 → T ∈ Tri := by
    intro T hT
    by_contra h
    exact hT (by simp [hz_def, restrictTri, h])
  -- the load bound (2.1): `a = (3K/2) n xmax`
  set a := 3 * K / 2 * n * xmax with ha_def
  have hcong : ∀ v, ∑ T ∈ univ.filter (fun T => v ∈ T), |z T| ≤ a := by
    intro v
    rw [hz_def, star_eq_load, load_restrictTri]
    refine (hz₀L v).trans ?_
    have h1 := inLoad_edgeEw_le hxmax v
    have h2 := l1_le_of_diag (fun e he => realImage_diag_eq_zero Tri hx he) hxmax hx0
    have h3 : l1 x / n ≤ n / 2 * xmax := by
      rw [div_le_iff₀ hn0]; nlinarith
    have : inLoad edgeEw v x + l1 x / n ≤ 3 / 2 * n * xmax := by linarith
    calc K * (inLoad edgeEw v x + l1 x / n) ≤ K * (3 / 2 * n * xmax) :=
          mul_le_mul_of_nonneg_left this hK
      _ = a := by rw [ha_def]; ring
  -- the corrected certificate
  refine ⟨Ker.corrected z, Ker.corrected_boundary hzsupp hzA, fun S => ?_⟩
  have hKinf : 0 ≤ (6 * C + 3 * K / 2 * (L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2)) *
      xmax / n := by positivity
  have hw : Ker.corrected z S = ∑ T, (z T / alphaT (edgesOf T) (triOn Tri)) * Ker.cbar T S +
      ∑ e, betaE (triOn Tri e) * (∑ T ∈ univ.filter (fun T => e ∈ edgesOf T),
        z T / alphaT (edgesOf T) (triOn Tri)) * unifVec (triOn Tri e) S := by
    simp [PivotData.corrected, Finset.sum_apply]
  by_cases hS : S ∈ Tri
  · rw [hw]
    refine le_trans (coeff_bound z (fun T hT => hTri T (hzsupp T hT)) hcong
      (fun T => alphaT (edgesOf T) (triOn Tri))
      (fun T hT => one_le_alpha _ _ fun e he =>
        two_le_card_triOn hC hn hdeg (hzsupp T hT) he)
      (θ := 6 * C / n) (by positivity)
      (fun T hT => (abs_inv_sub_one_le (one_le_alpha _ _ fun e he =>
        two_le_card_triOn hC hn hdeg (hzsupp T hT) he)).trans
        (alpha_sub_one_le hC hn hdeg (hzsupp T hT) (hTri T (hzsupp T hT))))
      (fun e => betaE (triOn Tri e)) (abs_beta_le hC hn hdeg) hL hDc Ker.cbar
      (fun T S hT h2 => Ker.cbar_eq_zero_of_two_le (hzsupp T hT) h2)
      (fun T S hT h1 => Ker.abs_cbar_le_one (hzsupp T hT) h1)
      (fun T S hT h0 => Ker.abs_cbar_le_zero (hzsupp T hT) h0)
      (fun e => unifVec (triOn Tri e)) (fun e S he => unifVec_eq_zero he)
      (abs_unifVec_le hC hn hdeg) x
      (fun e => by rw [← hzA, realOp_triMat_eq Tri hzsupp]) hxmax S (hTri S hS)) ?_
    have := sup_bound_assembly (C := C) hn0 hL hDc (le_refl a)
    rw [ha_def] at this ⊢
    convert this using 2
  · have h0 : Ker.corrected z S = 0 := by
      rw [hw]
      have h1 : ∀ T, z T / alphaT (edgesOf T) (triOn Tri) * Ker.cbar T S = 0 := by
        intro T
        by_cases hzT : z T = 0
        · simp [hzT]
        · rw [Ker.cbar_eq_zero_of_not_mem (hzsupp T hzT) hS, mul_zero]
      have h2 : ∀ e, unifVec (triOn Tri e) S = 0 := by
        intro e
        unfold unifVec
        rw [if_neg]
        rw [mem_triOn]
        exact fun h => hS h.1
      simp [h1, h2]
    rw [h0, abs_zero]
    exact hKinf

end S10V22
