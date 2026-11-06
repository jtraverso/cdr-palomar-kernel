/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10.PivotCorrection

@[expose] public section

/-!
# V22 / S10 §5: coefficient estimate, CONDITIONAL on the local kernel (3.1)

Triangle geometry on a finite vertex type `V`, `n = |V|`; coefficient index `Finset V`,
edges `Sym2 V`. `Tri` is the finite set of permitted triangles (all of size 3) and
`triOn Tri e` the permitted triangles through `e` (`d_e = |triOn Tri e|`).

* `LocalKernel A Tri L Dc` packages the GEOMETRIC INPUT (3.1) of S10 §3: per-source
  conditioned-pivot data (`PivotData`) whose random certificates are supported on permitted
  triangles, vanish on every triangle sharing `≥ 2` vertices with the source, and satisfy
  `E|c_T(S)| ≤ L (Dc/n)^(3 − |S∩T|)` for `|S∩T| ≤ 1`.
  **This kernel is NOT constructed in this project.** It must be realized from the original
  hinges (the geometric constructor of `semilla_residual/PRUEBAS.md` §§2–3).
* `LocalKernel.cbar_abs_le_*`: the induced bounds on the means `cbar_T = E c_T`.
* `coeff_bound` ((5.1)+(5.2)): for `z` with vertex loads `≤ a`,
  `|w_S| ≤ L(3Dc² + Dc³/3) a/n² + 6π(xmax + θ a)`.
* `alpha_sub_one_le`, `abs_beta_le`, `abs_unifVec_le`: the bounds `α_T − 1 ≤ 6C/n`,
  `|β_e| ≤ 2`, `p_e(S) ≤ C/n` from `d_e ≥ n/C` and `n ≥ 2C`.
* `sup_bound_assembly`: with `a ≤ (3K/2) n xmax` this gives `|w_S| ≤ K∞ xmax / n`,
  `K∞ = 6C + (3K/2)(L(3Dc² + Dc³/3) + 36C²)`.
-/

open Finset

noncomputable section

namespace S10V22

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges (non-diagonal pairs) of a vertex set. -/
def edgesOf (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- Permitted triangles through the edge `e`. -/
def triOn (Tri : Finset (Finset V)) (e : Sym2 V) : Finset (Finset V) :=
  Tri.filter (fun T => e ∈ edgesOf T)

omit [Fintype V] in
lemma card_edgesOf (S : Finset V) : (edgesOf S).card = S.card.choose 2 := by
  rw [← Sym2.card_image_offDiag]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ x y =>
  simp only [edgesOf, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_image, mem_offDiag]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩
  · rintro ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, he⟩
    change s(p, q) = s(x, y) at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨hp, hq⟩, hpq⟩
    · exact ⟨⟨hq, hp⟩, Ne.symm hpq⟩

omit [Fintype V] in
lemma mem_triOn {Tri : Finset (Finset V)} {T : Finset V} {e : Sym2 V} :
    T ∈ triOn Tri e ↔ T ∈ Tri ∧ e ∈ edgesOf T := by
  simp [triOn]

/-- **Local geometric kernel (3.1) (INPUT, NOT constructed here).** -/
structure LocalKernel {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A : (Finset V → ℝ) →ₗ[ℝ] M) (Tri : Finset (Finset V)) (L Dc : ℝ)
    extends PivotData A Tri edgesOf (triOn Tri) where
  /-- certificates use only permitted triangles -/
  supp : ∀ T ∈ Tri, ∀ ω S, c T ω S ≠ 0 → S ∈ Tri
  /-- certificates avoid every triangle sharing two vertices (an edge) with the source -/
  avoid : ∀ T ∈ Tri, ∀ ω S, 2 ≤ (S ∩ T).card → c T ω S = 0
  /-- the expectation kernel (3.1) -/
  expect : ∀ T ∈ Tri, ∀ S, (S ∩ T).card ≤ 1 →
    ∑ ω, μ T ω * |c T ω S| ≤ L * (Dc / (Fintype.card V : ℝ)) ^ (3 - (S ∩ T).card)

namespace LocalKernel

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {A : (Finset V → ℝ) →ₗ[ℝ] M}
  {Tri : Finset (Finset V)} {L Dc : ℝ}

lemma abs_cbar_le (Ker : LocalKernel A Tri L Dc) (T S : Finset V) :
    |Ker.cbar T S| ≤ ∑ ω, Ker.μ T ω * |Ker.c T ω S| := by
  unfold PivotData.cbar
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Ker.μ_nonneg T ω)]

lemma cbar_eq_zero_of_two_le (Ker : LocalKernel A Tri L Dc) {T S : Finset V} (hT : T ∈ Tri)
    (h : 2 ≤ (S ∩ T).card) : Ker.cbar T S = 0 := by
  unfold PivotData.cbar
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun ω _ => by simp [Ker.avoid T hT ω S h]

lemma cbar_eq_zero_of_not_mem (Ker : LocalKernel A Tri L Dc) {T S : Finset V} (hT : T ∈ Tri)
    (hS : S ∉ Tri) : Ker.cbar T S = 0 := by
  unfold PivotData.cbar
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases h : Ker.c T ω S = 0
  · simp [h]
  · exact absurd (Ker.supp T hT ω S h) hS

lemma abs_cbar_le_one (Ker : LocalKernel A Tri L Dc) {T S : Finset V} (hT : T ∈ Tri)
    (h : (S ∩ T).card = 1) :
    |Ker.cbar T S| ≤ L * Dc ^ 2 / (Fintype.card V : ℝ) ^ 2 := by
  have := (Ker.abs_cbar_le T S).trans (Ker.expect T hT S h.le)
  rw [h] at this
  simpa [div_pow, mul_div_assoc] using this

lemma abs_cbar_le_zero (Ker : LocalKernel A Tri L Dc) {T S : Finset V} (hT : T ∈ Tri)
    (h : (S ∩ T).card = 0) :
    |Ker.cbar T S| ≤ L * Dc ^ 3 / (Fintype.card V : ℝ) ^ 3 := by
  have := (Ker.abs_cbar_le T S).trans (Ker.expect T hT S (by omega))
  rw [h] at this
  simpa [div_pow, mul_div_assoc] using this

end LocalKernel

/-- Double counting: `Σ_T f(T) |U ∩ T| = Σ_(v ∈ U) Σ_(T ∋ v) f(T)`. -/
lemma sum_mul_card_inter (f : Finset V → ℝ) (U : Finset V) :
    ∑ T, f T * ((U ∩ T).card : ℝ) = ∑ v ∈ U, ∑ T ∈ univ.filter (fun T => v ∈ T), f T := by
  have hc : ∀ T : Finset V, ((U ∩ T).card : ℝ) = ∑ v ∈ U, if v ∈ T then (1 : ℝ) else 0 := by
    intro T
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  simp_rw [hc, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_filter]

/-- **(5.1)+(5.2), CONDITIONAL on the kernel bounds.** Inputs:
* `z` supported on 3-sets with vertex loads `Σ_(T∋v) |z_T| ≤ a`;
* `α_T ≥ 1`, `|1/α_T − 1| ≤ θ` (where `z_T ≠ 0`), `|β_e| ≤ 2`;
* `cbar_T(S) = 0` if `|S∩T| ≥ 2`, `|cbar_T(S)| ≤ L Dc²/n²` if `|S∩T| = 1`,
  `|cbar_T(S)| ≤ L Dc³/n³` if `|S∩T| = 0` (from (3.1), see `LocalKernel`);
* `p_e(S) = 0` unless `e ⊆ S`, `|p_e(S)| ≤ π`;
* `x_e = Σ_(T ∋ e) z_T`, `|x_e| ≤ xmax`.
Then for `|S| = 3`: `|w_S| ≤ L(3Dc² + Dc³/3) a/n² + 6π(xmax + θ a)`. -/
theorem coeff_bound (z : Finset V → ℝ)
    (hz3 : ∀ T, z T ≠ 0 → T.card = 3) {a : ℝ}
    (hcong : ∀ v, ∑ T ∈ univ.filter (fun T => v ∈ T), |z T| ≤ a)
    (α : Finset V → ℝ) (hα1 : ∀ T, z T ≠ 0 → 1 ≤ α T) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hαθ : ∀ T, z T ≠ 0 → |1 / α T - 1| ≤ θ)
    (β : Sym2 V → ℝ) (hβ : ∀ e, |β e| ≤ 2)
    {L Dc : ℝ} (hL : 0 ≤ L) (hDc : 0 ≤ Dc) (cbar : Finset V → Finset V → ℝ)
    (hc2 : ∀ T S, z T ≠ 0 → 2 ≤ (S ∩ T).card → cbar T S = 0)
    (hc1 : ∀ T S, z T ≠ 0 → (S ∩ T).card = 1 →
      |cbar T S| ≤ L * Dc ^ 2 / (Fintype.card V : ℝ) ^ 2)
    (hc0 : ∀ T S, z T ≠ 0 → (S ∩ T).card = 0 →
      |cbar T S| ≤ L * Dc ^ 3 / (Fintype.card V : ℝ) ^ 3)
    (p : Sym2 V → Finset V → ℝ) {π : ℝ}
    (hp0 : ∀ e S, e ∉ edgesOf S → p e S = 0) (hpπ : ∀ e S, |p e S| ≤ π)
    (x : Sym2 V → ℝ) (hx : ∀ e, x e = ∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T)
    {xmax : ℝ} (hxmax : ∀ e, |x e| ≤ xmax)
    (S : Finset V) (hS : S.card = 3) :
    |∑ T, (z T / α T) * cbar T S +
        ∑ e, β e * (∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T / α T) * p e S| ≤
      L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / (Fintype.card V : ℝ) ^ 2 +
        6 * π * (xmax + θ * a) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hW : Nonempty V := by
    obtain ⟨v, -⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
    exact ⟨v⟩
  obtain ⟨v₀⟩ := hW
  have ha0 : 0 ≤ a := le_trans (Finset.sum_nonneg fun T _ => abs_nonneg _) (hcong v₀)
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos_iff.2 ⟨v₀⟩
  have hπ0 : 0 ≤ π := le_trans (abs_nonneg _) (hpπ s(v₀, v₀) ∅)
  have hmass : ∑ T, |z T| ≤ n * a / 3 := by
    have h := sum_mul_card_inter (fun T => |z T|) univ
    have hlhs : ∑ T, |z T| * ((univ ∩ T).card : ℝ) = 3 * ∑ T, |z T| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hzT : z T = 0
      · simp [hzT]
      · rw [Finset.univ_inter, hz3 T hzT]; push_cast; ring
    have hrhs : ∑ v ∈ (univ : Finset V), ∑ T ∈ univ.filter (fun T => v ∈ T), |z T| ≤ n * a := by
      calc _ ≤ ∑ _v ∈ (univ : Finset V), a := Finset.sum_le_sum fun v _ => hcong v
        _ = n * a := by rw [sum_const, card_univ, nsmul_eq_mul]
    linarith
  have hmassS : ∑ T, |z T| * ((S ∩ T).card : ℝ) ≤ 3 * a := by
    rw [sum_mul_card_inter (fun T => |z T|) S]
    calc _ ≤ ∑ _v ∈ S, a := Finset.sum_le_sum fun v _ => hcong v
      _ = 3 * a := by rw [sum_const, hS, nsmul_eq_mul]; norm_num
  have hpt : ∀ T, |z T / α T * cbar T S| ≤
      |z T| * (L * Dc ^ 3 / n ^ 3 + L * Dc ^ 2 / n ^ 2 * ((S ∩ T).card : ℝ)) := by
    intro T
    by_cases hzT : z T = 0
    · simp [hzT]
    rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le one_pos (hα1 T hzT))]
    have hzα : |z T| / α T ≤ |z T| := div_le_self (abs_nonneg _) (hα1 T hzT)
    have hb : |cbar T S| ≤ L * Dc ^ 3 / n ^ 3 + L * Dc ^ 2 / n ^ 2 * ((S ∩ T).card : ℝ) := by
      have h3 : 0 ≤ L * Dc ^ 3 / n ^ 3 := by positivity
      have h2 : 0 ≤ L * Dc ^ 2 / n ^ 2 := by positivity
      rcases Nat.lt_or_ge (S ∩ T).card 2 with hlt | hge
      · interval_cases hk : (S ∩ T).card
        · have := hc0 T S hzT hk; push_cast; linarith
        · have := hc1 T S hzT hk; push_cast; linarith
      · rw [hc2 T S hzT hge, abs_zero]; positivity
    calc |z T| / α T * |cbar T S| ≤ |z T| * |cbar T S| :=
          mul_le_mul_of_nonneg_right hzα (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have hterm1 : |∑ T, (z T / α T) * cbar T S| ≤ L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / n ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun T _ => hpt T).trans ?_
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have e2 : ∑ T, |z T| * (L * Dc ^ 2 / n ^ 2 * ((S ∩ T).card : ℝ)) =
        L * Dc ^ 2 / n ^ 2 * ∑ T, |z T| * ((S ∩ T).card : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun T _ => by ring
    rw [e2]
    have h3 : 0 ≤ L * Dc ^ 3 / n ^ 3 := by positivity
    have h2 : 0 ≤ L * Dc ^ 2 / n ^ 2 := by positivity
    have b1 := mul_le_mul_of_nonneg_left hmass h3
    have b2 := mul_le_mul_of_nonneg_left hmassS h2
    have : (∑ T, |z T|) * (L * Dc ^ 3 / n ^ 3) ≤ L * Dc ^ 3 / n ^ 3 * (n * a / 3) := by
      rw [mul_comm]; exact b1
    have heq : L * Dc ^ 3 / n ^ 3 * (n * a / 3) + L * Dc ^ 2 / n ^ 2 * (3 * a) =
        L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / n ^ 2 := by
      field_simp; ring
    have heq' : (L * (3 * Dc ^ 2) + L * (Dc ^ 3 / 3)) * a / n ^ 2 =
        L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / n ^ 2 := by ring
    linarith
  have hh : ∀ e ∈ edgesOf S,
      |∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T / α T| ≤ xmax + θ * a := by
    intro e he
    have hdiff : ∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T / α T =
        x e + ∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T * (1 / α T - 1) := by
      rw [hx e, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hdiff]
    refine (abs_add_le _ _).trans (add_le_add (hxmax e) ?_)
    induction e using Sym2.ind with
    | _ u v =>
    calc |∑ T ∈ univ.filter (fun T => s(u, v) ∈ edgesOf T), z T * (1 / α T - 1)|
        ≤ ∑ T ∈ univ.filter (fun T => s(u, v) ∈ edgesOf T), |z T| * θ := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T _ => ?_)
          by_cases hzT : z T = 0
          · simp [hzT]
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hαθ T hzT) (abs_nonneg _)
      _ ≤ ∑ T ∈ univ.filter (fun T => u ∈ T), |z T| * θ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun T _ _ => by positivity
          intro T hT
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgesOf,
            Finset.mk_mem_sym2_iff] at hT ⊢
          exact hT.1.1
      _ = θ * ∑ T ∈ univ.filter (fun T => u ∈ T), |z T| := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun T _ => by ring
      _ ≤ θ * a := mul_le_mul_of_nonneg_left (hcong u) hθ0
  have hterm2 : |∑ e, β e * (∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T / α T) * p e S| ≤
      6 * π * (xmax + θ * a) := by
    rw [← Finset.sum_subset (Finset.subset_univ (edgesOf S)) (fun e _ he => by
      rw [hp0 e S he, mul_zero])]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ edgesOf S, |β e * (∑ T ∈ univ.filter (fun T => e ∈ edgesOf T), z T / α T) * p e S|
        ≤ ∑ _e ∈ edgesOf S, 2 * (xmax + θ * a) * π := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, abs_mul]
          have h1 := hh e he
          have h0 : 0 ≤ xmax + θ * a := le_trans (abs_nonneg _) h1
          exact mul_le_mul (mul_le_mul (hβ e) h1 (abs_nonneg _) (by norm_num)) (hpπ e S)
            (abs_nonneg _) (by positivity)
      _ = 6 * π * (xmax + θ * a) := by
          rw [sum_const, card_edgesOf, hS, nsmul_eq_mul]; norm_num; ring
  exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)

/-! ## Bounds on `α`, `β`, `p` from the third-vertex degrees -/

/-- From `d ≥ n/C` and `n ≥ 2C`: `d ≥ 2`, `d/(d−1) ≤ 2`, `1/(d−1) ≤ 2C/n`, `1/d ≤ C/n`. -/
lemma degree_consequences {n C : ℝ} (hC : 0 < C) (hn : 2 * C ≤ n) {d : ℝ} (hd : n / C ≤ d) :
    2 ≤ d ∧ d / (d - 1) ≤ 2 ∧ 1 / (d - 1) ≤ 2 * C / n ∧ 1 / d ≤ C / n := by
  have hn0 : 0 < n := by linarith
  have hnC : 2 ≤ n / C := by rw [le_div_iff₀ hC]; linarith
  have hd2 : 2 ≤ d := le_trans hnC hd
  refine ⟨hd2, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by linarith) hn0]
    have : n ≤ C * d := by rwa [div_le_iff₀' hC] at hd
    nlinarith
  · rw [div_le_div_iff₀ (by linarith) hn0]
    have : n ≤ C * d := by rwa [div_le_iff₀' hC] at hd
    linarith

/-- `|1/α − 1| ≤ α − 1` for `α ≥ 1`. -/
lemma abs_inv_sub_one_le {α : ℝ} (hα : 1 ≤ α) : |1 / α - 1| ≤ α - 1 := by
  have hα0 : 0 < α := by linarith
  rw [abs_of_nonpos (by rw [sub_nonpos, div_le_one hα0]; exact hα)]
  rw [show -(1 / α - 1) = (α - 1) / α by field_simp; ring]
  exact div_le_self (by linarith) hα

/-- Degree hypothesis: every edge of every permitted triangle has `≥ n/C` permitted thirds. -/
def DegreeCond (Tri : Finset (Finset V)) (C : ℝ) : Prop :=
  ∀ T ∈ Tri, ∀ e ∈ edgesOf T, (Fintype.card V : ℝ) / C ≤ ((triOn Tri e).card : ℝ)

lemma two_le_card_triOn {Tri : Finset (Finset V)} {C : ℝ} (hC : 0 < C)
    (hn : 2 * C ≤ (Fintype.card V : ℝ)) (hdeg : DegreeCond Tri C) {T : Finset V}
    (hT : T ∈ Tri) {e : Sym2 V} (he : e ∈ edgesOf T) : 2 ≤ (triOn Tri e).card := by
  have := (degree_consequences hC hn (hdeg T hT e he)).1
  exact_mod_cast this

/-- `0 ≤ α_T − 1 ≤ 6C/n` for a permitted triangle (three edges, each `d_e ≥ n/C`). -/
lemma alpha_sub_one_le {Tri : Finset (Finset V)} {C : ℝ} (hC : 0 < C)
    (hn : 2 * C ≤ (Fintype.card V : ℝ)) (hdeg : DegreeCond Tri C) {T : Finset V}
    (hT : T ∈ Tri) (h3 : T.card = 3) :
    alphaT (edgesOf T) (triOn Tri) - 1 ≤ 6 * C / (Fintype.card V : ℝ) := by
  unfold alphaT
  have hb : ∀ e ∈ edgesOf T, 1 / (((triOn Tri e).card : ℝ) - 1) ≤
      2 * C / (Fintype.card V : ℝ) := fun e he =>
    (degree_consequences hC hn (hdeg T hT e he)).2.2.1
  have := Finset.sum_le_sum hb
  rw [sum_const, card_edgesOf, h3, nsmul_eq_mul] at this
  have e6 : ((Nat.choose 3 2 : ℕ) : ℝ) * (2 * C / (Fintype.card V : ℝ)) =
      6 * C / (Fintype.card V : ℝ) := by norm_num; ring
  linarith

/-- `|β_e| ≤ 2` for every edge (if no permitted triangle contains `e`, `β_e = 0`). -/
lemma abs_beta_le {Tri : Finset (Finset V)} {C : ℝ} (hC : 0 < C)
    (hn : 2 * C ≤ (Fintype.card V : ℝ)) (hdeg : DegreeCond Tri C) (e : Sym2 V) :
    |betaE (triOn Tri e)| ≤ 2 := by
  by_cases h : (triOn Tri e).Nonempty
  · obtain ⟨T, hT⟩ := h
    rw [mem_triOn] at hT
    obtain ⟨h2, hb, -, -⟩ := degree_consequences hC hn (hdeg T hT.1 e hT.2)
    unfold betaE
    rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
    exact hb
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [betaE, h]

/-- `0 ≤ p_e(S) ≤ C/n` for every edge and every `S`. -/
lemma abs_unifVec_le {Tri : Finset (Finset V)} {C : ℝ} (hC : 0 < C)
    (hn : 2 * C ≤ (Fintype.card V : ℝ)) (hdeg : DegreeCond Tri C) (e : Sym2 V)
    (S : Finset V) : |unifVec (triOn Tri e) S| ≤ C / (Fintype.card V : ℝ) := by
  have hn0 : 0 < (Fintype.card V : ℝ) := by linarith
  unfold unifVec
  split_ifs with hS
  · have hS' := hS
    rw [mem_triOn] at hS'
    obtain ⟨h2, -, -, hp⟩ := degree_consequences hC hn (hdeg S hS'.1 e hS'.2)
    rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact hp
  · simp only [abs_zero]; positivity

omit [Fintype V] in
lemma unifVec_eq_zero {Tri : Finset (Finset V)} {e : Sym2 V} {S : Finset V}
    (h : e ∉ edgesOf S) : unifVec (triOn Tri e) S = 0 := by
  unfold unifVec
  rw [if_neg]
  rw [mem_triOn]
  exact fun h' => h h'.2

/-- **Assembly (1.2) from (2.1).** With `π = C/n`, `θ = 6C/n` and `a ≤ (3K/2) n · xmax`,
the estimate of `coeff_bound` is `≤ K∞ · xmax / n`,
`K∞ = 6C + (3K/2)(L(3Dc² + Dc³/3) + 36C²)`. -/
lemma sup_bound_assembly {n C K L Dc a xmax : ℝ} (hn : 0 < n)
    (hL : 0 ≤ L) (hDc : 0 ≤ Dc) (ha : a ≤ 3 * K / 2 * n * xmax) :
    L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / n ^ 2 + 6 * (C / n) * (xmax + 6 * C / n * a) ≤
      (6 * C + 3 * K / 2 * (L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2)) * xmax / n := by
  have hP : 0 ≤ L * (3 * Dc ^ 2 + Dc ^ 3 / 3) := by positivity
  have key : L * (3 * Dc ^ 2 + Dc ^ 3 / 3) * a / n ^ 2 + 6 * (C / n) * (xmax + 6 * C / n * a) =
      (6 * C * xmax + (L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2) * (a / n)) / n := by
    field_simp; ring
  rw [key, div_le_div_iff_of_pos_right hn]
  have han : a / n ≤ 3 * K / 2 * xmax := by
    rw [div_le_iff₀ hn]; linarith
  have hQ : 0 ≤ L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left han hQ]

end S10V22
