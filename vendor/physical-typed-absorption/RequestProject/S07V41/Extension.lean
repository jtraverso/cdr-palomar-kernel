/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V41.Solver
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V41 §2 — uniform bounded functional extension through an actual physical quotient

Fixed parameters `d D E R : ℕ`. There is `B0 ≥ 0` depending only on `(d, D, E, R)` such that
for every `A ≥ 0`, every finite edge type `X`, actual integer submodules `M0 ≤ M1`, `L` of
`X → ℤ`, an integer-linear `q : M1 → ℤ^d` with `ker q ⊆ L` and `|q(x)_i| ≤ D‖x‖₁`, a set `S`
of columns with coordinates in `[-E, E]` whose integer span is `q(L ∩ M1)`, a generating set
`B ⊆ M0` (no bound on `|B|`) with `‖b‖₁ ≤ R`, and an integer-linear `f : M0 → ℝ` with
`|f x| ≤ A‖x‖₁` killing `M0 ∩ L`, there is an integer-linear `f0 : M1 → ℝ` extending `f`,
killing `L`, and satisfying `|f0 x| ≤ B0 * A * ‖x‖₁` on ALL of `M1`
(`uniform_bounded_extension`; integer-valued input: `uniform_bounded_extension_int`).

No saturation, rank, index or class-count hypothesis is used. The hypothesis `L ≤ M1` of
the informal statement is not needed: `q(L)` is read as the image of `L ∩ M1` (which is `L`
when `L ≤ M1`). `B ⊆ M0` is implied by `span B = M0` and is therefore not stated.

Proof: rows `q(b)` (`b ∈ B`) and `s ∈ S` all lie in the box `[-(DR+E), DR+E]^d`; the
right-hand sides `f(b)` and `0` are proved compatible with every integer relation among the
rows (`relCompat_rows`), so the uniform solver `bounded_solver` yields `u`, and
`f0 x = ∑ i, u i * q(x)_i`.
-/

open Finset

noncomputable section

namespace S07V41

/-- Integer `ℓ¹` norm of an edge vector. -/
def zl1 {X : Type*} [Fintype X] (x : X → ℤ) : ℤ := ∑ e, |x e|

lemma zl1_nonneg {X : Type*} [Fintype X] (x : X → ℤ) : 0 ≤ zl1 x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp] lemma zl1_zero {X : Type*} [Fintype X] : zl1 (0 : X → ℤ) = 0 := by simp [zl1]

/-- `dotZ u` as an integer-linear map. -/
def dotZL {d : ℕ} (u : Fin d → ℝ) : (Fin d → ℤ) →ₗ[ℤ] ℝ where
  toFun t := dotZ u t
  map_add' t t' := by simp [dotZ, mul_add, Finset.sum_add_distrib]
  map_smul' n t := by
    simp only [dotZ, Pi.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast, Int.cast_id]
    rw [zsmul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma dotZL_apply {d : ℕ} (u : Fin d → ℝ) (t : Fin d → ℤ) : dotZL u t = dotZ u t := rfl

section Setup

variable {d : ℕ} {X : Type*} [Fintype X] {M0 M1 L : Submodule ℤ (X → ℤ)} (hM : M0 ≤ M1)
  (q : M1 →ₗ[ℤ] (Fin d → ℤ)) (S : Set (Fin d → ℤ)) (Bgen : Set (X → ℤ)) (f : M0 →ₗ[ℤ] ℝ)

/-- **Consistency core.** If `ker q ⊆ L`, `q(L ∩ M1) = span S` and `f` kills `M0 ∩ L`, then
`f x = 0` whenever `q x ∈ span S`. -/
theorem f_eq_zero_of_q_mem (hker : ∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L)
    (hqL : (L.comap M1.subtype).map q = Submodule.span ℤ S)
    (hfL : ∀ x : M0, (x : X → ℤ) ∈ L → f x = 0)
    (x : M0) (hx : q (Submodule.inclusion hM x) ∈ Submodule.span ℤ S) : f x = 0 := by
  rw [← hqL] at hx
  obtain ⟨l, hl, heq⟩ := hx
  have hl' : (l : X → ℤ) ∈ L := hl
  have h0 : q (Submodule.inclusion hM x - l) = 0 := by rw [map_sub, heq, sub_self]
  have h1 := hker _ h0
  apply hfL
  have : (x : X → ℤ) = ((Submodule.inclusion hM x - l : M1) : X → ℤ) + (l : X → ℤ) := by
    simp
  rw [this]
  exact L.add_mem h1 hl'

/-- The generator chosen to represent a row `t` (or `0` if `t` is not of the form `q b`). -/
def genOf (t : Fin d → ℤ) : M0 := by
  classical
  exact if h : ∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t then h.choose
    else 0

omit [Fintype X] in
lemma genOf_spec {t : Fin d → ℤ}
    (h : ∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t) :
    ((genOf hM q Bgen t : M0) : X → ℤ) ∈ Bgen ∧
      q (Submodule.inclusion hM (genOf hM q Bgen t)) = t := by
  classical
  unfold genOf
  rw [dif_pos h]
  exact h.choose_spec

omit [Fintype X] in
lemma genOf_neg {t : Fin d → ℤ}
    (h : ¬ ∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t) :
    genOf hM q Bgen t = 0 := by
  classical
  unfold genOf
  rw [dif_neg h]

/-- The row predicate: `t = q b` for a generator `b`, or `t ∈ S`. -/
def IsRow (t : Fin d → ℤ) : Prop :=
  (∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t) ∨ t ∈ S

omit [Fintype X] in
/-- Every row differs from the image of its chosen generator by an element of `span S`. -/
lemma row_sub_mem {t : Fin d → ℤ} (ht : IsRow hM q S Bgen t) :
    t - q (Submodule.inclusion hM (genOf hM q Bgen t)) ∈ Submodule.span ℤ S := by
  by_cases h : ∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t
  · rw [(genOf_spec hM q Bgen h).2, sub_self]; exact Submodule.zero_mem _
  · rw [genOf_neg hM q Bgen h, map_zero, map_zero, sub_zero]
    exact Submodule.subset_span (ht.resolve_left h)

lemma zl1_genOf_le {R : ℕ} (hBR : ∀ b ∈ Bgen, zl1 b ≤ R) (t : Fin d → ℤ) :
    zl1 ((genOf hM q Bgen t : M0) : X → ℤ) ≤ R := by
  by_cases h : ∃ x : M0, (x : X → ℤ) ∈ Bgen ∧ q (Submodule.inclusion hM x) = t
  · exact hBR _ (genOf_spec hM q Bgen h).1
  · rw [genOf_neg hM q Bgen h]; simp

/-- **Compatibility of the row system, proved.** For every finite set `T` of rows, every
integer relation among the rows annihilates the right-hand sides `f (genOf t)`. -/
theorem relCompat_rows (hker : ∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L)
    (hqL : (L.comap M1.subtype).map q = Submodule.span ℤ S)
    (hfL : ∀ x : M0, (x : X → ℤ) ∈ L → f x = 0)
    (T : Finset (Fin d → ℤ)) (hT : ∀ t ∈ T, IsRow hM q S Bgen t) :
    RelCompat T (fun t => f (genOf hM q Bgen t)) := by
  intro z hz
  set y : M0 := ∑ t : T, z t • genOf hM q Bgen (t : Fin d → ℤ) with hy
  have hfy : f y = ∑ t : T, (z t : ℝ) * f (genOf hM q Bgen (t : Fin d → ℤ)) := by
    rw [hy, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_zsmul, zsmul_eq_mul]
  rw [← hfy]
  apply f_eq_zero_of_q_mem hM q S f hker hqL hfL
  have hqy : q (Submodule.inclusion hM y) =
      -∑ t : T, z t • ((t : Fin d → ℤ) - q (Submodule.inclusion hM
        (genOf hM q Bgen (t : Fin d → ℤ)))) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hz, zero_sub, neg_neg, hy, map_sum,
      map_zsmul]
  rw [hqy]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ =>
    Submodule.smul_mem _ _ (row_sub_mem hM q S Bgen (hT t t.2)))

end Setup

/-- **Uniform bounded functional extension through an actual physical quotient.**
The constant `B0` depends only on `(d, D, E, R)`, and it is fixed BEFORE `A`, the edge type
`X`, the submodules, `q`, `S`, the generating set `B` (of arbitrary cardinality) and `f`. -/
theorem uniform_bounded_extension (d D E R : ℕ) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ (A : ℝ), 0 ≤ A →
    ∀ (X : Type) [Fintype X] (M0 M1 L : Submodule ℤ (X → ℤ)) (hM : M0 ≤ M1)
      (q : M1 →ₗ[ℤ] (Fin d → ℤ)) (S : Set (Fin d → ℤ)) (Bgen : Set (X → ℤ))
      (f : M0 →ₗ[ℤ] ℝ),
      (∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L) →
      (∀ x : M1, ∀ i, |q x i| ≤ (D : ℤ) * zl1 (x : X → ℤ)) →
      (∀ s ∈ S, ∀ i, |s i| ≤ (E : ℤ)) →
      (L.comap M1.subtype).map q = Submodule.span ℤ S →
      Submodule.span ℤ Bgen = M0 → (∀ b ∈ Bgen, zl1 b ≤ R) →
      (∀ x : M0, |f x| ≤ A * zl1 (x : X → ℤ)) →
      (∀ x : M0, (x : X → ℤ) ∈ L → f x = 0) →
      ∃ f0 : M1 →ₗ[ℤ] ℝ, (∀ x : M0, f0 (Submodule.inclusion hM x) = f x) ∧
        (∀ x : M1, (x : X → ℤ) ∈ L → f0 x = 0) ∧
        ∀ x : M1, |f0 x| ≤ B0 * A * zl1 (x : X → ℤ) := by
  classical
  obtain ⟨C, hC0, hC⟩ := bounded_solver d ((D : ℤ) * R + E)
  refine ⟨d * C * R * D, by positivity, ?_⟩
  intro A hA X _ M0 M1 L hM q S Bgen f hker hqb hSE hqL hBspan hBR hfA hfL
  -- the finite row set
  let T : Finset (Fin d → ℤ) :=
    (rowBox d ((D : ℤ) * R + E)).filter (fun t => IsRow hM q S Bgen t)
  have hrow_box : ∀ t, IsRow hM q S Bgen t → ∀ i, |t i| ≤ (D : ℤ) * R + E := by
    rintro t (⟨x, hxB, rfl⟩ | hs) i
    · have h1 := hqb (Submodule.inclusion hM x) i
      have h2 : zl1 ((Submodule.inclusion hM x : M1) : X → ℤ) ≤ R := hBR _ hxB
      have hE : (0 : ℤ) ≤ E := by positivity
      nlinarith [zl1_nonneg ((Submodule.inclusion hM x : M1) : X → ℤ)]
    · have := hSE t hs i
      have hDR : (0 : ℤ) ≤ D * R := by positivity
      linarith
  have memT : ∀ t, t ∈ T ↔ IsRow hM q S Bgen t := fun t => by
    simp only [T, Finset.mem_filter, mem_rowBox]
    exact ⟨fun h => h.2, fun h => ⟨hrow_box t h, h⟩⟩
  -- solve
  have hbnd : ∀ t ∈ T, |f (genOf hM q Bgen t)| ≤ A * R := fun t _ => by
    refine (hfA _).trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact_mod_cast zl1_genOf_le hM q Bgen hBR t
  obtain ⟨u, hu, hub⟩ := hC T (fun t ht i => hrow_box t ((memT t).1 ht) i)
    (fun t => f (genOf hM q Bgen t)) (A * R) (by positivity) hbnd
    (relCompat_rows hM q S Bgen f hker hqL hfL T fun t ht => (memT t).1 ht)
  have key := f_eq_zero_of_q_mem hM q S f hker hqL hfL
  refine ⟨(dotZL u).comp q, ?_, ?_, ?_⟩
  · -- extension: agree on generators, then on their span
    subst hBspan
    have hext : (dotZL u).comp (q.comp (Submodule.inclusion hM)) = f := by
      refine LinearMap.ext_on (Submodule.span_span_coe_preimage (R := ℤ) (s := Bgen)) ?_
      intro x hx
      have hxB : (x : X → ℤ) ∈ Bgen := hx
      set t := q (Submodule.inclusion hM x)
      have hex : ∃ x' : (Submodule.span ℤ Bgen), (x' : X → ℤ) ∈ Bgen ∧
          q (Submodule.inclusion hM x') = t := ⟨x, hxB, rfl⟩
      have hsol := hu t ((memT t).2 (Or.inl hex))
      simp only [LinearMap.coe_comp, Function.comp_apply, dotZL_apply]
      rw [hsol]
      have hdiff := key (x - genOf hM q Bgen t) (by
        rw [map_sub, map_sub, (genOf_spec hM q Bgen hex).2, sub_self]
        exact Submodule.zero_mem _)
      rw [map_sub, sub_eq_zero] at hdiff
      exact hdiff.symm
    intro x
    exact LinearMap.congr_fun hext x
  · -- kills `L`
    intro x hxL
    have hqx : q x ∈ Submodule.span ℤ S := by
      rw [← hqL]; exact ⟨x, hxL, rfl⟩
    show dotZL u (q x) = 0
    have hle : Submodule.span ℤ S ≤ LinearMap.ker (dotZL u) := by
      rw [Submodule.span_le]
      intro s hs
      have hsT : IsRow hM q S Bgen s := Or.inr hs
      simp only [SetLike.mem_coe, LinearMap.mem_ker, dotZL_apply]
      rw [hu s ((memT s).2 hsT)]
      apply key
      have h1 := row_sub_mem hM q S Bgen hsT
      have h2 : s ∈ Submodule.span ℤ S := Submodule.subset_span hs
      have := Submodule.sub_mem _ h2 h1
      simpa using this
    exact hle hqx
  · -- the uniform bound
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, dotZL_apply, dotZ]
    have hl := zl1_nonneg (x : X → ℤ)
    calc |∑ i, u i * (q x i : ℝ)| ≤ ∑ i, |u i * (q x i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (C * (A * R)) * (D * (zl1 (x : X → ℤ) : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have h1 : |(q x i : ℝ)| ≤ D * (zl1 (x : X → ℤ) : ℝ) := by
            have := hqb x i
            rw [← Int.cast_abs]; exact_mod_cast this
          exact mul_le_mul (hub i) h1 (abs_nonneg _) (by positivity)
      _ = d * C * R * D * A * zl1 (x : X → ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Integer-valued input.** The same uniform constant serves an integer-valued `f`; the
extension `f0` is real-valued (an integer-valued bounded extension need not exist). -/
theorem uniform_bounded_extension_int (d D E R : ℕ) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ (A : ℝ), 0 ≤ A →
    ∀ (X : Type) [Fintype X] (M0 M1 L : Submodule ℤ (X → ℤ)) (hM : M0 ≤ M1)
      (q : M1 →ₗ[ℤ] (Fin d → ℤ)) (S : Set (Fin d → ℤ)) (Bgen : Set (X → ℤ))
      (f : M0 →ₗ[ℤ] ℤ),
      (∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L) →
      (∀ x : M1, ∀ i, |q x i| ≤ (D : ℤ) * zl1 (x : X → ℤ)) →
      (∀ s ∈ S, ∀ i, |s i| ≤ (E : ℤ)) →
      (L.comap M1.subtype).map q = Submodule.span ℤ S →
      Submodule.span ℤ Bgen = M0 → (∀ b ∈ Bgen, zl1 b ≤ R) →
      (∀ x : M0, |(f x : ℝ)| ≤ A * zl1 (x : X → ℤ)) →
      (∀ x : M0, (x : X → ℤ) ∈ L → f x = 0) →
      ∃ f0 : M1 →ₗ[ℤ] ℝ, (∀ x : M0, f0 (Submodule.inclusion hM x) = f x) ∧
        (∀ x : M1, (x : X → ℤ) ∈ L → f0 x = 0) ∧
        ∀ x : M1, |f0 x| ≤ B0 * A * zl1 (x : X → ℤ) := by
  obtain ⟨B0, hB0, h⟩ := uniform_bounded_extension d D E R
  refine ⟨B0, hB0, fun A hA X _ M0 M1 L hM q S Bgen f hker hqb hSE hqL hBspan hBR hfA hfL =>
    ?_⟩
  let fR : M0 →ₗ[ℤ] ℝ := (Int.castAddHom ℝ).toIntLinearMap.comp f
  obtain ⟨f0, h1, h2, h3⟩ := h A hA X M0 M1 L hM q S Bgen fR hker hqb hSE hqL hBspan hBR
    (fun x => hfA x) (fun x hx => by simp [fR, hfL x hx])
  exact ⟨f0, fun x => by rw [h1]; rfl, h2, h3⟩

end S07V41
