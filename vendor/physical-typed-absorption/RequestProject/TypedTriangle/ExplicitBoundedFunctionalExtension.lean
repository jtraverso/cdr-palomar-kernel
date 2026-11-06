module
public import RequestProject.TypedTriangle.ExplicitBoundedSolver
public import RequestProject.S07V41.Extension
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V41.Explicit

def extensionCost (d D E R : ℕ) : ℝ := (d:ℝ)*solverCost d ((D:ℤ)*R+E)*(R:ℝ)*(D:ℝ)

theorem extensionCost_nonneg (d D E R : ℕ) : 0 ≤ extensionCost d D E R := by
  have hC := solverCost_nonneg d ((D:ℤ)*R+E)
  unfold extensionCost
  positivity

theorem uniform_bounded_extension_explicit (d D E R : ℕ) :
    ∀ (A : ℝ), 0  ≤  A →
    ∀ (X : Type) [Fintype X] (M0 M1 L : Submodule ℤ (X → ℤ)) (hM : M0  ≤  M1)
      (q : M1 →ₗ[ℤ] (Fin d → ℤ)) (S : Set (Fin d → ℤ)) (Bgen : Set (X → ℤ))
      (f : M0 →ₗ[ℤ] ℝ),
      (∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L) →
      (∀ x : M1, ∀ i, |q x i|  ≤  (D : ℤ) * zl1 (x : X → ℤ)) →
      (∀ s ∈ S, ∀ i, |s i|  ≤  (E : ℤ)) →
      (L.comap M1.subtype).map q = Submodule.span ℤ S →
      Submodule.span ℤ Bgen = M0 → (∀ b ∈ Bgen, zl1 b  ≤  R) →
      (∀ x : M0, |f x|  ≤  A * zl1 (x : X → ℤ)) →
      (∀ x : M0, (x : X → ℤ) ∈ L → f x = 0) →
      ∃ f0 : M1 →ₗ[ℤ] ℝ, (∀ x : M0, f0 (Submodule.inclusion hM x) = f x) ∧
        (∀ x : M1, (x : X → ℤ) ∈ L → f0 x = 0) ∧
        ∀ x : M1, |f0 x|  ≤  extensionCost d D E R * A * zl1 (x : X → ℤ) := by
  classical
  let C := solverCost d ((D:ℤ)*R+E)
  have hC0 : 0 ≤ C := solverCost_nonneg d ((D:ℤ)*R+E)
  intro A hA X _ M0 M1 L hM q S Bgen f hker hqb hSE hqL hBspan hBR hfA hfL
  -- the finite row set
  let T : Finset (Fin d → ℤ) :=
    (rowBox d ((D : ℤ) * R + E)).filter (fun t => IsRow hM q S Bgen t)
  have hrow_box : ∀ t, IsRow hM q S Bgen t → ∀ i, |t i|  ≤  (D : ℤ) * R + E := by
    rintro t (⟨x, hxB, rfl⟩ | hs) i
    · have h1 := hqb (Submodule.inclusion hM x) i
      have h2 : zl1 ((Submodule.inclusion hM x : M1) : X → ℤ)  ≤  R := hBR _ hxB
      have hE : (0 : ℤ)  ≤  E := by positivity
      nlinarith [zl1_nonneg ((Submodule.inclusion hM x : M1) : X → ℤ)]
    · have := hSE t hs i
      have hDR : (0 : ℤ)  ≤  D * R := by positivity
      linarith
  have memT : ∀ t, t ∈ T ↔ IsRow hM q S Bgen t := fun t => by
    simp only [T, Finset.mem_filter, mem_rowBox]
    exact ⟨fun h => h.2, fun h => ⟨hrow_box t h, h⟩⟩
  -- solve
  have hbnd : ∀ t ∈ T, |f (genOf hM q Bgen t)|  ≤  A * R := fun t _ => by
    refine (hfA _).trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact_mod_cast zl1_genOf_le hM q Bgen hBR t
  obtain ⟨u, hu, hub⟩ := bounded_solver_explicit d ((D:ℤ)*R+E) T (fun t ht i => hrow_box t ((memT t).1 ht) i)
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
    have hle : Submodule.span ℤ S  ≤  LinearMap.ker (dotZL u) := by
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
    calc |∑ i, u i * (q x i : ℝ)|  ≤  ∑ i, |u i * (q x i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _  ≤  ∑ _i : Fin d, (C * (A * R)) * (D * (zl1 (x : X → ℤ) : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have h1 : |(q x i : ℝ)|  ≤  D * (zl1 (x : X → ℤ) : ℝ) := by
            have := hqb x i
            rw [← Int.cast_abs]; exact_mod_cast this
          exact mul_le_mul (hub i) h1 (abs_nonneg _) (by positivity)
      _ = d * C * R * D * A * zl1 (x : X → ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


theorem uniform_bounded_extension_int_explicit (d D E R : ℕ) :
    ∀ (A : ℝ), 0  ≤  A →
    ∀ (X : Type) [Fintype X] (M0 M1 L : Submodule ℤ (X → ℤ)) (hM : M0  ≤  M1)
      (q : M1 →ₗ[ℤ] (Fin d → ℤ)) (S : Set (Fin d → ℤ)) (Bgen : Set (X → ℤ))
      (f : M0 →ₗ[ℤ] ℤ),
      (∀ x : M1, q x = 0 → (x : X → ℤ) ∈ L) →
      (∀ x : M1, ∀ i, |q x i|  ≤  (D : ℤ) * zl1 (x : X → ℤ)) →
      (∀ s ∈ S, ∀ i, |s i|  ≤  (E : ℤ)) →
      (L.comap M1.subtype).map q = Submodule.span ℤ S →
      Submodule.span ℤ Bgen = M0 → (∀ b ∈ Bgen, zl1 b  ≤  R) →
      (∀ x : M0, |(f x : ℝ)|  ≤  A * zl1 (x : X → ℤ)) →
      (∀ x : M0, (x : X → ℤ) ∈ L → f x = 0) →
      ∃ f0 : M1 →ₗ[ℤ] ℝ, (∀ x : M0, f0 (Submodule.inclusion hM x) = f x) ∧
        (∀ x : M1, (x : X → ℤ) ∈ L → f0 x = 0) ∧
        ∀ x : M1, |f0 x|  ≤  extensionCost d D E R * A * zl1 (x : X → ℤ) := by
  intro A hA X _ M0 M1 L hM q S Bgen f hker hqb hSE hqL hBspan hBR hfA hfL
  let fR : M0 →ₗ[ℤ] ℝ := (Int.castAddHom ℝ).toIntLinearMap.comp f
  obtain ⟨f0, h1, h2, h3⟩ := uniform_bounded_extension_explicit d D E R A hA X M0 M1 L hM q S Bgen fR hker hqb hSE hqL hBspan hBR
    (fun x => hfA x) (fun x hx => by simp [fR, hfL x hx])
  exact ⟨f0, fun x => by rw [h1]; rfl, h2, h3⟩


#print axioms uniform_bounded_extension_explicit
#print axioms uniform_bounded_extension_int_explicit
end S07V41.Explicit
