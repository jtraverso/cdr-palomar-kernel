/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S10.Realification
@[expose] public section

/-!
# V38 — the real kernel of an integer matrix is spanned by integer kernel vectors

Mathlib only (plus the S10 casting `S10V22.castV`). For an arbitrary finite integer matrix
`B : R → C → ℤ` (no rank, saturation or index hypothesis):

* `clear_den` — every rational vector is `1/D` times an integer vector, `D ≥ 1`;
* `intKer B` — the ACTUAL integer kernel `{z | ∀ r, ∑ c, B r c * z c = 0}`;
* `realKer_mem_span` — every real `x` with `∑ c, B r c * x c = 0` for all `r` lies in the
  real span of the casts of integer kernel vectors.

Proof of the rational-to-real step: the finitely many coordinates of `x` span a
finite-dimensional `ℚ`-subspace `S` of `ℝ`; choose a `ℚ`-basis `b` of `S`. The integer
equations are `ℚ`-linear in the coordinates, so each basis coordinate `y_k` of `x` is a
RATIONAL kernel vector, and `x = ∑ k, b k • y_k`. Denominators are then cleared.
-/

open Finset

noncomputable section

namespace S07V38

open S10V22

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The actual integer kernel of an integer matrix. -/
def intKer (B : R → C → ℤ) : Set (C → ℤ) := {z | ∀ r, ∑ c, B r c * z c = 0}

omit [Fintype R] in
/-- **Clearing denominators** of a rational vector. -/
theorem clear_den (y : C → ℚ) : ∃ (D : ℕ) (z : C → ℤ), 0 < D ∧ ∀ c, (z c : ℚ) = D * y c := by
  classical
  refine ⟨∏ c, (y c).den, fun c => (y c).num * (((∏ c', (y c').den) / (y c).den : ℕ) : ℤ),
    Finset.prod_pos fun c _ => (y c).den_pos, fun c => ?_⟩
  have hdvd : (y c).den ∣ ∏ c', (y c').den := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  have hden : ((y c).den : ℚ) ≠ 0 := by exact_mod_cast (y c).den_nz
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hden, Nat.cast_prod]
  conv_rhs => rw [← Rat.num_div_den (y c)]
  field_simp

omit [Fintype R] in
/-- **Real kernel = real span of the integer kernel.** For every finite integer matrix `B`,
every real solution of `B x = 0` is a real combination of casts of integer solutions. -/
theorem realKer_mem_span (B : R → C → ℤ) (x : C → ℝ)
    (hx : ∀ r, ∑ c, (B r c : ℝ) * x c = 0) :
    x ∈ Submodule.span ℝ (castV '' intKer B) := by
  classical
  set S : Submodule ℚ ℝ := Submodule.span ℚ (Set.range x) with hS
  haveI : FiniteDimensional ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  let b := Module.finBasis ℚ S
  have hxS : ∀ c, x c ∈ S := fun c => Submodule.subset_span ⟨c, rfl⟩
  let y : Fin (Module.finrank ℚ S) → C → ℚ := fun k c => b.repr ⟨x c, hxS c⟩ k
  -- coordinates
  have hxy : ∀ c, x c = ∑ k, (y k c : ℝ) * (b k : ℝ) := by
    intro c
    have h := b.sum_repr ⟨x c, hxS c⟩
    have h' := congrArg (fun s : S => (s : ℝ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Rat.smul_def]
  -- each coordinate is a rational kernel vector
  have hyker : ∀ k r, ∑ c, (B r c : ℚ) * y k c = 0 := by
    intro k r
    have h0 : ∑ c, B r c • (⟨x c, hxS c⟩ : S) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, ZeroMemClass.coe_zero]
      rw [← hx r]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Submodule.coe_smul_of_tower, zsmul_eq_mul]
    have h1 := congrArg (fun s => b.repr s k) h0
    simp only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [zsmul_eq_mul]
  -- clear denominators
  choose D z hD hz using fun k => clear_den (y k)
  have hzker : ∀ k, z k ∈ intKer B := by
    intro k r
    have : ((∑ c, B r c * z k c : ℤ) : ℚ) = 0 := by
      push_cast
      simp only [hz]
      rw [show ∑ c, (B r c : ℚ) * (D k * y k c) = D k * ∑ c, (B r c : ℚ) * y k c by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring]
      rw [hyker, mul_zero]
    exact_mod_cast this
  have hxeq : x = ∑ k, ((b k : ℝ) / D k) • castV (z k) := by
    funext c
    rw [hxy c, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hDk : (D k : ℝ) ≠ 0 := by exact_mod_cast (hD k).ne'
    have hzc : (z k c : ℝ) = D k * y k c := by exact_mod_cast hz k c
    simp only [Pi.smul_apply, castV, smul_eq_mul, hzc]
    field_simp
  rw [hxeq]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨z k, hzker k, rfl⟩)

end S07V38
