/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.RegularFactorizations

/-! # The sharp entropy lower bound for a fixed regular support -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n d : ℕ} {E : Finset (Fin n × Fin n)}

theorem factorization_covers (hE : Regular E d) (r : PartialFactorization E d)
    (v w : Fin n) (hvw : (v,w)∈E) : ∃! i : Fin d, r.1.1 i v=w := by
  have hinj : Function.Injective (fun i : Fin d => r.1.1 i v) := by
    intro i j he
    by_contra hij
    exact r.1.2 i j hij v he
  have hsub : univ.image (fun i : Fin d => r.1.1 i v) ⊆ rowSet E v := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨mem_univ _,r.2 i v⟩
  have heq : univ.image (fun i : Fin d => r.1.1 i v)=rowSet E v := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injective _ hinj,card_univ,Fintype.card_fin,hE.1]
  have hw : w ∈ univ.image (fun i : Fin d => r.1.1 i v) := by
    rw [heq]
    exact mem_filter.mpr ⟨mem_univ _,hvw⟩
  obtain ⟨i,_,hi⟩ := mem_image.mp hw
  exact ⟨i,hi,fun j hj => hinj (hj.trans hi.symm)⟩

theorem factorization_count_lower (hE : Regular E d) :
    (d.factorial:ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n)^d ≤
      Fintype.card (PartialFactorization E d) := by
  have hh := partial_factorization_count hE d le_rfl
  rw [prod_mul_distrib,prod_const,card_range,prod_pow] at hh
  have hfac : (∏ i ∈ range d, ((d-i:ℕ):ℝ)) = (d.factorial:ℝ) := by
    rw [← prod_range_reflect]
    have he : (∏ i ∈ range d, ((d-(d-1-i):ℕ):ℝ)) = ∏ i ∈ range d, ((i+1:ℕ):ℝ) := by
      apply prod_congr rfl
      intro i hi
      rw [mem_range] at hi
      congr 1
      omega
    rw [he,← Nat.cast_prod,prod_range_add_one_eq_factorial]
  rwa [hfac] at hh

theorem factorization_log_lower (hE : Regular E d) (hn : 0<n) (hd : 0<d) :
    0<Fintype.card (PartialFactorization E d) ∧
      (n:ℝ)*d*(Real.log d-2) ≤ Real.log (Fintype.card (PartialFactorization E d)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hnf : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hdf : (0:ℝ)<d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hpos : (0:ℝ)<(d.factorial:ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n)^d := by positivity
  have hbound := factorization_count_lower hE
  have hcard : 0<Fintype.card (PartialFactorization E d) := by
    exact_mod_cast (lt_of_lt_of_le hpos hbound)
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul (pow_pos hdf _).ne' (pow_pos (div_pos hnf (pow_pos hnR _)) _).ne',
    Real.log_pow,Real.log_pow,Real.log_div hnf.ne' (pow_pos hnR _).ne',Real.log_pow] at hlog
  have hf₁ := mul_le_mul_of_nonneg_left (_root_.STS.log_factorial_ge d) (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hf₂ := mul_le_mul_of_nonneg_left (_root_.STS.log_factorial_ge n) (Nat.cast_nonneg d : (0:ℝ)≤d)
  exact ⟨hcard,by nlinarith only [hlog,hf₁,hf₂]⟩

end CDRBicolour.KBicolor.PrescribedCounting
