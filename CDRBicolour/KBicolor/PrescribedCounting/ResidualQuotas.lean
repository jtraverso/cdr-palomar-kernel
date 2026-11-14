/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.QuotaDivision
public import CDRBicolour.KBicolor.TypeIdentities

/-! # Extract and split nonnegative exact quotas after the residual is fixed -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {k : ℕ}

theorem extract_residual_quotas (h : ℕ) (b : Fin k → ℕ)
    (r c t : Fin k → Fin k → ℕ)
    (hlow : ∀ i j, i ≠ j → r i j ≤ t i j)
    (hmod : ∀ i j, i ≠ j → (3 : ℤ) ∣ ((t i j : ℤ)-r i j))
    (hpair : ∀ i j, i ≠ j → t i j+t j i=(r i j+c i j)+(r j i+c j i))
    (hrow : ∀ i, (∑ j ∈ univ.filter (fun j => j ≠ i), t i j)=
      ∑ j ∈ univ.filter (fun j => j ≠ i), (r i j+c i j))
    (hcPair : ∀ i j, i ≠ j → c i j+c j i=3*(h*(b i*b j)))
    (hcRow : ∀ i, (∑ j ∈ univ.filter (fun j => j ≠ i), c i j)=3*(h*(b i*b i))) :
    ∃ y : Fin h → Fin k → Fin k → ℕ,
      (∀ o, Pattern.IsTour b (y o)) ∧
      ∀ i j, i ≠ j → r i j+∑ o, 3*y o i j=t i j := by
  let q : Fin k → Fin k → ℕ := fun i j => if i=j then 0 else t i j-r i j
  have hqdiag : ∀ i, q i i=0 := by intro i; simp [q]
  have hqadd : ∀ i j, i ≠ j → r i j+q i j=t i j := by
    intro i j hij
    simp only [q,ite_eq_right hij]
    exact Nat.add_sub_of_le (hlow i j hij)
  have hqdiv : ∀ i j, 3 ∣ q i j := by
    intro i j
    by_cases hij : i=j
    · subst j; simp [hqdiag]
    have hh := hmod i j hij
    have he : (q i j : ℤ)=(t i j : ℤ)-r i j := by
      dsimp only [q]
      rw [ite_eq_right hij,Nat.cast_sub (hlow i j hij)]
    rw [← he] at hh
    exact_mod_cast hh
  have hqpair : ∀ i j, i ≠ j → q i j+q j i=3*(h*(b i*b j)) := by
    intro i j hij
    have ha := hqadd i j hij
    have hb := hqadd j i hij.symm
    have hp := hpair i j hij
    have hc := hcPair i j hij
    omega
  have hqrow : ∀ i, ∑ j, q i j=3*(h*(b i*b i)) := by
    intro i
    have ha : (∑ j ∈ univ.filter (fun j => j ≠ i), r i j)+
        (∑ j ∈ univ.filter (fun j => j ≠ i), q i j)=
        ∑ j ∈ univ.filter (fun j => j ≠ i), t i j := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      exact hqadd i j (mem_filter.mp hj).2.symm
    have hrow' := hrow i
    rw [sum_add_distrib] at hrow'
    have hc := hcRow i
    have he : (∑ j ∈ univ.filter (fun j => j ≠ i), q i j)=∑ j, q i j := by
      apply sum_subset (filter_subset _ _)
      intro j _ hj
      have hji : j=i := by simpa only [mem_filter,mem_univ,true_and,not_not] using hj
      subst j
      exact hqdiag i
    rw [he] at ha
    omega
  obtain ⟨y,hy,hys⟩ := divide_cross_quotas h b q hqdiag hqdiv hqpair hqrow
  exact ⟨y,hy,fun i j hij => by rw [hys]; exact hqadd i j hij⟩

end CDRBicolour.KBicolor.PrescribedCounting
