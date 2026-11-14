/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.AllocationSplit
public import CDRBicolour.KBicolor.Pattern.Outline

/-! # A scaled integer tournament splits into ordinary integer tournaments -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {k : ℕ}

def allocation (x : Fin k → Fin k → ℕ) (e : Fin k × Fin k) (v : Fin k) : ℕ :=
  (if e.1=v ∧ v<e.2 then x v e.2 else 0) +
    (if e.2=v ∧ e.1<v then x v e.1 else 0)

theorem allocation_row (x : Fin k → Fin k → ℕ) (i j : Fin k) :
    ∑ v, allocation x (i,j) v = if i<j then x i j+x j i else 0 := by
  have he : ∀ v, allocation x (i,j) v =
      (if v=i then (if i<j then x i j else 0) else 0) +
        (if v=j then (if i<j then x j i else 0) else 0) := by
    intro v
    by_cases hvi : v=i <;> by_cases hvj : v=j <;> simp_all [allocation,eq_comm]
  simp only [he,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]
  split_ifs <;> simp

theorem allocation_column (x : Fin k → Fin k → ℕ) (c : Fin k) :
    ∑ e : Fin k × Fin k, allocation x e c = ∑ j, if j=c then 0 else x c j := by
  have hfirst : (∑ i : Fin k, ∑ j : Fin k,
      if i=c ∧ c<j then x c j else 0) = ∑ j, if c<j then x c j else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases hcj : c<j <;> simp [hcj]
  have hsecond : (∑ i : Fin k, ∑ j : Fin k,
      if j=c ∧ i<c then x c i else 0) = ∑ i, if i<c then x c i else 0 := by
    apply sum_congr rfl
    intro i _
    by_cases hic : i<c <;> simp [hic]
  simp only [allocation,Fintype.sum_prod_type,sum_add_distrib]
  rw [hfirst,hsecond,← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy c j with hcj | rfl | hjc
  · simp [hcj,not_lt_of_ge hcj.le,ne_of_gt hcj]
  · simp
  · simp [hjc,not_lt_of_ge hjc.le,ne_of_lt hjc]

def unpack (A : (Fin k × Fin k) → Fin k → ℕ) (i j : Fin k) : ℕ :=
  if i<j then A (i,j) i else if j<i then A (j,i) i else 0

theorem unpack_diag (A : (Fin k × Fin k) → Fin k → ℕ) (i : Fin k) : unpack A i i=0 := by
  simp [unpack]

theorem unpack_allocation (x : Fin k → Fin k → ℕ) (hx : ∀ i, x i i=0) :
    unpack (allocation x) = x := by
  funext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [unpack,allocation,hij,not_lt_of_ge hij.le,ne_of_lt hij]
  · simp [unpack,allocation,hx]
  · simp [unpack,allocation,hji,not_lt_of_ge hji.le,ne_of_gt hji]

theorem allocation_unpack (A : (Fin k × Fin k) → Fin k → ℕ)
    (hA : ∀ e v, ¬(e.1<e.2 ∧ (e.1=v ∨ e.2=v)) → A e v=0) :
    allocation (unpack A) = A := by
  funext e v
  rcases e with ⟨i,j⟩
  by_cases hij : i<j
  · by_cases hiv : i=v
    · subst v
      simp [allocation,unpack,hij,ne_of_lt hij,not_lt_of_ge hij.le]
    · by_cases hjv : j=v
      · subst v
        simp [allocation,unpack,hij,ne_of_lt hij,ne_of_gt hij,not_lt_of_ge hij.le]
      · have hz := hA (i,j) v (by simpa [hij,hiv,hjv])
        simp [allocation,hiv,hjv,hz]
  · have hz := hA (i,j) v (by simp [hij])
    have h₁ : ¬(i=v ∧ v<j) := by rintro ⟨rfl,hh⟩; exact hij hh
    have h₂ : ¬(j=v ∧ i<v) := by rintro ⟨rfl,hh⟩; exact hij hh
    simp [allocation,h₁,h₂,hz]

theorem split_scaled_tournament (h : ℕ) (b : Fin k → ℕ) (x : Fin k → Fin k → ℕ)
    (hdiag : ∀ i, x i i=0)
    (hpair : ∀ i j, i≠j → x i j+x j i=h*(b i*b j))
    (hrow : ∀ i, ∑ j, x i j=h*(b i*b i)) :
    ∃ y : Fin h → Fin k → Fin k → ℕ,
      (∀ t, Pattern.IsTour b (y t)) ∧ (∀ i j, ∑ t, y t i j=x i j) := by
  have hr : ∀ e : Fin k × Fin k, ∑ v, allocation x e v =
      h*(if e.1<e.2 then b e.1*b e.2 else 0) := by
    rintro ⟨i,j⟩
    rw [allocation_row]
    by_cases hij : i<j <;> simp only [hij,ite_true,ite_false,mul_zero]
    exact hpair i j (ne_of_lt hij)
  have hc : ∀ v, ∑ e : Fin k × Fin k, allocation x e v=h*(b v*b v) := by
    intro v
    rw [allocation_column]
    have he : (fun j => if j=v then 0 else x v j) = x v := by
      funext j; by_cases hj : j=v <;> simp_all
    rw [he,hrow]
  obtain ⟨A,hAr,hAc,hAs,hAle,hAz⟩ := Hilton.decompose_with_support h (allocation x)
    (fun e : Fin k × Fin k => if e.1<e.2 then b e.1*b e.2 else 0)
    (fun v => b v*b v) hr hc
  have hsupport : ∀ t e v, ¬(e.1<e.2 ∧ (e.1=v ∨ e.2=v)) → A t e v=0 := by
    intro t e v hbad
    apply hAz t e v
    have h₁ : ¬(e.1=v ∧ v<e.2) := by rintro ⟨hh,hh'⟩; exact hbad ⟨hh ▸ hh',Or.inl hh⟩
    have h₂ : ¬(e.2=v ∧ e.1<v) := by rintro ⟨hh,hh'⟩; exact hbad ⟨hh ▸ hh',Or.inr hh⟩
    simp [allocation,h₁,h₂]
  refine ⟨fun t => unpack (A t),fun t => ⟨unpack_diag _,?_,?_⟩,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hh := allocation_row (unpack (A t)) i j
      rw [allocation_unpack (A t) (hsupport t),hAr] at hh
      simpa only [hij,ite_true] using hh.symm
    · have hh := allocation_row (unpack (A t)) j i
      rw [allocation_unpack (A t) (hsupport t),hAr] at hh
      simpa only [hji,ite_true,Nat.add_comm,Nat.mul_comm] using hh.symm
  · intro i
    have hh := allocation_column (unpack (A t)) i
    rw [allocation_unpack (A t) (hsupport t),hAc] at hh
    have he : (fun j => if j=i then 0 else unpack (A t) i j) = unpack (A t) i := by
      funext j; by_cases hj : j=i <;> simp_all [unpack_diag]
    simpa only [he] using hh.symm
  · intro i j
    have hh := congrFun (congrFun (unpack_allocation x hdiag) i) j
    rw [← hh]
    unfold unpack
    by_cases hij : i<j <;> by_cases hji : j<i <;>
      simp only [hij,hji,ite_true,ite_false,sum_const_zero,hAs]

end CDRBicolour.KBicolor.PrescribedCounting
