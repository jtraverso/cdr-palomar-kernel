/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.ReservedSpectrum
public import CDRBicolour.KBicolor.PrescribedCounting.CycleResidues

/-! # Congruences of the full type vector from its cycle coordinates -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
variable {k : ℕ}

theorem type_congruences_of_coordinates (o : Fin k) (u v : Fin k → Fin k → ℕ)
    (hp : ∀ i j, i ≠ j → u i j+u j i=v i j+v j i)
    (hr : ∀ i, ∑ j ∈ univ.filter (fun j => j ≠ i), u i j =
      ∑ j ∈ univ.filter (fun j => j ≠ i), v i j)
    (hc : ∀ i : Coord o, 3 ∣ ((u i.1.1 i.1.2 : ℤ)-v i.1.1 i.1.2)) :
    ∀ i j, i ≠ j → 3 ∣ ((u i j : ℤ)-v i j) := by
  have hanti : ∀ i j, i ≠ j → (u i j : ℤ)-v i j = -((u j i : ℤ)-v j i) := by
    intro i j hij
    have he : (u i j : ℤ)+u j i=v i j+v j i := by exact_mod_cast hp i j hij
    omega
  have hfree : ∀ i j, i ≠ o → j ≠ o → i ≠ j → 3 ∣ ((u i j : ℤ)-v i j) := by
    intro i j hio hjo hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hc ⟨(i,j),hlt,hio,hjo⟩
    · rw [hanti i j hij]
      exact dvd_neg.mpr (hc ⟨(j,i),hlt,hjo,hio⟩)
  have hroot : ∀ i, i ≠ o → 3 ∣ ((u i o : ℤ)-v i o) := by
    intro i hio
    let A := univ.filter (fun j : Fin k => j ≠ i)
    have ho : o ∈ A := mem_filter.mpr ⟨mem_univ _,hio.symm⟩
    have hs : 3 ∣ ∑ j ∈ A.erase o, ((u i j : ℤ)-v i j) := by
      apply dvd_sum
      intro j hj
      exact hfree i j hio (mem_erase.mp hj).1 (mem_filter.mp (mem_erase.mp hj).2).2.symm
    have he : ((u i o : ℤ)-v i o) + ∑ j ∈ A.erase o, ((u i j : ℤ)-v i j)=0 := by
      rw [add_sum_erase A (fun j => (u i j : ℤ)-v i j) ho,sum_sub_distrib]
      have hh : (∑ j ∈ A, (u i j : ℤ))=∑ j ∈ A, (v i j : ℤ) := by
        exact_mod_cast hr i
      exact sub_eq_zero.mpr hh
    have heq : ((u i o : ℤ)-v i o)= -(∑ j ∈ A.erase o, ((u i j : ℤ)-v i j)) := by omega
    rw [heq]
    exact dvd_neg.mpr hs
  intro i j hij
  by_cases hio : i=o
  · subst i
    rw [hanti _ _ hij]
    exact dvd_neg.mpr (hroot j hij.symm)
  by_cases hjo : j=o
  · subst j; exact hroot i hio
  exact hfree i j hio hjo hij

theorem choose_modular_trade_halves {n m : ℕ} (lab : Fin n → Fin k) (o : Fin k)
    [Fact m.Prime] (hm : 8 < m) (P : Place lab (Coord o) m) (hτ : P.τ=tau3 o)
    (E C : Finset (Finset (Fin n))) (t : Fin k → Fin k → ℕ)
    (hfull : ∀ σ, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab))
      ((E ∪ packG P σ) ∪ C))
    (hEP : ∀ σ, Disjoint E (packG P σ))
    (hRC : ∀ σ, Disjoint (E ∪ packG P σ) C)
    (hpair : ∀ i j, i ≠ j → 2*(t i j+t j i)=ksz lab i*ksz lab j)
    (hrow : ∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), t i j=ksz lab i*(ksz lab i-1))
    (hC : ∀ i j, i ≠ j → 3 ∣ kTypeCount lab C i j) :
    ∃ σ, ∀ i j, i ≠ j → 3 ∣ ((t i j : ℤ)-kTypeCount lab (E ∪ packG P σ) i j) := by
  let D := fun σ => (E ∪ packG P σ) ∪ C
  let σ₀ : Coord o × ZMod m × ZMod m → Bool := fun _ => false
  obtain ⟨N,hN,hmod⟩ := residue_switch_numbers
    (fun i : Coord o => (kTypeCount lab (D σ₀) i.1.1 i.1.2 : ℤ))
    (fun i => (t i.1.1 i.1.2 : ℤ))
  obtain ⟨σ,hσ⟩ := exists_selected_switches (univ : Finset (Coord o × ZMod m × ZMod m)) N (by
    intro i
    have hcard : #(univ.filter (fun c : Coord o × ZMod m × ZMod m => c.1=i))=m*m := by
      have he : univ.filter (fun c : Coord o × ZMod m × ZMod m => c.1=i)=
          {i} ×ˢ (univ : Finset (ZMod m × ZMod m)) := by
        ext c
        simp only [mem_filter,mem_univ,true_and,mem_product,mem_singleton,and_true]
      rw [he,card_product]
      simp [ZMod.card]
    rw [hcard]
    have hm0 : 9 ≤ m := by omega
    exact (hN i).trans (by nlinarith))
  have hcount : ∀ (R P : Finset (Finset (Fin n))), Disjoint R P → ∀ i j,
      kTypeCount lab (R ∪ P) i j=kTypeCount lab R i j+kTypeCount lab P i j := by
    intro R P hd i j
    unfold kTypeCount
    rw [filter_union,card_union_of_disjoint (disjoint_filter_filter hd)]
  have hadd : ∀ σ i j, (kTypeCount lab (D σ) i j : ℤ)=
      (kTypeCount lab E i j : ℤ)+kTypeCount lab (packG P σ) i j+kTypeCount lab C i j := by
    intro σ i j
    dsimp only [D]
    rw [hcount _ _ (hRC σ),hcount _ _ (hEP σ)]
    push_cast
    rfl
  have hcoord : ∀ i : Coord o, 3 ∣ ((kTypeCount lab (D σ) i.1.1 i.1.2 : ℤ)-t i.1.1 i.1.2) := by
    intro i
    have hc := packG_count P hm σ i.1.1 i.1.2
    have hc0 := packG_count P hm σ₀ i.1.1 i.1.2
    simp only [σ₀,Bool.false_eq_true,ite_false,sum_const_zero,add_zero] at hc0
    simp_rw [hτ] at hc0
    simp_rw [hτ,diff_coord] at hc
    rw [hσ i] at hc
    have he := hmod i
    rw [hadd σ]
    rw [hadd σ₀] at he
    convert he using 1 <;> linarith
  have hall := type_congruences_of_coordinates o (kTypeCount lab (D σ)) t
    (fun i j hij => by
      have h1 := typeCount_pair lab (hfull σ) hij
      have h2 := hpair i j hij
      change 2*(kTypeCount lab (D σ) i j+kTypeCount lab (D σ) j i)=_ at h1
      omega)
    (fun i => by
      have h1 := typeCount_row lab (hfull σ) i
      have h2 := hrow i
      change 2*∑ j ∈ univ.filter (fun j => j ≠ i), kTypeCount lab (D σ) i j=_ at h1
      omega) hcoord
  refine ⟨σ,fun i j hij => ?_⟩
  have hcZ : (3 : ℤ) ∣ (kTypeCount lab C i j : ℤ) := by exact_mod_cast hC i j hij
  have he := hall i j hij
  rw [hadd σ] at he
  have hs := dvd_sub he hcZ
  apply dvd_neg.mp
  rw [hcount _ _ (hEP σ)]
  push_cast
  convert hs using 1 <;> simp only [neg_sub]; ring

end CDRBicolour.KBicolor.PrescribedCounting
