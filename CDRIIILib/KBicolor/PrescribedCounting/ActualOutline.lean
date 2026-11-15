/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.CrossTypeCounts

/-! # The exact marginals of an actual bicoloured Latin table -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {B k : ℕ}

theorem sum_by_class (κ : Fin B → Fin k) (f : Fin B → ℕ) :
    (∑ c, ∑ a ∈ univ.filter (fun a => κ a=c), f a)=∑ a, f a := by
  simp only [sum_filter]
  rw [sum_comm]
  simp

theorem actual_outline_marginals (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B)
    (hL : _root_.STS.IsLatin L) :
    (∀ r c, ∑ s, outlineMass κ L r c s=Hilton.csize κ r*Hilton.csize κ c) ∧
    (∀ r s, ∑ c, outlineMass κ L r c s=Hilton.csize κ r*Hilton.csize κ s) ∧
    (∀ c s, ∑ r, outlineMass κ L r c s=Hilton.csize κ c*Hilton.csize κ s) := by
  have hr : ∀ r s, (∑ c : Fin B, if κ (L r c)=s then 1 else 0)=Hilton.csize κ s := by
    intro r s
    have hh := (latin_class_graphs_regular κ L hL s).1 r
    simpa only [rowSet,classGraph,mem_filter,mem_univ,true_and,sum_boole,Nat.cast_id] using hh
  have hc : ∀ c s, (∑ r : Fin B, if κ (L r c)=s then 1 else 0)=Hilton.csize κ s := by
    intro c s
    have hh := (latin_class_graphs_regular κ L hL s).2 c
    simpa only [colSet,classGraph,mem_filter,mem_univ,true_and,sum_boole,Nat.cast_id] using hh
  refine ⟨fun r c => ?_,fun r s => ?_,fun c s => ?_⟩
  · unfold outlineMass
    rw [sum_comm]
    simp_rw [sum_comm (s := univ) (t := univ.filter (fun y => κ y=c))]
    simp [Hilton.csize,Fintype.card_subtype]
  · unfold outlineMass
    rw [sum_comm]
    simp_rw [sum_by_class κ]
    simp_rw [hr]
    simp [Hilton.csize,Fintype.card_subtype]
  · unfold outlineMass
    rw [sum_by_class κ]
    rw [sum_comm]
    simp_rw [hc]
    simp [Hilton.csize,Fintype.card_subtype]

theorem actual_outline_zero (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B)
    (hok : ∀ r c, Pattern.bic (κ r) (κ c) (κ (L r c))) :
    ∀ r c s, ¬Pattern.bic r c s → outlineMass κ L r c s=0 := by
  intro r c s hbad
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  have har := (mem_filter.mp ha).2
  have hbc := (mem_filter.mp hb).2
  have hn : κ (L a b) ≠ s := by
    intro he
    exact hbad (by simpa only [har,hbc,he] using hok a b)
  exact ite_eq_right hn

theorem actual_latin_type_tournament (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B)
    (hL : _root_.STS.IsLatin L) (hok : ∀ r c, Pattern.bic (κ r) (κ c) (κ (L r c))) :
    ∃ x : Fin k → Fin k → ℕ, Pattern.IsTour (Hilton.csize κ) x ∧
      ∀ i j, i ≠ j → latinTypeCount κ L i j=3*x i j := by
  obtain ⟨h1,h2,h3⟩ := actual_outline_marginals κ L hL
  have h0 := actual_outline_zero κ L hok
  let M := outlineMass κ L
  let x : Fin k → Fin k → ℕ := fun i j => M i i j
  have hsym := fun i j hij => bicoloured_outline_symmetric (Hilton.csize κ) M h1 h2 h3 h0 (X := i) (Y := j) hij
  refine ⟨x,⟨fun i => ?_,fun i j hij => ?_,fun i => ?_⟩,fun i j hij => ?_⟩
  · exact h0 i i i (by simp [Pattern.bic])
  · have hh : M i j i+M i j j=Hilton.csize κ i*Hilton.csize κ j := by
      rw [← h1]
      symm
      apply sum_two_supported _ hij
      intro s hsi hsj
      apply h0
      simp only [Pattern.bic]
      tauto
    have ha := (hsym i j hij).1
    have hb := (hsym j i hij.symm).2.1
    dsimp only [x]
    omega
  · exact h1 i i
  · rw [latinTypeCount_eq_outline κ L i j hij]
    exact (hsym i j hij).2.2

end CDRBicolour.KBicolor.PrescribedCounting
