/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkReach
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)

@[expose] public section

/-! Local integration candidate. NOT kernel-checked.
Removing an isolated root from the deletion list does not change its link.
No previous declaration or proof is modified.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

/-- Deleting an isolated vertex has no effect, even with protected base edges. -/
lemma delG_erase_isolated {Ω : Type*} (J : SimpleGraph Ω) (A : Finset Ω)
    (B : Finset (Sym2 Ω)) (r : Ω) (hr : ∀ u, ¬ J.Adj r u) :
    delG J (A.erase r) B = delG J A B := by
  ext u v
  change (J.Adj u v ∧ u ∉ A.erase r ∧ v ∉ A.erase r ∧ s(u,v) ∉ B) ↔
    (J.Adj u v ∧ u ∉ A ∧ v ∉ A ∧ s(u,v) ∉ B)
  constructor
  · rintro ⟨h,hu,hv,hB⟩
    have hur : u ≠ r := by intro he; subst u; exact hr v h
    have hvr : v ≠ r := by intro he; subst v; exact hr u h.symm
    exact ⟨h,fun huA => hu (Finset.mem_erase.mpr ⟨hur,huA⟩),
      fun hvA => hv (Finset.mem_erase.mpr ⟨hvr,hvA⟩),hB⟩
  · rintro ⟨h,hu,hv,hB⟩
    exact ⟨h,fun huS => hu (Finset.mem_of_mem_erase huS),
      fun hvS => hv (Finset.mem_of_mem_erase hvS),hB⟩

variable {V I : Type*} [Fintype V]

lemma link_root_isolated (H : Host V I) (F : Set (Multiset I)) (z : V) :
    ∀ u, ¬ (linkGraph H F z).Adj z u := by
  intro u h
  exact (linkGraph_adj_ne h).1 rfl

/-- The old robust incidence theorem applies also when the link root is deleted. -/
theorem link_image_robust_any_root {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (z : V) (A : Finset V) (B : Finset (Sym2 V))
    (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (A.card : ℝ)+2+4*d < α*Fintype.card V)
    (hwin2 : ((A.card : ℝ)+h+5*d)*2 ^ Nat.choose h 2 ≤ α/2*Fintype.card V)
    {x : V → ℤ} (hx : ∀ y ∈ A, x y=0) :
    x ∈ Incidence.incLattice (linkGraph H F z) ↔
      x ∈ Incidence.incLattice (delG (linkGraph H F z) A B) := by
  have hcard : ((A.erase z).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hw1 : ((A.erase z).card : ℝ)+2+4*d < α*Fintype.card V := by linarith
  have hw2 : (((A.erase z).card : ℝ)+h+5*d)*2 ^ Nat.choose h 2 ≤
      α/2*Fintype.card V := by
    exact (mul_le_mul_of_nonneg_right (by linarith :
      ((A.erase z).card : ℝ)+h+5*d ≤ (A.card : ℝ)+h+5*d) (by positivity)).trans hwin2
  have result := link_image_robust hα hH3 hH4 (A.erase z) (Finset.notMem_erase z A)
    B d hdeg hw1 hw2 (fun y hy => hx y (Finset.mem_of_mem_erase hy))
  rw [linkOn_goodEdges_eq,
    delG_erase_isolated (linkGraph H F z) A B z (link_root_isolated H F z)] at result
  exact result

/-- Link connectivity survives deletion even for roots inside the deletion set. -/
theorem link_reach_robust_any_root {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (z : V) (A : Finset V) (B : Finset (Sym2 V))
    (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (A.card : ℝ)+2+4*d < α*Fintype.card V)
    (hwin2 : ((A.card : ℝ)+h+5*d)*2 ^ Nat.choose h 2 ≤ α/2*Fintype.card V)
    {a b : V} (ha : a ∉ A) (hb : b ∉ A)
    (hab : (linkGraph H F z).Reachable a b) :
    (delG (linkGraph H F z) A B).Reachable a b := by
  obtain ⟨p⟩ := hab
  have hm := Incidence.walk_mem p
  have hx : ∀ y ∈ A,
      (Incidence.dlt a - ((-1 : ℤ) ^ p.length) • Incidence.dlt b) y=0 := by
    intro y hy
    have hya : y ≠ a := fun he => ha (he ▸ hy)
    have hyb : y ≠ b := fun he => hb (he ▸ hy)
    simp [Incidence.dlt,hya,hyb]
  exact Incidence.reach_of_mem_incLattice
    ((link_image_robust_any_root hα hH3 hH4 z A B d hdeg hwin1 hwin2 hx).mp hm)

/-- Odd closed walks survive deletion for roots inside or outside the deletion set. -/
theorem link_oddAt_robust_any_root {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (z : V) (A : Finset V) (B : Finset (Sym2 V))
    (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (A.card : ℝ)+2+4*d < α*Fintype.card V)
    (hwin2 : ((A.card : ℝ)+h+5*d)*2 ^ Nat.choose h 2 ≤ α/2*Fintype.card V)
    {a : V} (ha : a ∉ A) (hodd : Incidence.OddAt (linkGraph H F z) a) :
    Incidence.OddAt (delG (linkGraph H F z) A B) a := by
  obtain ⟨p,hp⟩ := hodd
  have hm := Incidence.walk_mem p
  rw [hp.neg_one_pow,neg_one_smul,sub_neg_eq_add,← two_smul ℤ] at hm
  have hx : ∀ y ∈ A, ((2 : ℤ) • Incidence.dlt a) y=0 := by
    intro y hy
    have hya : y ≠ a := fun he => ha (he ▸ hy)
    simp [Incidence.dlt,hya]
  exact Incidence.oddAt_of_two_dlt_mem
    ((link_image_robust_any_root hα hH3 hH4 z A B d hdeg hwin1 hwin2 hx).mp hm)

end TypedTriangle
