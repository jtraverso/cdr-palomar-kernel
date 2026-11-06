/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VertexDeletedQuotient

@[expose] public section

/-!
# Restricting the vertex type and inheriting the common-neighbour condition

Local proof candidate; not kernel-checked in this campaign.
The subtype is essential: H3 is not asserted on deleted isolated vertices.
H4 transport and the zero-extension quotient isomorphism remain separate tasks.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Actual host on the remaining vertex type, with restricted labels. -/
def restrictedHost (H : Host V I) (Z : Finset V) : Host {v : V // v ∉ Z} I where
  G := {
    Adj := fun u v => H.G.Adj u.1 v.1
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun _ h => H.G.loopless.irrefl _ h⟩ }
  lab := fun v => H.lab v.1

lemma card_commonNbrs_restrictedHost (H : Host V I) (Z : Finset V) (k : I)
    (u v : {w : V // w ∉ Z}) :
    (commonNbrs (restrictedHost H Z) k u v).card =
      ((commonNbrs H k u.1 v.1).filter (fun w => w ∉ Z)).card := by
  refine Finset.card_bij (fun (w : {w : V // w ∉ Z}) _ => w.1) ?_ ?_ ?_
  · intro w hw
    have hp := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, w.2⟩
  · intro w _ w' _ heq
    exact Subtype.ext heq
  · intro w hw
    obtain ⟨hw, hwZ⟩ := Finset.mem_filter.1 hw
    refine ⟨⟨w, hwZ⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩

/-- H3 is inherited by the true remaining host after losing at most αn/2 vertices. -/
theorem commonNbrCond_restrictedHost {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hα : 0 ≤ α) (hH3 : CommonNbrCond H F α) (Z : Finset V)
    (hZ : (Z.card : ℝ) ≤ α * Fintype.card V / 2) :
    CommonNbrCond (restrictedHost H Z) F (α / 2) := by
  intro u v huv k hlabels
  have hfull := hH3 u.1 v.1 (fun heq => huv (Subtype.ext heq)) k hlabels
  set C := commonNbrs H k u.1 v.1
  have hcover : C ⊆ C.filter (fun w => w ∉ Z) ∪ Z := by
    intro w hw
    by_cases hwZ : w ∈ Z
    · exact Finset.mem_union_right _ hwZ
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, hwZ⟩)
  have hcount := (Finset.card_le_card hcover).trans
    (Finset.card_union_le (C.filter (fun w => w ∉ Z)) Z)
  have hcountR : (C.card : ℝ) ≤
      (commonNbrs (restrictedHost H Z) k u v).card + Z.card := by
    rw [card_commonNbrs_restrictedHost]
    exact_mod_cast hcount
  have hcard : (Fintype.card {w : V // w ∉ Z} : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun w : {w : V // w ∉ Z} => w.1) (fun _ _ heq => Subtype.ext heq)
  have hscaled := mul_le_mul_of_nonneg_left hcard hα
  change α / 2 * Fintype.card {w : V // w ∉ Z} ≤ _
  change α * Fintype.card V ≤ (C.card : ℝ) at hfull
  nlinarith

/-- Numerical windows used for original H3--H4 on a residual host of order N ≥ n/2. -/
theorem vertex_deletion_windows {a n N z P hh : ℝ}
    (ha : 0 < a) (hz : 0 ≤ z) (hP : 1 ≤ P)
    (hN : n / 2 ≤ N) (hn : 16 ≤ a * n)
    (hzP : z * P ≤ a * n / 64) (hhP : hh * P ≤ a * n / 16) :
    z + 2 < (a / 2) * N ∧ (z + hh) * P ≤ (a / 4) * N := by
  have hzmono : z ≤ z * P := by
    calc z = z * 1 := by ring
         _ ≤ z * P := mul_le_mul_of_nonneg_left hP hz
  have hzbound : z ≤ a * n / 64 := hzmono.trans hzP
  have htwo : 2 ≤ a * n / 8 := by linarith
  have hscale := mul_le_mul_of_nonneg_left hN ha.le
  constructor
  · calc z + 2 ≤ 9 * a * n / 64 := by nlinarith
         _ < a * n / 4 := by nlinarith
         _ ≤ (a / 2) * N := by nlinarith
  · calc (z + hh) * P ≤ 5 * a * n / 64 := by nlinarith
         _ ≤ a * n / 8 := by nlinarith
         _ ≤ (a / 4) * N := by nlinarith

end TypedTriangle
