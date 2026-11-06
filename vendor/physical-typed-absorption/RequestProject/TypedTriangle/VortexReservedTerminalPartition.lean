/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3BasalRemainderSplit
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex
open CatalogNative BasalIncidence

/-- The reserved terminal stock remains literally in the basal remainder.
Removing it is justified by the original disjoint resource construction,
not by subtracting an arbitrary basal graph from another basal graph. -/
theorem reserved_terminal_remainder {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (D DT : Finset (Finset V)) (R T Bank E Rtail : Finset (Sym2 V))
    (hR : Basal H F R) (hT : IsDecomposition H F T DT)
    (hBank : Basal H F Bank) (hE : Basal H F E)
    (hDT : Disjoint (cover D) T) (hRdis : Disjoint R (cover D ∪ T))
    (hBankdis : Disjoint Bank ((cover D ∪ R) ∪ T))
    (hEdis : Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank))
    (hDtail : Disjoint (cover D) Rtail)
    (hEq : cover D ∪ Rtail = (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E) :
    Rtail = ((R ∪ T) ∪ Bank) ∪ E ∧
      T ⊆ Rtail ∧ Basal H F (Rtail \ T) := by
  obtain ⟨DR,hDR,hDtail',hEq'⟩ :=
    basal_remainder_split D DT R T Bank E hR hT hBank hE
      hDT hRdis hBankdis hEdis
  have hTail : Rtail = ((R ∪ T) ∪ Bank) ∪ E := by
    have hUnions := hEq.trans hEq'.symm
    ext e
    have hm := congrArg (fun S : Finset (Sym2 V) => e ∈ S) hUnions
    simp only [Finset.mem_union] at hm
    have hno : e ∈ Rtail → e ∉ cover D :=
      fun he hd => Finset.disjoint_left.mp hDtail hd he
    have hno' : e ∈ ((R ∪ T) ∪ Bank) ∪ E → e ∉ cover D :=
      fun he hd => Finset.disjoint_left.mp hDtail' hd he
    have hm' := Iff.of_eq hm
    simp only [Finset.mem_union] at hno' ⊢
    tauto
  have hRT : Disjoint R T := hRdis.mono_right Finset.subset_union_right
  have hBT : Disjoint Bank T := hBankdis.mono_right Finset.subset_union_right
  have hET : Disjoint E T := by
    apply hEdis.mono_right
    intro e he
    exact mem_union_left _ (mem_union_right _ he)
  have hWithout : (((R ∪ T) ∪ Bank) ∪ E) \ T = (R ∪ Bank) ∪ E := by
    ext e
    have hRnot : e ∈ R → e ∉ T := fun he => Finset.disjoint_left.mp hRT he
    have hBnot : e ∈ Bank → e ∉ T := fun he => Finset.disjoint_left.mp hBT he
    have hEnot : e ∈ E → e ∉ T := fun he => Finset.disjoint_left.mp hET he
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hRB : Disjoint R Bank := by
    apply Disjoint.symm
    apply hBankdis.mono_right
    intro e he
    exact mem_union_left _ (mem_union_right _ he)
  have hRBE : Disjoint (R ∪ Bank) E := by
    apply Disjoint.symm
    apply hEdis.mono_right
    intro e he
    rcases mem_union.mp he with heR | heB
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ heR))
    · exact mem_union_right _ heB
  refine ⟨hTail,?_,?_⟩
  · rw [hTail]
    intro e he
    exact mem_union_left _ (mem_union_left _ (mem_union_right _ he))
  · rw [hTail,hWithout]
    exact Basal.union (Basal.union hR hBank hRB) hE hRBE

#print axioms reserved_terminal_remainder

end TypedTriangle.Vortex
