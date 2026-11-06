/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3NativeResourceBasal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Separate the distinguished stock from the remaining basal resources.
The latter have their own decomposition, so they can be passed as the
protected reserve to the monitored G4 transition. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open BasalIncidence

theorem basal_remainder_split {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)}
    (D DT : Finset (Finset V))
    (R T Bank E : Finset (Sym2 V))
    (hR : Basal H F R) (hT : IsDecomposition H F T DT)
    (hBank : Basal H F Bank) (hE : Basal H F E)
    (hDT : Disjoint (cover D) T)
    (hRDT : Disjoint R (cover D∪T))
    (hBankDis : Disjoint Bank ((cover D∪R)∪T))
    (hEDis : Disjoint E (((cover D∪R)∪T)∪Bank)) :
    let R' := ((R∪T)∪Bank)∪E
    ∃ DR : Finset (Finset V),
      IsDecomposition H F R' DR ∧
      Disjoint (cover D) R' ∧
      cover D∪R' = (((cover D∪R)∪T)∪Bank)∪E := by
  dsimp only
  have hRT : Disjoint R T := by
    apply disjoint_left.mpr
    intro e heR heT
    exact (disjoint_left.mp hRDT) heR
      (mem_union.mpr (Or.inr heT))
  have hRTBank : Disjoint (R∪T) Bank := by
    apply disjoint_left.mpr
    intro e heRT heBank
    have heBase : e ∈ ((cover D∪R)∪T) := by
      rcases mem_union.mp heRT with heR | heT
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr heR)))
      · exact mem_union.mpr (Or.inr heT)
    exact (disjoint_left.mp hBankDis) heBank heBase
  have hRTBankE : Disjoint ((R∪T)∪Bank) E := by
    apply disjoint_left.mpr
    intro e heRTB heE
    have heBase : e ∈ (((cover D∪R)∪T)∪Bank) := by
      rcases mem_union.mp heRTB with heRT | heBank
      · rcases mem_union.mp heRT with heR | heT
        · exact mem_union.mpr (Or.inl
            (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr heR)))))
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr heT)))
      · exact mem_union.mpr (Or.inr heBank)
    exact (disjoint_left.mp hEDis) heE heBase
  have hTail : Basal H F (((R∪T)∪Bank)∪E) :=
    Basal.union (Basal.union (Basal.union hR ⟨DT,hT⟩ hRT)
      hBank hRTBank) hE hRTBankE
  obtain ⟨DR,hDR⟩ := hTail
  refine ⟨DR,hDR,?_,?_⟩
  · apply disjoint_left.mpr
    intro e heD heTail
    rcases mem_union.mp heTail with heRTB | heE
    · rcases mem_union.mp heRTB with heRT | heBank
      · rcases mem_union.mp heRT with heR | heT
        · exact (disjoint_left.mp hRDT) heR
            (mem_union.mpr (Or.inl heD))
        · exact (disjoint_left.mp hDT) heD heT
      · exact (disjoint_left.mp hBankDis) heBank
          (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl heD))))
    · exact (disjoint_left.mp hEDis) heE
        (mem_union.mpr (Or.inl
          (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl heD))))))
  · simp only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

#print axioms basal_remainder_split

end TypedTriangle.CatalogNative
