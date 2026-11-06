/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3MacroBankBasal
public import RequestProject.TypedTriangle.SlotPairing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical

namespace TypedTriangle

/-- The inherited stock, new stock, selector and protected bank form a single
basal set when their disjointness is exactly that produced by G3. -/
theorem prepared_resource_union_basal {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)}
    {T D R B : Finset (Sym2 V)}
    (hT : Basal H F T) (hD : Basal H F D) (hR : Basal H F R)
    (hDT : Disjoint D T) (hRDT : Disjoint R (D ∪ T))
    (hB : Basal H F B) (hBDRT : Disjoint B ((D ∪ R) ∪ T)) :
    Basal H F (((D ∪ R) ∪ T) ∪ B) := by
  have hDR : Disjoint D R := hRDT.symm.mono_left subset_union_left
  have hDRT : Disjoint (D ∪ R) T := by
    rw [disjoint_union_left]
    exact ⟨hDT, hRDT.mono_right subset_union_right⟩
  have hDRbasal : Basal H F (D ∪ R) := Basal.union hD hR hDR
  have hDRTbasal : Basal H F ((D ∪ R) ∪ T) := Basal.union hDRbasal hT hDRT
  exact Basal.union hDRTbasal hB hBDRT.symm

end TypedTriangle
