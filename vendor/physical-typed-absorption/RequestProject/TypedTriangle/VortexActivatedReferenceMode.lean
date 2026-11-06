/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeActivatedChild
public import RequestProject.TypedTriangle.CoreEdgeGraph
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace TypedTriangle.CatalogNative
open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47

/-- Reference avoidance only needs the actual residue and the bank inside
the avoiding resource union. The protection F0 may also contain a prescribed
future stock which the reference itself must retain. -/
theorem activated_mode_avoiding_actual_reference {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    {d c E Rc P q Ecell zmax L N J : ℕ}
    (C0 : CoreCompression H.G H.lab F W d c E)
    (F0 U Y Eref : Finset (Sym2 V)) (x : MCore H.G H.lab F W)
    (hM : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N)
    (hJ : J ≤ L) (hYF : Y ⊆ F0) (hYE : Y ⊆ edges H)
    (hx : (x : Sym2 V → ℤ) = SparseEdge.ind Y)
    (hOut : ProtOutcome C0 Rc P q Ecell zmax F0 N J x)
    (hYU : Y ⊆ U)
    (hBU : Br (protSetting C0 Rc P q Ecell zmax F0) N ⊆ U)
    (hAvoid : Disjoint Eref U) :
    ∃ Ytot Yb Bc : Finset (Sym2 V),
      Ytot = Y ∪ Yb ∧ Ytot ⊆ edges H ∧ Ytot ⊆ U ∧
      Disjoint Eref Ytot ∧
      Br (protSetting C0 Rc P q Ecell zmax F0) N = Bc ∪ Yb ∧
      Basal H F Bc ∧ Disjoint Bc F0 ∧
      Disjoint Bc Yb ∧ Disjoint Y Yb ∧
      SparseEdge.ind Ytot ∈ LamCore H.G H.lab F W ∧
      Yb ⊆ childEdges H.G W := by
  obtain ⟨Yb,Bc,hBc,hBcF,hWhole,hBcYb,hYYb,hLam,hYbCore⟩ :=
    activated_child_and_whole_complement C0 F0 hM hJ Y hYF x hx hOut
  have hYbBank : Yb ⊆ Br (protSetting C0 Rc P q Ecell zmax F0) N := by
    rw [hWhole]
    exact Finset.subset_union_right
  have hYtotU : Y ∪ Yb ⊆ U := Finset.union_subset hYU (hYbBank.trans hBU)
  have hYbE : Yb ⊆ edges H := by
    intro e he
    have heAdj := SparseEdge.mem_edges.mp (hYbCore he)
    induction e using Sym2.ind with
    | _ u v =>
      exact SparseEdge.mem_edges.mpr ((S07V42.indG_le H.G W) heAdj)
  exact ⟨Y ∪ Yb,Yb,Bc,rfl,Finset.union_subset hYE hYbE,hYtotU,
    hAvoid.mono_right hYtotU,hWhole,hBc,hBcF,hBcYb,hYYb,hLam,hYbCore⟩

#print axioms activated_mode_avoiding_actual_reference

end TypedTriangle.CatalogNative
