/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3MacroBankBasal
public import RequestProject.TypedTriangle.SlotPairing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The bank's original-host basal certificate is expressed in the same
predicate as the stock and the sampled reference. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem protected_bank_basal {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {d c E Rc P q Ecell zmax L N : ℕ}
    (C0 : S07V42.CoreCompression H.G H.lab F W d c E)
    (F0 : Finset (Sym2 V))
    (hM : S07V40.MacroBank
      (S07V47.protSetting C0 Rc P q Ecell zmax F0) L N) :
    Basal H F (S07V40.Br
      (S07V47.protSetting C0 Rc P q Ecell zmax F0) N) := by
  have h := (S07V47.protected_total_bank_basal C0 F0 hM).1
  have hEdge : (TypedTriangle.triEdges : Finset V → Finset (Sym2 V)) =
      SparseEdge.triEdges := rfl
  rcases h with ⟨DB,hDB⟩
  refine ⟨DB,?_⟩
  simpa only [TypedTriangle.IsDecomposition, SparseEdge.IsDecomposition,
    TypedTriangle.IsAllowed, SparseEdge.IsAllowed, hEdge] using hDB

#print axioms protected_bank_basal

end TypedTriangle.CatalogNative
