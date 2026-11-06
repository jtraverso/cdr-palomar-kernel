/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3ProtectedBankBasalBridge
public import RequestProject.TypedTriangle.G3PreparedBasalUnion
public import RequestProject.TypedTriangle.BasalPackingIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The particular stock, selector and whole bank exported by the native G3
construction form one basal resource. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open BasalIncidence

theorem native_stock_bank_basal {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {d c E Rc P q Ecell zmax L N : ℕ}
    (C0 : S07V42.CoreCompression H.G H.lab F W d c E)
    (T R : Finset (Sym2 V)) (DT A : Finset (Finset V))
    (hT : IsDecomposition H F T DT)
    (hA : IsDecomposition H F (cover A) A)
    (hR : Basal H F R)
    (hAT : Disjoint (cover A) T)
    (hRAT : Disjoint R (cover A ∪ T))
    (hM : S07V40.MacroBank
      (S07V47.protSetting C0 Rc P q Ecell zmax ((cover A∪R)∪T)) L N)
    (hBankDis : Disjoint
      (S07V40.Br (S07V47.protSetting C0 Rc P q Ecell zmax ((cover A∪R)∪T)) N)
      ((cover A∪R)∪T)) :
    Basal H F ((((cover A∪R)∪T)∪
      S07V40.Br (S07V47.protSetting C0 Rc P q Ecell zmax ((cover A∪R)∪T)) N)) := by
  have hBank : Basal H F
      (S07V40.Br (S07V47.protSetting C0 Rc P q Ecell zmax ((cover A∪R)∪T)) N) :=
    protected_bank_basal C0 ((cover A∪R)∪T) hM
  exact prepared_resource_union_basal ⟨DT,hT⟩ ⟨A,hA⟩ hR
    hAT hRAT hBank hBankDis

#print axioms native_stock_bank_basal

end TypedTriangle.CatalogNative
