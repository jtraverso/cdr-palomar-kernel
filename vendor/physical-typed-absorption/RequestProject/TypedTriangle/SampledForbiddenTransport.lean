/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreBasalPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Pull a protected ambient edge set into a previously chosen sampled core.
The local degree does not increase, and avoiding the pullback is equivalent to
avoiding the ambient set after lifting. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.SampledResource

variable {V : Type} [Fintype V]

def edgeLift (W : Finset V) : Sym2 {x // x ∈ W} → Sym2 V :=
  Sym2.map Subtype.val

lemma edgeLift_injective (W : Finset V) : Function.Injective (edgeLift W) :=
  Sym2.map.injective Subtype.val_injective

def pull (W : Finset V) (B : Finset (Sym2 V)) :
    Finset (Sym2 {x // x ∈ W}) :=
  B.preimage (edgeLift W) (edgeLift_injective W).injOn

lemma degree_pull_le (W : Finset V) (B : Finset (Sym2 V))
    (v : {x // x ∈ W}) :
    SelSimul.edeg (pull W B) v ≤ SelSimul.edeg B v.1 := by
  apply card_le_card_of_injOn (edgeLift W)
  · intro e he
    obtain ⟨heB,hve⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_preimage.mp heB,
      Sym2.mem_map.mpr ⟨v,hve,rfl⟩⟩
  · exact (edgeLift_injective W).injOn

def lift (W : Finset V) (E : Finset (Sym2 {x // x ∈ W})) :
    Finset (Sym2 V) := E.image (edgeLift W)

lemma lift_disjoint_of_pull_disjoint (W : Finset V)
    (E : Finset (Sym2 {x // x ∈ W})) (B : Finset (Sym2 V))
    (h : Disjoint E (pull W B)) : Disjoint (lift W E) B := by
  apply disjoint_left.mpr
  intro e heE heB
  obtain ⟨f,hf,rfl⟩ := mem_image.mp heE
  exact disjoint_left.mp h hf (mem_preimage.mpr heB)

#print axioms degree_pull_le
#print axioms lift_disjoint_of_pull_disjoint

end TypedTriangle.SampledResource
