module
public import RequestProject.TypedTriangle.PaschEmbeddedPaddedEligibility
public import RequestProject.TypedTriangle.PaschRawFloorTarget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone

def embeddedMixedEligibilityOrder (α C : ℝ) (L : ℕ) : ℕ :=
  max (max (supersaturationOrder α) ⌈2*C⌉₊)
    ⌈((6*C^3+localMixedDegreeScale C L)/(massConstant α C/16))^2⌉₊

variable {X V I : Type*} [Fintype X] [Fintype V]

/-- H3 and the actual raw coefficient window discharge every clone test.
The nonempty tested index family supplies the allowed triangle witness. -/
theorem raw_embedded_padded_tuple_eligible {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (e : X ↪ V) (L : ℕ)
    (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X) :
    letI : DecidableEq X := Classical.decEq X
    letI : DecidableEq V := Classical.decEq V
    ∀ B : Finset (Finset V), PairCodegreeBound B L →
      (∀ T ∈ B, T.card = 3) →
      (∀ T ∈ B, 2 ≤ (T ∩ (univ : Finset X).map e).card) →
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 3 → ∀ R : Finset (allowed H F),
      1 ≤ R.card → R.card ≤ ℓ →
      let A := allowed H F
      let n := (Fintype.card X : ℝ)
      tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ R *
          (n^2)^((R.card : ℝ)+1/4) ≤
        tupleMass (indexedPackets A) (floorCopies A μ n)
          (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ := by
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq V := Classical.decEq V
  intro B hL hB hBX ℓ hℓ1 hℓ3 R hR1 hRℓ
  let A := allowed H F
  let n := (Fintype.card X : ℝ)
  have hNF : max (supersaturationOrder α) ⌈2*C⌉₊ ≤ Fintype.card X := by
    unfold embeddedMixedEligibilityOrder at hN
    omega
  have hnNat : 0 < Fintype.card X := by
    have hSix : 6 ≤ Fintype.card X :=
      (le_max_left _ _).trans ((le_max_left _ _).trans hNF)
    omega
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hnNat
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hFloorUp : ∀ T ∈ A, floorWeights A μ n T ≤ C/n := by
    intro T hT
    have hAllow := isAllowed_of_mem_allowed hT
    exact (floorWeights_bounds A μ hC0 hn
      (fun Q hQ => hLow Q (isAllowed_of_mem_allowed hQ)) hT).2.trans (hUp T hAllow)
  have hTarget := floor_target_lower_of_nonempty_index_family hH3 hα hC hLow hUp hNF R
    (card_pos.mp (by omega : 0 < R.card))
  have hScale : ((6*C^3+localMixedDegreeScale C L)/(massConstant α C/16))^2 ≤ n := by
    apply Nat.ceil_le.mp
    unfold embeddedMixedEligibilityOrder at hN
    omega
  exact embedded_padded_floor_tuple_eligible e A B μ C (massConstant α C/16) L hC
    (by unfold massConstant; positivity) hnNat
    (fun T hT => (isAllowed_of_mem_allowed hT).1) hL hB hBX hFloorUp hTarget hScale
    ℓ hℓ1 hℓ3 R hR1 hRℓ

#print axioms raw_embedded_padded_tuple_eligible
end TypedTriangle.Pasch
