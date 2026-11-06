module
public import RequestProject.TypedTriangle.PaschPaddedCloneEligibility
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

def mixedEligibilityOrder (α C : ℝ) (L : ℕ) : ℕ :=
  max (floorEligibilityOrder α C)
    ⌈((6*C^3 + mixedDegreeScale C L)/(massConstant α C/16))^2⌉₊

variable {V I : Type*} [Fintype V]

/-- The original H1 and H3 discharge every actual clone eligibility
condition for the padded mixed bank tests. There is no new mass, degree,
or completion-provider assumption on the host. -/
theorem host_floor_padded_tuple_eligible {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (L : ℕ) (hN : mixedEligibilityOrder α C L ≤ Fintype.card V) :
    letI : DecidableEq V := Classical.decEq V
    ∀ (B : Finset (Finset V)), PairCodegreeBound B L →
      (∀ T ∈ B, T.card = 3) → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 3 →
      ∀ R : Finset (allowed H F), 1 ≤ R.card → R.card ≤ ℓ →
      let A := allowed H F
      let n := (Fintype.card V : ℝ)
      tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ R *
          (n^2)^((R.card : ℝ)+1/4) ≤
        tupleMass (indexedPackets A) (floorCopies A μ n)
          (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ := by
  letI : DecidableEq V := Classical.decEq V
  intro B hL hB ℓ hℓ1 hℓ3 R hR1 hRℓ
  let A := allowed H F
  let n := (Fintype.card V : ℝ)
  have hNF : floorEligibilityOrder α C ≤ Fintype.card V := by
    unfold mixedEligibilityOrder at hN
    omega
  have hNS : supersaturationOrder α ≤ Fintype.card V := by
    unfold floorEligibilityOrder at hNF
    omega
  have hnNat : 0 < Fintype.card V := by
    unfold floorEligibilityOrder at hNF
    omega
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hnNat
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < massConstant α C := by unfold massConstant; positivity
  have hRound : 2*C ≤ n := by
    apply Nat.ceil_le.mp
    unfold floorEligibilityOrder at hNF
    omega
  have hLow : ∀ T ∈ A, 1/(C*n) ≤ μ T :=
    fun T hT => (hH1.1 T (isAllowed_of_mem_allowed hT)).1
  have hUp : ∀ T ∈ A, μ T ≤ C/n :=
    fun T hT => (hH1.1 T (isAllowed_of_mem_allowed hT)).2
  have hFloorUp : ∀ T ∈ A, floorWeights A μ n T ≤ C/n :=
    fun T hT => (floorWeights_bounds A μ hC0 hn hLow hT).2.trans (hUp T hT)
  by_cases hE : edges H = ∅
  · exfalso
    obtain ⟨i, _⟩ := card_pos.mp (show 0 < R.card by omega)
    have hHas : (allowed H F).Nonempty := ⟨i.val, i.property⟩
    rw [allowed_empty_of_edges_empty hE] at hHas
    exact not_nonempty_empty hHas
  · have hSource := (target_lower_or_empty hH1 hH3 hα hC0 hNS).resolve_left hE
    have hSource0 : 0 ≤ target μ A := (by positivity : (0 : ℝ) ≤ massConstant α C*n^2).trans hSource
    have hRounded := floorWeights_target_lower A μ hC0 hn
      (by linarith only [hRound, hC0]) hLow
    have hFactor := fourth_rounding_factor_lower
      ((div_le_iff₀ hn).2 (by linarith only [hRound]) : C/n ≤ (1/2 : ℝ))
    have hFloorTarget : (massConstant α C/16)*n^2 ≤ target (floorWeights A μ n) A := by
      have h1 := mul_le_mul_of_nonneg_right hFactor hSource0
      have h2 := div_le_div_of_nonneg_right hSource (by norm_num : (0 : ℝ) ≤ 16)
      nlinarith only [h1, h2, hRounded]
    have hScale : ((6*C^3 + mixedDegreeScale C L)/(massConstant α C/16))^2 ≤ n := by
      apply Nat.ceil_le.mp
      unfold mixedEligibilityOrder at hN
      omega
    exact padded_floor_tuple_eligible A B μ C (massConstant α C/16) L hC (by positivity)
      hnNat (fun T hT => (isAllowed_of_mem_allowed hT).1) hL hB hFloorUp
      hFloorTarget hScale ℓ hℓ1 hℓ3 R hR1 hRℓ

#print axioms host_floor_padded_tuple_eligible
end TypedTriangle.Pasch
