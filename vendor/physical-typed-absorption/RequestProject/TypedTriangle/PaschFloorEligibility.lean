module
public import RequestProject.TypedTriangle.PaschIndexedExtensions
public import RequestProject.TypedTriangle.ClonedFloorMultiplicity
public import RequestProject.TypedTriangle.PaschEGJEligibility
public import RequestProject.TypedTriangle.PaschExtensionUniformBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone
variable {V : Type*} [Fintype V]

def floorCopies (D : Finset (Finset V)) (μ : Finset V → ℝ) (n : ℝ) : D → ℕ :=
  floorMultiplicity (n^2) (fun i => μ i.val)

def floorWeights (D : Finset (Finset V)) (μ : Finset V → ℝ) (n : ℝ) : Finset V → ℝ :=
  normalizedWeights D (floorCopies D μ n) (n^2)

theorem floorWeights_nonneg (D : Finset (Finset V)) (μ : Finset V → ℝ) (n : ℝ) (T : Finset V) :
    0 ≤ floorWeights D μ n T := by
  unfold floorWeights normalizedWeights
  split_ifs <;> positivity

theorem floorWeights_bounds (D : Finset (Finset V)) (μ : Finset V → ℝ) {n C : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hμ : ∀ T ∈ D, 1/(C*n) ≤ μ T) {T : Finset V} (hT : T ∈ D) :
    (1-C/n)*μ T ≤ floorWeights D μ n T ∧ floorWeights D μ n T ≤ μ T := by
  have hF := floorMultiplicity_normalized C n hC hn (fun i : D => μ i.val)
    (fun i => hμ i.val i.property) ⟨T,hT⟩
  have hN : floorWeights D μ n T = (floorCopies D μ n ⟨T,hT⟩ : ℝ)/n^2 :=
    normalizedWeights_apply D (floorCopies D μ n) (n^2) ⟨T,hT⟩
  rw [hN]
  exact hF

theorem floorWeights_target_lower (D : Finset (Finset V)) (μ : Finset V → ℝ) {n C : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hRound : C ≤ n) (hμ : ∀ T ∈ D, 1/(C*n) ≤ μ T) :
    (1-C/n)^4*target μ D ≤ target (floorWeights D μ n) D := by
  apply target_multiplicative_lower
  · exact sub_nonneg.mpr ((div_le_one hn).mpr hRound)
  · intro T hT
    exact (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hμ T hT)
  · intro T hT
    exact (floorWeights_bounds D μ hC hn hμ hT).1

theorem floor_actual_mass (D : Finset (Finset V)) (μ : Finset V → ℝ) {n : ℝ} (hn : 0 < n) :
    (n^2)^4*target (floorWeights D μ n) D =
      tupleMass (indexedPackets D) (floorCopies D μ n) (indexedWeight D) 4 := by
  have h := tupleMass_indexed_div D (floorCopies D μ n) (n^2)
  have hp : (n^2)^4 ≠ 0 := ne_of_gt (pow_pos (sq_pos_of_pos hn) 4)
  have he := (eq_div_iff hp).mp h.symm
  exact (mul_comm _ _).trans he

theorem floor_actual_extension_le (D : Finset (Finset V)) (μ : Finset V → ℝ) {n C : ℝ}
    (hC : 1 ≤ C) (hn : 1 ≤ Fintype.card V) (hnEq : n = Fintype.card V)
    (hD : ∀ T ∈ D, T.card = 3) (hLow : ∀ T ∈ D, 1/(C*n) ≤ μ T)
    (hUp : ∀ T ∈ D, μ T ≤ C/n) (R : Finset D) (hR1 : 1 ≤ R.card) (hR4 : R.card ≤ 4) :
    tupleExtensionMass (indexedPackets D) (floorCopies D μ n) (indexedWeight D) 4 R ≤
      (n^2)^(4-R.card)*(2*C^3) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hn0 : 0 < n := by rw [hnEq]; exact_mod_cast (by omega : 0 < Fintype.card V)
  have hRD : indexProjection D R ⊆ D := by
    intro T hT
    obtain ⟨i,_,rfl⟩ := mem_image.mp hT
    exact i.property
  have hNormUp : ∀ T ∈ D, floorWeights D μ n T ≤ C/(Fintype.card V:ℝ) := by
    intro T hT
    rw [← hnEq]
    exact (floorWeights_bounds D μ hC0 hn0 hLow hT).2.trans (hUp T hT)
  have hGamma := extensionMass_le_two_mul_cube D (floorWeights D μ n) (indexProjection D R)
    hC hn hD hRD (by rw [indexProjection_card]; exact hR1) (by rw [indexProjection_card]; exact hR4)
    (fun T _ => floorWeights_nonneg D μ n T) hNormUp
  have hDiv := tupleExtensionMass_indexed_div D (floorCopies D μ n) (n^2) R
  have hBound := (div_le_iff₀ (pow_pos (sq_pos_of_pos hn0) (4-R.card))).mp (hDiv.trans_le hGamma)
  exact hBound.trans_eq (mul_comm _ _)

def floorEligibilityOrder (α C : ℝ) : ℕ :=
  max (supersaturationOrder α) (max 1 (max ⌈2*C⌉₊ ⌈32*C^3/massConstant α C⌉₊))

/-- Every nonempty partial Pasch satisfies the actual integer-clone EGJ
eligibility inequality. All fractional degrees and the mass floor are derived
from H1 and H3; no Pasch-mass or extension provider is assumed. -/
theorem floor_paschtuple_eligible {I : Type*} {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (hN : floorEligibilityOrder α C ≤ Fintype.card V)
    (R : Finset (allowed H F)) (hR1 : 1 ≤ R.card) (hR4 : R.card ≤ 4) :
    let n := (Fintype.card V:ℝ)
    tupleExtensionMass (indexedPackets (allowed H F)) (floorCopies (allowed H F) μ n)
      (indexedWeight (allowed H F)) 4 R * (n^2)^((R.card:ℝ)+(1/4:ℝ)) ≤
        tupleMass (indexedPackets (allowed H F)) (floorCopies (allowed H F) μ n)
          (indexedWeight (allowed H F)) 4 := by
  let D := allowed H F
  let n := (Fintype.card V:ℝ)
  have hNsup : supersaturationOrder α ≤ Fintype.card V := by
    unfold floorEligibilityOrder at hN
    omega
  have hnNat : 1 ≤ Fintype.card V := by
    unfold floorEligibilityOrder at hN
    omega
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast hnNat
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < massConstant α C := by unfold massConstant; positivity
  have hRound : 2*C ≤ n := by
    apply Nat.ceil_le.mp
    unfold floorEligibilityOrder at hN
    omega
  have hScale : 32*C^3 ≤ massConstant α C*n := by
    have hh : 32*C^3/massConstant α C ≤ n := by
      apply Nat.ceil_le.mp
      unfold floorEligibilityOrder at hN
      omega
    exact ((div_le_iff₀ hc).mp hh).trans_eq (mul_comm _ _)
  by_cases hE : edges H = ∅
  · exfalso
    obtain ⟨i,_⟩ := card_pos.mp (show 0 < R.card by omega)
    have hHas : (allowed H F).Nonempty := ⟨i.val,i.property⟩
    rw [allowed_empty_of_edges_empty hE] at hHas
    exact not_nonempty_empty hHas
  · have hSource := (target_lower_or_empty hH1 hH3 hα hC0 hNsup).resolve_left hE
    have hLow : ∀ T ∈ D, 1/(C*n) ≤ μ T := fun T hT =>
      (hH1.1 T (isAllowed_of_mem_allowed hT)).1
    have hUp : ∀ T ∈ D, μ T ≤ C/n := fun T hT =>
      (hH1.1 T (isAllowed_of_mem_allowed hT)).2
    have hRounded := floorWeights_target_lower D μ hC0 hn0 (by linarith only [hRound,hC0]) hLow
    have hGamma := gamma_sqrt_le_rounded_mass hC0.le hc.le hn hRound hScale (le_refl (2*C^3))
      hSource hRounded
    have hDegree := floor_actual_extension_le D μ hC hnNat rfl
      (fun T hT => (isAllowed_of_mem_allowed hT).1) hLow hUp R hR1 hR4
    have hMass := le_of_eq (floor_actual_mass D μ hn0)
    exact tuple_eligibility_of_gamma_sqrt hn0 hR4 hDegree hMass hGamma

#print axioms floorWeights_bounds
#print axioms floorWeights_target_lower
#print axioms floor_actual_mass
#print axioms floor_actual_extension_le
#print axioms floor_paschtuple_eligible
end TypedTriangle.Pasch
