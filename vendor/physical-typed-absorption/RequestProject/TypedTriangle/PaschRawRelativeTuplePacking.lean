module
public import RequestProject.TypedTriangle.PaschRawFractionalTuplePacking
public import RequestProject.TypedTriangle.PaschRawRelativeTupleControl
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone WeightedStar

/-- One raw near-packing simultaneously retains relative positive linear
monitors and all eligible extra tuple tests. The linear quota is a condition
on the test; no exact diffuse seed or physicality is assumed. -/
theorem raw_fractional_packing_with_pasch_relative_and_tuple_tests (a b α η c ζ : ℝ) (q : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) (hη : 0 < η) (hc : 0 < c) (hζ : 0 < ζ) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ) (ε : ℝ), N ≤ Fintype.card V → 0 ≤ ε → ε ≤ 1/2 →
      (∀ T, IsAllowed H F T → a/Fintype.card V ≤ φ T ∧ φ T ≤ b/Fintype.card V) →
      (∀ e ∈ edges H, |bdry H F φ e-1| ≤ ε) → CommonNbrCond H F α →
      ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
      Fintype.card κ ≤ (Fintype.card V)^q →
      (∀ k T, 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, (∑ T ∈ allowed H F, (φ T/(1+ε))*W k T) = 0 ∨
        c*Fintype.card V ≤ ∑ T ∈ allowed H F, (φ T/(1+ε))*W k T) →
      ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
      Fintype.card ν ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤
          (2*ε+η)*Fintype.card V) ∧
        (count P:ℝ) ≤ rawPaschPackingCost a b*(Fintype.card V:ℝ)^2 ∧
        (∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, (φ T/(1+ε))*W k T)| ≤
          ζ*(∑ T ∈ allowed H F, (φ T/(1+ε))*W k T)) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
          floorTupleTestControl (allowed H F) (fun T => φ T/(1+ε)) P (X ℓ k) ℓ := by
  let C := rawProfileConstant a b
  have hC : 1 ≤ C := rawProfileConstant_one_le a b
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨NRaw,hRaw⟩ := raw_fractional_packing_with_pasch_and_tuple_tests
    a b α η (q+1) ha hab hα hη
  obtain ⟨NNum,hNum1,hNum⟩ := exists_egj13_square_order C c (ζ/2) 0 0 hc (by positivity)
  refine ⟨max NRaw (max 2 (max NNum ⌈4/c^2⌉₊)),?_⟩
  intro V I _ H F φ ε hn hε hεHalf hWindow hLoad h3 κ _ W hκ hW hQuota ν _ X hν hX
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hNNum : NNum ≤ Fintype.card V := by omega
  obtain ⟨_,_,_,_,_,hρ,hRound,_,hRatio⟩ := hNum (Fintype.card V) hNNum
  have hSqrt : Real.sqrt (Fintype.card V:ℝ) ≤ c*Fintype.card V/2 := by
    apply sqrt_le_linear_of_order hc hn0
    exact (Nat.le_ceil (4/c^2)).trans
      (by exact_mod_cast (show ⌈4/c^2⌉₊ ≤ Fintype.card V by omega))
  let μ : Finset V → ℝ := fun T => φ T/(1+ε)
  have hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card V) ≤ μ T := by
    intro T hT
    exact (raw_normalized_coefficient_window ha hε hεHalf hn0 (hWindow T hT)).1
  let Y : ℕ → κ ⊕ ν → Finset (Finset V) → ℝ := fun ℓ =>
    Sum.elim (fun k => if ℓ = 1 then linearTupleWeight (W k) else fun _ => 0) (X ℓ)
  have hY : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Y ℓ k S := by
    intro ℓ hℓ hℓ4 k S
    rcases k with k | k
    · dsimp only [Y,Sum.elim_inl]
      split_ifs
      · exact sum_nonneg (fun T _ => (hW k T).1)
      · exact le_rfl
    · exact hX ℓ hℓ hℓ4 k S
  have hCard : Fintype.card (κ ⊕ ν) ≤ (Fintype.card V)^(q+1) := by
    calc
      Fintype.card (κ ⊕ ν) = Fintype.card κ+Fintype.card ν := Fintype.card_sum
      _ ≤ (Fintype.card V)^q+(Fintype.card V)^q := Nat.add_le_add hκ hν
      _ = 2*(Fintype.card V)^q := by omega
      _ ≤ Fintype.card V*(Fintype.card V)^q := Nat.mul_le_mul_right _ hn2
      _ = (Fintype.card V)^(q+1) := (pow_succ' _ _).symm
  obtain ⟨P,hPsub,hP,hNear,hCount,hControls⟩ := hRaw H F φ ε
    ((le_max_left _ _).trans hn) hε hεHalf hWindow hLoad h3 (κ ⊕ ν) Y hCard hY
  refine ⟨P,hPsub,hP,hNear,hCount,?_,?_⟩
  · intro k
    have hControl : floorTupleTestControl (allowed H F) μ P (linearTupleWeight (W k)) 1 := by
      simpa [Y,μ] using hControls 1 (by omega) (by omega) (Sum.inl k)
    have hh := relative_error_of_floor_linear_control_of_coefficients hLow hC0 hc
      (show 0 ≤ ζ/2 by positivity) hn0 hRound hSqrt hρ hRatio P (W k) (hW k) (hQuota k) hControl
    convert hh using 1 <;> ring
  · intro ℓ hℓ hℓ4 k
    simpa only [Y,Sum.elim_inr] using hControls ℓ hℓ hℓ4 (Sum.inr k)

#print axioms raw_fractional_packing_with_pasch_relative_and_tuple_tests
end TypedTriangle.Pasch
