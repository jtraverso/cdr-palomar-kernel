module
public import RequestProject.TypedTriangle.PaschRawRelativeTuplePacking
public import RequestProject.TypedTriangle.PaschRawAmbientMonitor
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

/-- A genuine raw near-packing with the actual ambient monitor, whose
quota follows from the profile window, positive loads and H3. Every sampled
subfamily inherits its nonnegative ambient upper bound. Arbitrary extra
tuple tests share the same packing and retain their actual eligibility clause. -/
theorem raw_fractional_packing_with_pasch_ambient_and_tuple_tests (a b α η ζ : ℝ) (q : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ) (ε : ℝ), N ≤ Fintype.card V → 0 ≤ ε → ε ≤ 1/2 →
      (∀ T, IsAllowed H F T → a/Fintype.card V ≤ φ T ∧ φ T ≤ b/Fintype.card V) →
      (∀ e ∈ edges H, |bdry H F φ e-1| ≤ ε) → CommonNbrCond H F α →
      ∀ (Z : Type) [Fintype Z] (e : V ↪ Z) (Rprev : Finset (Finset Z)) (Lprev : ℕ),
      PairCodegreeBound Rprev Lprev →
      ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
      Fintype.card ν ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤
          (2*ε+η)*Fintype.card V) ∧
        (count P:ℝ) ≤ rawPaschPackingCost a b*(Fintype.card V:ℝ)^2 ∧
        (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
            (∑ T ∈ allowed H F, (φ T/(1+ε))*childPaddedWeight e Rprev Lprev T)| ≤
          ζ*(∑ T ∈ allowed H F, (φ T/(1+ε))*childPaddedWeight e Rprev Lprev T)) ∧
        (∀ D ⊆ P, (∑ T ∈ D, childPaddedWeight e Rprev Lprev T) ≤
          (1+ζ)*b*Fintype.card V) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
          floorTupleTestControl (allowed H F) (fun T => φ T/(1+ε)) P (X ℓ k) ℓ := by
  have hb : 0 < b := ha.trans_le hab
  let c := (a/2)*α^3/54
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N,hRaw⟩ := raw_fractional_packing_with_pasch_relative_and_tuple_tests
    a b α η c ζ q ha hab hα hη hc hζ
  refine ⟨max N 1,?_⟩
  intro V I _ H F φ ε hn hε hεHalf hWindow hLoad h3 Z _ e Rprev Lprev hPrev
    ν _ X hν hX
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hDen : 0 < 1+ε := by linarith only [hε]
  let μ : Finset V → ℝ := fun T => φ T/(1+ε)
  have hμ (T : Finset V) (hT : IsAllowed H F T) :
      (a/2)/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V := by
    obtain ⟨hl,hu⟩ := hWindow T hT
    have hφ0 : 0 ≤ φ T := (by positivity : (0:ℝ) ≤ a/Fintype.card V).trans hl
    constructor
    · calc
        _ = (a/Fintype.card V)/2 := by ring
        _ ≤ (a/Fintype.card V)/(1+ε) := div_le_div_of_nonneg_left
          (by positivity : (0:ℝ) ≤ a/Fintype.card V) hDen (by linarith only [hεHalf])
        _ ≤ _ := div_le_div_of_nonneg_right hl hDen.le
    · exact (div_le_self hφ0 (by linarith only [hε] : 1 ≤ 1+ε)).trans hu
  have hμLoad : ∀ f ∈ edges H, 0 < bdry H F μ f := by
    intro f hf
    rw [bdry_div_constant]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/3)
      (raw_normalized_load_window hε hεHalf (hLoad f hf)).2.1
  have hW : ∀ (_k : Unit) T, 0 ≤ childPaddedWeight e Rprev Lprev T ∧
      childPaddedWeight e Rprev Lprev T ≤ 1 :=
    fun _ T => childPaddedWeight_bounds e Rprev Lprev hPrev hn1 T
  have hQuota : (∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T) = 0 ∨
      c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T := by
    rcases raw_child_padded_target_lower_or_empty e Rprev Lprev hPrev
      (show 0 < a/2 by positivity) hα hn0 (fun T hT => (hμ T hT).1) hμLoad h3
      with hEmpty | hPositive
    · exact Or.inl hEmpty.2
    · exact Or.inr hPositive
  have hUnit : Fintype.card Unit ≤ (Fintype.card V)^q := by
    change 1 ≤ (Fintype.card V)^q
    exact one_le_pow₀ hn1
  obtain ⟨P,hPsub,hP,hNear,hCount,hRelative,hControls⟩ := hRaw H F φ ε
    ((le_max_left _ _).trans hn) hε hεHalf hWindow hLoad h3 Unit
      (fun _ => childPaddedWeight e Rprev Lprev) hUnit hW (fun _ => hQuota) ν X hν hX
  have hUpper := raw_child_padded_target_upper e Rprev Lprev hPrev hb.le hn0
    (fun T hT => ⟨(by positivity : (0:ℝ) ≤ (a/2)/Fintype.card V).trans (hμ T hT).1,(hμ T hT).2⟩)
  refine ⟨P,hPsub,hP,hNear,hCount,hRelative (),?_,hControls⟩
  intro D hD
  calc
    _ ≤ ∑ T ∈ P, childPaddedWeight e Rprev Lprev T :=
      sum_le_sum_of_subset_of_nonneg hD (fun T _ _ => (hW () T).1)
    _ ≤ (1+ζ)*(∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T) := by
      have hh := (abs_le.mp (hRelative ())).2
      linarith only [hh]
    _ ≤ (1+ζ)*(b*Fintype.card V) := mul_le_mul_of_nonneg_left hUpper (by positivity)
    _ = _ := by ring

#print axioms raw_fractional_packing_with_pasch_ambient_and_tuple_tests
end TypedTriangle.Pasch
