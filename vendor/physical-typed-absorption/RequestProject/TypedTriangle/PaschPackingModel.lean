module
public import RequestProject.TypedTriangle.PaschFloorInputs
public import RequestProject.TypedTriangle.ClonedFloorLinear
public import RequestProject.TypedTriangle.PaschActiveStars
public import RequestProject.TypedTriangle.PaschTargetUpper
public import RequestProject.TypedTriangle.PaschEGJ13Numerics
public import RequestProject.TypedTriangle.PaschFractionalTarget
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
variable {V κ : Type*} [Fintype V] [Fintype κ]

abbrev PackingMonitor (V κ : Type*) := V ⊕ (κ ⊕ Unit)

def packingTupleWeight (D : Finset (Finset V)) (W : κ → Finset V → ℝ) (ℓ : ℕ)
    (k : PackingMonitor V κ) (S : Finset D) : ℝ :=
  if ℓ = 1 then
    match k with
    | Sum.inl v => linearTupleWeight (fun i => WeightedStar.starWeight v i.val) S
    | Sum.inr (Sum.inl k) => linearTupleWeight (fun i => W k i.val) S
    | Sum.inr (Sum.inr _) => 0
  else if ℓ = 4 then
    match k with
    | Sum.inr (Sum.inr _) => indexedWeight D S
    | _ => 0
  else 0

theorem packingTupleWeight_star (D : Finset (Finset V)) (W : κ → Finset V → ℝ) (v : V) :
    packingTupleWeight D W 1 (Sum.inl v) = linearTupleWeight (fun i => WeightedStar.starWeight v i.val) := by
  funext S
  simp [packingTupleWeight]

theorem packingTupleWeight_test (D : Finset (Finset V)) (W : κ → Finset V → ℝ) (k : κ) :
    packingTupleWeight D W 1 (Sum.inr (Sum.inl k)) = linearTupleWeight (fun i => W k i.val) := by
  funext S
  simp [packingTupleWeight]

theorem packingTupleWeight_pasch (D : Finset (Finset V)) (W : κ → Finset V → ℝ) :
    packingTupleWeight D W 4 (Sum.inr (Sum.inr ())) = indexedWeight D := by
  funext S
  simp [packingTupleWeight]

theorem packingTupleWeight_nonneg (D : Finset (Finset V)) (W : κ → Finset V → ℝ)
    (hW : ∀ k T, T ∈ D → 0 ≤ W k T) (ℓ : ℕ) (k : PackingMonitor V κ) (S : Finset D) :
    0 ≤ packingTupleWeight D W ℓ k S := by
  unfold packingTupleWeight
  split_ifs
  · rcases k with v | k
    · apply sum_nonneg
      intro i _
      unfold WeightedStar.starWeight
      split_ifs <;> norm_num
    · rcases k with k | u
      · exact sum_nonneg (fun i _ => hW k i.val i.property)
      · exact le_rfl
  · rcases k with v | k
    · exact le_rfl
    · rcases k with k | u
      · exact le_rfl
      · exact indexedWeight_nonneg D S
  · exact le_rfl

theorem packingMonitor_card_le (q : ℕ) (hn : 2 ≤ Fintype.card V)
    (hκ : Fintype.card κ ≤ (Fintype.card V)^q) :
    Fintype.card (PackingMonitor V κ) ≤ (Fintype.card V)^(q+3) := by
  let n := Fintype.card V
  have hn1 : 1 ≤ n := by omega
  have hnp : n ≤ n^(q+1) := le_self_pow₀ hn1 (by omega)
  have hqp : n^q ≤ n^(q+1) := pow_le_pow_right₀ hn1 (Nat.le_succ q)
  have h1p : 1 ≤ n^(q+1) := one_le_pow₀ hn1
  have h3 : 3 ≤ n^2 := by nlinarith only [hn]
  have hk : Fintype.card κ ≤ n^(q+1) := hκ.trans hqp
  calc
    Fintype.card (PackingMonitor V κ) = n+Fintype.card κ+1 := by simp [PackingMonitor,n,Nat.add_assoc]
    _ ≤ 3*n^(q+1) := by omega
    _ ≤ n^2*n^(q+1) := Nat.mul_le_mul_right _ h3
    _ = n^(q+3) := by rw [← pow_add]; congr 1; omega

theorem sqrt_le_linear_of_order {d n : ℝ} (hd : 0 < d) (hn : 0 < n) (hN : 4/d^2 ≤ n) :
    Real.sqrt n ≤ d*n/2 := by
  have h4 := (div_le_iff₀ (pow_pos hd 2)).mp hN
  have hh := mul_le_mul_of_nonneg_right h4 hn.le
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity,by nlinarith only [hh]⟩

/-- Convert the actual clone matching estimate to the original linear seed
statistic. The same lemma applies to active vertex stars and supplied tests. -/
theorem linear_floor_test_error {ι : Type*} [Fintype ι] {C n ε ρ : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) (hRatio : C/n ≤ ε)
    (φ a : ι → ℝ) (hφ : ∀ i, 1/(C*n) ≤ φ i) (ha : ∀ i, 0 ≤ a i)
    (Q : Finset ι)
    (hTest : |(∑ i ∈ Q, a i) - normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a| ≤
      ρ*normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a) :
    |(∑ i ∈ Q, a i) - (∑ i, φ i*a i)| ≤ 2*ε*(∑ i, φ i*a i) := by
  let mass := normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a
  let source := ∑ i, φ i*a i
  have hs0 : 0 ≤ source := sum_nonneg (fun i _ => mul_nonneg
    ((by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hφ i)) (ha i))
  have hm0 : 0 ≤ mass := sum_nonneg (fun i _ => mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (sq_nonneg n)) (ha i))
  have hm := (floor_linear_mass_bounds hC hn φ a hφ ha).2
  have hMatch : ρ*mass ≤ ε*source := mul_le_mul hρε hm hm0 hε
  have hBias := (floor_linear_mass_close hC hn φ a hφ ha).trans
    (mul_le_mul_of_nonneg_right hRatio hs0)
  calc
    |(∑ i ∈ Q, a i)-source| ≤ |(∑ i ∈ Q, a i)-mass|+|mass-source| := abs_sub_le _ _ _
    _ ≤ ε*source+ε*source := add_le_add (hTest.trans hMatch) hBias
    _ = _ := by ring

#print axioms packingTupleWeight_nonneg
#print axioms packingMonitor_card_le
#print axioms sqrt_le_linear_of_order
#print axioms linear_floor_test_error
end TypedTriangle.Pasch
