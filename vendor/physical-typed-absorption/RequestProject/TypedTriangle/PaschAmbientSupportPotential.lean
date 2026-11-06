module
public import RequestProject.TypedTriangle.PaschAmbientChildSupport
public import RequestProject.TypedTriangle.PaschSupportPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace TypedTriangle.Pasch
variable {X V J K : Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype K]

theorem sum_rooted_completions_embedded_le_any (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (a b : V) :
    (∑ x : X, rootedCount (insert {a,b,e x} R) {a,b,e x}) ≤ Fintype.card V*L^3 := by
  calc
    _ = ∑ c ∈ (univ : Finset X).map e, rootedCount (insert {a,b,c} R) {a,b,c} := by rw [sum_map]
    _ ≤ ∑ c : V, rootedCount (insert {a,b,c} R) {a,b,c} := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := sum_rooted_completions_le_any R L hL a b

/-- Tensorization separates one child coordinate while keeping all other
endpoints ambient and dependent on the remaining child coordinates. -/
theorem card_mul_sum_embedded_free_coordinate_le (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (i : J)
    (a b : ({j : J // j ≠ i} → X) → V) :
    Fintype.card X*(∑ f : J → X, rootedCount
      (insert {a (fun j => f j.val),b (fun j => f j.val),e (f i)} R)
      {a (fun j => f j.val),b (fun j => f j.val),e (f i)}) ≤
        Fintype.card (J → X)*Fintype.card V*L^3 := by
  let Rest := {j : J // j ≠ i} → X
  let cost (r : Rest) (c : X) := rootedCount (insert {a r,b r,e c} R) {a r,b r,e c}
  let split : (J → X) ≃ X × Rest := Equiv.funSplitAt i X
  have hSumEq : (∑ f : J → X, cost (fun j => f j.val) (f i)) =
      ∑ p : X × Rest, cost p.2 p.1 := Equiv.sum_comp split (fun p => cost p.2 p.1)
  have hCard : Fintype.card (J → X) = Fintype.card X*Fintype.card Rest := by
    simpa only [Fintype.card_prod] using Fintype.card_congr split
  have hSum : (∑ f : J → X, cost (fun j => f j.val) (f i)) ≤
      Fintype.card Rest*(Fintype.card V*L^3) := by
    calc
      _ = ∑ r : Rest, ∑ c : X, cost r c := by rw [hSumEq,Fintype.sum_prod_type,sum_comm]
      _ ≤ ∑ _r : Rest, Fintype.card V*L^3 :=
        sum_le_sum (fun r _ => sum_rooted_completions_embedded_le_any e R L hL (a r) (b r))
      _ = _ := by simp
  calc
    _ ≤ Fintype.card X*(Fintype.card Rest*(Fintype.card V*L^3)) := Nat.mul_le_mul_left _ hSum
    _ = _ := by rw [hCard]; ring

def embeddedSupportCompletionCost (e : X ↪ V) (R : Finset (Finset V)) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → X) → V) (f : J → X) : ℕ :=
  ∑ k : K, rootedCount
    (insert {a k (fun j => f j.val),b k (fun j => f j.val),e (f (i k))} R)
    {a k (fun j => f j.val),b k (fun j => f j.val),e (f (i k))}

theorem card_mul_sum_embedded_supportCost_le (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → X) → V) :
    Fintype.card X*(∑ f : J → X, embeddedSupportCompletionCost e R i a b f) ≤
      Fintype.card (J → X)*Fintype.card V*(Fintype.card K*L^3) := by
  simp only [embeddedSupportCompletionCost]
  rw [sum_comm,mul_sum]
  calc
    _ ≤ ∑ _k : K, Fintype.card (J → X)*Fintype.card V*L^3 := by
      apply sum_le_sum
      intro k _
      exact card_mul_sum_embedded_free_coordinate_le e R L hL (i k) (a k) (b k)
    _ = _ := by simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

/-- One assignment in the original positive-density family pays all
ambient support forms. The factor |V|/|X| is retained exactly. -/
theorem exists_low_embedded_support_potential (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → X) → V) (P : Finset (J → X)) (κ : ℝ)
    (hκ : 0 < κ) (hnX : 0 < (Fintype.card X : ℝ))
    (hP : κ*(Fintype.card (J → X) : ℝ) ≤ P.card) :
    ∃ f ∈ P, (embeddedSupportCompletionCost e R i a b f : ℝ) ≤
      ((Fintype.card V : ℝ)/Fintype.card X)*((Fintype.card K : ℝ)*(L : ℝ)^3)/κ := by
  have hnXNat : 0 < Fintype.card X := by exact_mod_cast hnX
  obtain ⟨x0⟩ : Nonempty X := Fintype.card_pos_iff.mp hnXNat
  have hNNat : 0 < Fintype.card (J → X) := Fintype.card_pos_iff.mpr ⟨fun _ => x0⟩
  have hN : 0 < (Fintype.card (J → X) : ℝ) := by exact_mod_cast hNNat
  let cost := embeddedSupportCompletionCost e R i a b
  have hPos : 0 < (P.card : ℝ) := (mul_pos hκ hN).trans_le hP
  obtain ⟨f,hf,hMin⟩ := exists_min_image P cost (card_pos.mp (by exact_mod_cast hPos))
  have hPartial : P.card*cost f ≤ ∑ g : J → X, cost g := by
    calc
      _ = ∑ _g ∈ P, cost f := by simp
      _ ≤ ∑ g ∈ P, cost g := sum_le_sum (fun g hg => hMin g hg)
      _ ≤ _ := sum_le_sum_of_subset (subset_univ P)
  have hAverage : Fintype.card X*(P.card*cost f) ≤
      Fintype.card (J → X)*Fintype.card V*(Fintype.card K*L^3) :=
    (Nat.mul_le_mul_left _ hPartial).trans (card_mul_sum_embedded_supportCost_le e R L hL i a b)
  have hAverageR : (Fintype.card X : ℝ)*((P.card : ℝ)*(cost f : ℝ)) ≤
      (Fintype.card (J → X) : ℝ)*Fintype.card V*((Fintype.card K : ℝ)*(L : ℝ)^3) := by
    exact_mod_cast hAverage
  have hCombined := (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg (cost f)))
    (Nat.cast_nonneg (Fintype.card X))).trans hAverageR
  have hCancel : κ*(Fintype.card X : ℝ)*(cost f : ℝ) ≤
      (Fintype.card V : ℝ)*((Fintype.card K : ℝ)*(L : ℝ)^3) := by
    apply (mul_le_mul_iff_left₀ hN).mp
    convert hCombined using 1 <;> ring
  have hBound : (cost f : ℝ) ≤
      ((Fintype.card V : ℝ)*((Fintype.card K : ℝ)*(L : ℝ)^3))/(κ*Fintype.card X) := by
    apply (le_div_iff₀ (mul_pos hκ hnX)).mpr
    convert hCancel using 1 <;> ring
  have hEq : ((Fintype.card V : ℝ)*((Fintype.card K : ℝ)*(L : ℝ)^3))/(κ*Fintype.card X) =
      ((Fintype.card V : ℝ)/Fintype.card X)*((Fintype.card K : ℝ)*(L : ℝ)^3)/κ := by
    field_simp [ne_of_gt hκ,ne_of_gt hnX] <;> ring
  exact ⟨f,hf,hEq ▸ hBound⟩

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.sum_rooted_completions_embedded_le_any
#print axioms TypedTriangle.Pasch.card_mul_sum_embedded_free_coordinate_le
#print axioms TypedTriangle.Pasch.card_mul_sum_embedded_supportCost_le
#print axioms TypedTriangle.Pasch.exists_low_embedded_support_potential
