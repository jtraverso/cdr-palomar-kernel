module
public import RequestProject.TypedTriangle.PaschEdgeSelection
public import Mathlib.Logic.Equiv.Prod
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem rootedCount_eq_zero_of_small_root (D : Finset (Finset V)) (Q : Finset V)
    (hQ : Q.card < 3) : rootedCount D Q = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hCfg,hQS⟩ := mem_filter.mp hS
  have hc := (mem_configurations.mp hCfg).2.2.2.1 Q hQS
  omega

theorem sum_rooted_completions_le_any (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (a b : V) :
    (∑ c : V, rootedCount (insert {a,b,c} R) {a,b,c}) ≤ Fintype.card V * L^3 := by
  by_cases hab : a = b
  · subst b
    have hz (c : V) : rootedCount (insert {a,a,c} R) {a,a,c} = 0 := by
      apply rootedCount_eq_zero_of_small_root
      have hc : ({a,a,c} : Finset V).card ≤ 2 := by simpa using (card_le_two (a := a) (b := c))
      omega
    simp only [hz,sum_const_zero,Nat.zero_le]
  · exact sum_rooted_completions_le R L hL a b hab

/-- Separating one free coordinate preserves the arista average even when
the other endpoints depend on every remaining coordinate. -/
theorem sum_free_coordinate_completions_le {J : Type*} [Fintype J] [DecidableEq J]
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (i : J)
    (a b : ({j : J // j ≠ i} → V) → V) :
    (∑ f : J → V, rootedCount
      (insert {a (fun j => f j.val),b (fun j => f j.val),f i} R)
      {a (fun j => f j.val),b (fun j => f j.val),f i}) ≤ Fintype.card (J → V) * L^3 := by
  let Rest := {j : J // j ≠ i} → V
  let cost (r : Rest) (c : V) := rootedCount (insert {a r,b r,c} R) {a r,b r,c}
  let e : (J → V) ≃ V × Rest := Equiv.funSplitAt i V
  have he : (∑ f : J → V, cost (fun j => f j.val) (f i)) =
      ∑ p : V × Rest, cost p.2 p.1 := by
    exact Equiv.sum_comp e (fun p => cost p.2 p.1)
  have hCard : Fintype.card (J → V) = Fintype.card V * Fintype.card Rest := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  calc (∑ f : J → V, cost (fun j => f j.val) (f i)) =
        ∑ p : V × Rest, cost p.2 p.1 := he
    _ = ∑ r : Rest, ∑ c : V, cost r c := by rw [Fintype.sum_prod_type,sum_comm]
    _ ≤ ∑ _r : Rest, Fintype.card V * L^3 := by
      apply sum_le_sum
      intro r _
      exact sum_rooted_completions_le_any R L hL (a r) (b r)
    _ = Fintype.card (J → V)*L^3 := by simp [hCard,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

/-- A positive-density family of valid assignments contains a bounded-cost
assignment. Candidate geometry is retained as membership in that very family. -/
theorem exists_free_coordinate_completion_bounded {J : Type*} [Fintype J] [DecidableEq J]
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (i : J)
    (a b : ({j : J // j ≠ i} → V) → V) (P : Finset (J → V)) (κ : ℝ)
    (hκ : 0 < κ) (hN : 0 < (Fintype.card (J → V):ℝ))
    (hP : κ*(Fintype.card (J → V):ℝ) ≤ P.card) :
    ∃ f ∈ P, (rootedCount
      (insert {a (fun j => f j.val),b (fun j => f j.val),f i} R)
      {a (fun j => f j.val),b (fun j => f j.val),f i}:ℝ) ≤ (L:ℝ)^3/κ := by
  let cost (f : J → V) := rootedCount
    (insert {a (fun j => f j.val),b (fun j => f j.val),f i} R)
    {a (fun j => f j.val),b (fun j => f j.val),f i}
  have hPos : 0 < (P.card:ℝ) := (mul_pos hκ hN).trans_le hP
  obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image P cost (card_pos.mp (by exact_mod_cast hPos))
  have hAverage : P.card*cost f ≤ Fintype.card (J → V)*L^3 := by
    calc P.card*cost f = ∑ _g ∈ P, cost f := by simp
      _ ≤ ∑ g ∈ P, cost g := sum_le_sum (fun g hg => hmin g hg)
      _ ≤ ∑ g : J → V, cost g := sum_le_sum_of_subset (subset_univ P)
      _ ≤ _ := sum_free_coordinate_completions_le R L hL i a b
  refine ⟨f,hf,?_⟩
  have hb : (P.card:ℝ)*(cost f:ℝ) ≤ (Fintype.card (J → V):ℝ)*(L:ℝ)^3 := by
    exact_mod_cast hAverage
  have hb' := (mul_le_mul_of_nonneg_right hP (show 0 ≤ (cost f:ℝ) by positivity)).trans hb
  apply (le_div_iff₀ hκ).mpr
  apply (mul_le_mul_iff_left₀ hN).mp
  convert hb' using 1 <;> ring

#print axioms rootedCount_eq_zero_of_small_root
#print axioms sum_rooted_completions_le_any
#print axioms sum_free_coordinate_completions_le
#print axioms exists_free_coordinate_completion_bounded
end TypedTriangle.Pasch
