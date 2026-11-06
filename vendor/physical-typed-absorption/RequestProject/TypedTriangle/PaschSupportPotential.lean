module
public import RequestProject.TypedTriangle.PaschFreeCoordinateAveraging
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V J K : Type*} [DecidableEq V] [Fintype V]
  [Fintype J] [DecidableEq J] [Fintype K]

/-- One potential controls all indicated support triples simultaneously.
Each form designates a free coordinate; its other two vertices depend only on the remaining coordinates. -/
def supportCompletionCost (R : Finset (Finset V)) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → V) → V) (f : J → V) : ℕ :=
  ∑ k : K, rootedCount
    (insert {a k (fun j => f j.val),b k (fun j => f j.val),f (i k)} R)
    {a k (fun j => f j.val),b k (fun j => f j.val),f (i k)}

theorem sum_supportCompletionCost_le (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → V) → V) :
    (∑ f : J → V, supportCompletionCost R i a b f) ≤
      Fintype.card (J → V) * (Fintype.card K * L^3) := by
  simp only [supportCompletionCost]
  rw [sum_comm]
  calc (∑ k : K, ∑ f : J → V, rootedCount
        (insert {a k (fun j => f j.val),b k (fun j => f j.val),f (i k)} R)
        {a k (fun j => f j.val),b k (fun j => f j.val),f (i k)})
      ≤ ∑ _k : K, Fintype.card (J → V)*L^3 := by
        apply sum_le_sum
        intro k _
        exact sum_free_coordinate_completions_le R L hL (i k) (a k) (b k)
    _ = _ := by simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

/-- A single valid assignment pays the entire support potential. The
candidate family P is retained; no separate selections of its triangles are made. -/
theorem exists_low_support_potential (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (i : K → J)
    (a b : ∀ k, ({j : J // j ≠ i k} → V) → V) (P : Finset (J → V)) (κ : ℝ)
    (hκ : 0 < κ) (hN : 0 < (Fintype.card (J → V):ℝ))
    (hP : κ*(Fintype.card (J → V):ℝ) ≤ P.card) :
    ∃ f ∈ P, (supportCompletionCost R i a b f:ℝ) ≤ ((Fintype.card K:ℝ)*(L:ℝ)^3)/κ := by
  have hPos : 0 < (P.card:ℝ) := (mul_pos hκ hN).trans_le hP
  obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image P (supportCompletionCost R i a b)
    (card_pos.mp (by exact_mod_cast hPos))
  have hAverage : P.card*supportCompletionCost R i a b f ≤
      Fintype.card (J → V)*(Fintype.card K*L^3) := by
    calc P.card*supportCompletionCost R i a b f =
        ∑ _g ∈ P, supportCompletionCost R i a b f := by simp
      _ ≤ ∑ g ∈ P, supportCompletionCost R i a b g := sum_le_sum (fun g hg => hmin g hg)
      _ ≤ ∑ g : J → V, supportCompletionCost R i a b g := sum_le_sum_of_subset (subset_univ P)
      _ ≤ _ := sum_supportCompletionCost_le R L hL i a b
  refine ⟨f,hf,?_⟩
  have hb : (P.card:ℝ)*(supportCompletionCost R i a b f:ℝ) ≤
      (Fintype.card (J → V):ℝ)*((Fintype.card K:ℝ)*(L:ℝ)^3) := by exact_mod_cast hAverage
  have hb' := (mul_le_mul_of_nonneg_right hP
    (show 0 ≤ (supportCompletionCost R i a b f:ℝ) by positivity)).trans hb
  apply (le_div_iff₀ hκ).mpr
  apply (mul_le_mul_iff_left₀ hN).mp
  convert hb' using 1 <;> ring

#print axioms sum_supportCompletionCost_le
#print axioms exists_low_support_potential
end TypedTriangle.Pasch
