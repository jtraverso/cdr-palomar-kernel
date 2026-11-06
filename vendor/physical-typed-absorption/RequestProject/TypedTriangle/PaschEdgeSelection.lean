module
public import RequestProject.TypedTriangle.PaschEdgeAveraging
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Any nonempty candidate pool contains a vertex with at most the average
rooted-completion cost. The bound is multiplicative and has no rounding loss. -/
theorem exists_rooted_completion_average (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (a b : V) (hab : a ≠ b)
    (W : Finset V) (hW : W.Nonempty) :
    ∃ c ∈ W, W.card * rootedCount (insert {a,b,c} R) {a,b,c} ≤ Fintype.card V * L^3 := by
  let cost (c : V) := rootedCount (insert {a,b,c} R) {a,b,c}
  obtain ⟨c,hc,hmin⟩ := Finset.exists_min_image W cost hW
  refine ⟨c,hc,?_⟩
  calc W.card * cost c = ∑ _x ∈ W, cost c := by simp
    _ ≤ ∑ x ∈ W, cost x := sum_le_sum (fun x hx => hmin x hx)
    _ ≤ ∑ x : V, cost x := sum_le_sum_of_subset (subset_univ W)
    _ ≤ Fintype.card V * L^3 := sum_rooted_completions_le R L hL a b hab

/-- A pool of size κn admits cost at most L³/κ, independent of n.
The pool can impose all the geometric and disjointness requirements of a later constructor. -/
theorem exists_rooted_completion_bounded (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (a b : V) (hab : a ≠ b)
    (W : Finset V) (κ : ℝ) (hκ : 0 < κ) (hn : 0 < (Fintype.card V:ℝ))
    (hW : κ*(Fintype.card V:ℝ) ≤ W.card) :
    ∃ c ∈ W, (rootedCount (insert {a,b,c} R) {a,b,c}:ℝ) ≤ (L:ℝ)^3/κ := by
  have hPos : 0 < (W.card:ℝ) := (mul_pos hκ hn).trans_le hW
  have hNonempty : W.Nonempty := card_pos.mp (by exact_mod_cast hPos)
  obtain ⟨c,hc,hcBound⟩ := exists_rooted_completion_average R L hL a b hab W hNonempty
  refine ⟨c,hc,?_⟩
  have hb : (W.card:ℝ)*(rootedCount (insert {a,b,c} R) {a,b,c}:ℝ) ≤
      (Fintype.card V:ℝ)*(L:ℝ)^3 := by exact_mod_cast hcBound
  have hb' := (mul_le_mul_of_nonneg_right hW
    (show 0 ≤ (rootedCount (insert {a,b,c} R) {a,b,c}:ℝ) by positivity)).trans hb
  apply (le_div_iff₀ hκ).mpr
  apply (mul_le_mul_iff_left₀ hn).mp
  convert hb' using 1 <;> ring

#print axioms exists_rooted_completion_average
#print axioms exists_rooted_completion_bounded
end TypedTriangle.Pasch
