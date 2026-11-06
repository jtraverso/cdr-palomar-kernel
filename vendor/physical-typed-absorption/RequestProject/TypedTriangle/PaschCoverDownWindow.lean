module
public import RequestProject.TypedTriangle.PaschCoverDownPotential
public import RequestProject.TypedTriangle.ExplicitBankCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.StockEntry.Explicit

/- The original numerical proof, retaining the unused half-density margin. -/
theorem cover_down_window_pasch_margin (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) :
    ∀ n m d : ℕ, coverDownOrder κ η ≤ n →
      m ≤ n*d → (d:ℝ) ≤ coverDownBudget κ η*n →
      let q := coverDownQuota κ η n;
      0 < q ∧
      ((m + q*(2*d+4*q) : ℕ):ℝ)+(q:ℝ)*(κ/2)*n ≤ q*κ*n ∧
        ((2*d+2*q : ℕ):ℝ) ≤ η*n := by
  let θ := min (κ/64) (min (η/64) (1/64))
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hθκ : θ ≤ κ/64 := min_le_left _ _
  have hθη : θ ≤ η/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  intro n m d hn hm hd
  change ⌈1/θ⌉₊ ≤ n at hn
  change (d:ℝ) ≤ θ^2*n at hd
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnθ : 1 ≤ θ*n := by
    have h1 : 1/θ ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hh := (div_le_iff₀ hθ).mp h1
    nlinarith
  have hnpos : (0:ℝ) < n := by nlinarith
  let q := ⌈θ*n⌉₊
  have hlo : θ*n ≤ (q:ℝ) := Nat.le_ceil _
  have hhi : (q:ℝ) ≤ 2*θ*n := by
    have h1 : (q:ℝ) < θ*n+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hq : (0:ℝ) < q := by nlinarith
  have hd' : (d:ℝ) ≤ θ*n := by
    have ht : θ^2 ≤ θ := by nlinarith
    exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_right ht hN])
  have hm' : (m:ℝ) ≤ (q:ℝ)*θ*n := by
    have hmR : (m:ℝ) ≤ n*d := by exact_mod_cast hm
    have h1 := mul_le_mul_of_nonneg_left hd hN
    have h2 := mul_le_mul_of_nonneg_right hlo (mul_nonneg hθ.le hN)
    nlinarith
  have hmid : (2*(d:ℝ)+4*q) ≤ 10*θ*n := by linarith
  have hsum : (m:ℝ)+(q:ℝ)*(2*d+4*q) ≤ (q:ℝ)*11*θ*n := by
    have hh := mul_le_mul_of_nonneg_left hmid hq.le
    nlinarith
  have hMargin : (m:ℝ)+(q:ℝ)*(2*d+4*q)+(q:ℝ)*(κ/2)*n ≤ (q:ℝ)*κ*n := by
    have h11 : 11*θ ≤ κ/2 := by linarith only [hθκ,hκ]
    have hh := mul_le_mul_of_nonneg_left h11 (mul_nonneg hq.le hN)
    nlinarith only [hsum,hh]
  refine ⟨by exact_mod_cast hq,?_,?_⟩
  · push_cast
    exact hMargin
  · change ((2*d+2*q:ℕ):ℝ) ≤ η*n
    push_cast
    nlinarith
end TypedTriangle.StockEntry.Explicit

namespace TypedTriangle.Pasch
open StockEntry.Explicit
variable {V I : Type*} [Fintype V]

/-- The native cover-down budgets already leave the half-density margin used
by the actual low-Pasch-cost greedy. No cost-selection oracle is an input. -/
theorem cover_down_native_with_pasch (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (H : Host V I) (F : Set (Multiset I)) (P0 : Finset (Finset V))
    (hP0 : IsPacking H F P0) (U X : Finset (Sym2 V)) (hUX : Disjoint U X)
    (hProtected : Disjoint (P0.biUnion triEdges) (U∪X)) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hOrder : coverDownOrder κ η ≤ Fintype.card V)
    (hCard : U.card ≤ Fintype.card V*d)
    (hSparse : (d : ℝ) ≤ coverDownBudget κ η*Fintype.card V)
    (hSupply : ∀ e ∈ U, κ*(Fintype.card V : ℝ) ≤ (Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      U ⊆ C.biUnion triEdges ∧ C.biUnion triEdges ⊆ U∪X ∧
      (∀ v, (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤ η*Fintype.card V) ∧
      (count (P0∪C) : ℝ) ≤ count P0+2*(U.card : ℝ)/κ := by
  let q := coverDownQuota κ η (Fintype.card V)
  obtain ⟨hq,hMargin,hDegree⟩ := cover_down_window_pasch_margin κ η hκ hη
    (Fintype.card V) U.card d hOrder hCard hSparse
  change 0 < q at hq
  change ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
    (q : ℝ)*κ*Fintype.card V at hMargin
  change ((2*d+2*q : ℕ) : ℝ) ≤ η*Fintype.card V at hDegree
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simpa [q,coverDownQuota,hz] using hq
  have hMargin' : ∀ e ∈ U,
      (U.card : ℝ)+(q : ℝ)*(2*(d+2*q) : ℕ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
        (q : ℝ)*(Cand e).card := by
    intro e he
    calc
      _ = ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V := by
        push_cast
        ring
      _ ≤ (q : ℝ)*κ*Fintype.card V := hMargin
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (hSupply e he) (Nat.cast_nonneg q)
        convert hh using 1 <;> ring
  obtain ⟨C,hC,hPC,hCover,hSub,hDeg,hStat⟩ := cover_down_with_pasch H F P0 hP0 U X hUX
    hProtected hU Cand hCand hq (κ/2) (half_pos hκ) hn hdeg hMargin'
  refine ⟨C,hC,hPC,hCover,hSub,?_,?_⟩
  · intro v
    exact (by exact_mod_cast hDeg v : (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤
      (2*d+2*q : ℕ)).trans hDegree
  · have hEq : (U.card : ℝ)/(κ/2) = 2*(U.card : ℝ)/κ := by
      field_simp [ne_of_gt hκ]
    simpa only [hEq] using hStat

end TypedTriangle.Pasch

#print axioms TypedTriangle.StockEntry.Explicit.cover_down_window_pasch_margin
#print axioms TypedTriangle.Pasch.cover_down_native_with_pasch
