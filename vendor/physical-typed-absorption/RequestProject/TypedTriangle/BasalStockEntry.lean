/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeBasalStock
public import RequestProject.TypedTriangle.CoverDownProtected
public import RequestProject.TypedTriangle.BasalEnvelopeQuantitative
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Cover the actual remaining edges outside a prebuilt basal stock, then
enter its edge universe with ambient integer physicality preserved. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
open BasalIncidence
variable {V I : Type*} [Fintype V]

def candidates (H : Host V I) (F : Set (Multiset I)) (X : Finset (Sym2 V))
    (e : Sym2 V) : Finset V :=
  univ.filter fun w => w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧
    ∀ x ∈ e, s(x,w) ∈ X

lemma good_subset_candidates (H : Host V I) (F : Set (Multiset I))
    (D : Finset (Finset V)) (u v : V) :
    good H F D u v ⊆ candidates H F (cover D) s(u,v) := by
  intro w hw
  obtain ⟨ht,hu,hv⟩ := (mem_filter.mp hw).2
  obtain ⟨_,huw,hvw⟩ := distinct_of_card_three ht.1
  refine mem_filter.mpr ⟨mem_univ _,?_,?_,?_⟩
  · simp only [Sym2.mem_iff,not_or]
    exact ⟨huw.symm,hvw.symm⟩
  · rwa [← tri_eq_insert_toFinset]
  · intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

theorem stock_cover_down {H : Host V I} {F : Set (Multiset I)}
    {D : Finset (Finset V)} {κ : ℝ}
    (hSupply : ∀ u v, H.G.Adj u v → κ * Fintype.card V ≤ (good H F D u v).card)
    (U : Finset (Sym2 V)) (hUH : U ⊆ edges H) (hUX : Disjoint U (cover D))
    {d q : ℕ} (hdeg : ∀ x, (U.filter (fun e => x ∈ e)).card ≤ d)
    (hwin : ((U.card + q * (2*d + 4*q) : ℕ) : ℝ) < q * κ * Fintype.card V) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ U ⊆ C.biUnion triEdges ∧
      C.biUnion triEdges ⊆ U ∪ cover D ∧
      ∀ x, ((C.biUnion triEdges).filter (fun e => x ∈ e)).card ≤ 2*d + 2*q := by
  have hdiag : ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using hUH he)
  apply cover_down H F U (cover D) hUX hdiag (candidates H F (cover D))
  · intro e _ w hw
    exact (mem_filter.mp hw).2
  · exact hdeg
  · intro e he
    have hmass : κ * Fintype.card V ≤ (candidates H F (cover D) e).card := by
      induction e using Sym2.ind with
      | _ u v =>
        have huv : H.G.Adj u v := by simpa [edges] using hUH he
        exact (hSupply u v huv).trans (by exact_mod_cast card_le_card (good_subset_candidates H F D u v))
    have hmul := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    have hreal : ((U.card + q*(2*d+4*q) : ℕ):ℝ) <
        (q:ℝ) * (candidates H F (cover D) e).card := by nlinarith
    rw [show 2*(d+2*q) = 2*d+4*q by ring]
    exact_mod_cast hreal

/-- Entry is into the stock fixed before the residue. Physicality is in
the original ambient host; no intrinsic stock-lattice assertion is hidden. -/
theorem enter_stock {H : Host V I} {F : Set (Multiset I)}
    {D : Finset (Finset V)} {κ : ℝ}
    (hSupply : ∀ u v, H.G.Adj u v → κ * Fintype.card V ≤ (good H F D u v).card)
    (J : Finset (Sym2 V)) (hJH : J ⊆ edges H) (hXJ : cover D ⊆ J)
    (hphys : IsPhysical H F J) {d q : ℕ}
    (hdeg : ∀ x, ((J \ cover D).filter (fun e => x ∈ e)).card ≤ d)
    (hwin : (((J \ cover D).card + q*(2*d+4*q) : ℕ):ℝ) < q*κ*Fintype.card V) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ C.biUnion triEdges ⊆ J ∧
      (J \ C.biUnion triEdges) ⊆ cover D ∧ IsPhysical H F (J \ C.biUnion triEdges) ∧
      ∀ x, ((C.biUnion triEdges).filter (fun e => x ∈ e)).card ≤ 2*d+2*q := by
  obtain ⟨C,hC,hcov,hsub,hcd⟩ := stock_cover_down hSupply (J \ cover D)
    (sdiff_subset.trans hJH) sdiff_disjoint hdeg hwin
  have hCJ : C.biUnion triEdges ⊆ J := hsub.trans (union_subset sdiff_subset hXJ)
  refine ⟨C,hC,hCJ,?_,isPhysical_sdiff_of_decomposition hphys hC.isDecomposition hCJ,hcd⟩
  intro e he
  by_contra heX
  exact (mem_sdiff.mp he).2 (hcov (mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,heX⟩))

theorem cover_down_window (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n m d : ℕ, n₀ ≤ n →
      m ≤ n*d → (d:ℝ) ≤ ε*n →
      ∃ q : ℕ, ((m + q*(2*d+4*q) : ℕ):ℝ) < q*κ*n ∧
        ((2*d+2*q : ℕ):ℝ) ≤ η*n := by
  let θ := min (κ/64) (min (η/64) (1/64))
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hθκ : θ ≤ κ/64 := min_le_left _ _
  have hθη : θ ≤ η/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  refine ⟨θ^2,by positivity,⌈1/θ⌉₊,?_⟩
  intro n m d hn hm hd
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
  have hstrict : (q:ℝ)*11*θ*n < (q:ℝ)*κ*n := by
    have h11 : 11*θ < κ := by linarith
    have hh := mul_lt_mul_of_pos_left h11 (mul_pos hq hnpos)
    nlinarith
  refine ⟨q,?_,?_⟩
  · push_cast
    exact hsum.trans_lt hstrict
  · push_cast
    nlinarith

end TypedTriangle.StockEntry
