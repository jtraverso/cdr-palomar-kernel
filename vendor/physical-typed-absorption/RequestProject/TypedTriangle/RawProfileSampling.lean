/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.SeedCore
public import RequestProject.TypedTriangle.RawHostWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.RawReference
open S07V24 S07V48
variable {V I : Type*} [Fintype V]

/-- Concentration of a unit-mass vertex weight does not require that it came
from an exact fractional decomposition of the host. -/
theorem unit_weight_tails {q B δ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < Fintype.card V)
    (c : V → ℝ) (hc0 : ∀ v, 0 ≤ c v)
    (hcB : ∀ v, c v ≤ B/Fintype.card V) (hc1 : ∑ v, c v = 1) :
    bprob q univ (fun W => wsum c W < q-δ*q) ≤
        Real.exp (-(δ^2*q^2/(4*B)*Fintype.card V)) ∧
    bprob q univ (fun W => q+δ*q < wsum c W) ≤
        Real.exp (-(δ^2*q^2/(4*B)*Fintype.card V)) := by
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  constructor
  · refine (bprob_mono hq.le hq1 (E := fun W => wsum c W < q-δ*q)
      (E' := fun W => wsum c W ≤ q*1-δ*q)
      (iE' := fun _ => inferInstance) (fun W hw => by linarith)).trans
      ((wtail_lo hq.le hq1 c hc0 hcB (by positivity) hc1 one_pos
        (by positivity) (by nlinarith)).trans (le_of_eq ?_))
    congr 1; field_simp
  · refine (bprob_mono hq.le hq1 (E := fun W => q+δ*q < wsum c W)
      (E' := fun W => q*1+δ*q ≤ wsum c W)
      (iE' := fun _ => inferInstance) (fun W hw => by linarith)).trans
      ((wtail_hi hq.le hq1 c hc0 hcB (by positivity) hc1 one_pos
        (by positivity) (by nlinarith)).trans (le_of_eq ?_))
    congr 1; field_simp

def normalizedCompletion (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (u v a : V) : ℝ :=
  compW H.G H.lab F μ u v a / bdry H F μ s(u,v)

/-- Each edge is normalized by its OWN original load. This is only a test
weight; it is not asserted to be a consistent triangle seed on the host. -/
theorem normalized_completion_bounds {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {b ε : ℝ} (hb : 0 < b) (hε : ε ≤ 1/2)
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (hload : ∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε)
    {u v : V} (huv : H.G.Adj u v) :
    (∀ a, 0 ≤ normalizedCompletion H F μ u v a) ∧
    (∀ a, normalizedCompletion H F μ u v a ≤ (2*b)/Fintype.card V) ∧
    (∑ a, normalizedCompletion H F μ u v a) = 1 ∧
    0 < bdry H F μ s(u,v) ∧ bdry H F μ s(u,v) ≤ 2 := by
  have he : s(u,v) ∈ edges H :=
    mem_filter.mpr ⟨mem_univ _,(SimpleGraph.mem_edgeSet H.G).2 huv⟩
  have hS := abs_le.mp (hload _ he)
  have hSp : 0 < bdry H F μ s(u,v) := by linarith
  have hc0 : ∀ a, 0 ≤ compW H.G H.lab F μ u v a := by
    intro a; unfold compW
    split_ifs with h
    · exact (hμ _ h).1
    · exact le_rfl
  have hcB : ∀ a, compW H.G H.lab F μ u v a ≤ b/Fintype.card V := by
    intro a; unfold compW
    split_ifs with h
    · exact (hμ _ h).2
    · positivity
  refine ⟨fun a => div_nonneg (hc0 a) hSp.le,?_,?_,hSp,by linarith⟩
  · intro a
    unfold normalizedCompletion
    rw [div_le_iff₀ hSp]
    have hnR : (0:ℝ) < Fintype.card V := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨u⟩
    have hf : b/Fintype.card V ≤ (2*b)/Fintype.card V*bdry H F μ s(u,v) := by
      rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hnR]
      nlinarith
    exact (hcB a).trans hf
  · simp only [normalizedCompletion]
    rw [←sum_div,sum_compW_eq_load H.G H.lab F μ huv.ne]
    have heq : (∑ T ∈ univ.filter (fun T => SparseEdge.IsAllowed H.G H.lab F T ∧
        s(u,v) ∈ SparseEdge.triEdges T), μ T) = bdry H F μ s(u,v) := by
      have hsets : univ.filter (fun T => SparseEdge.IsAllowed H.G H.lab F T ∧
          s(u,v) ∈ SparseEdge.triEdges T) = triOn H F s(u,v) := by
        ext T
        simp only [triOn,allowed,mem_filter,mem_univ,true_and]
        rfl
      rw [bdry_eq_sum_triOn]
      rw [hsets]
    rw [heq,div_self hSp.ne']

def rawProfileBad (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (q δ : ℝ) : V×V×Bool → Finset V → Prop
  | (u,v,true) => fun W => H.G.Adj u v ∧
      wsum (normalizedCompletion H F μ u v) W < q-δ*q
  | (u,v,false) => fun W => H.G.Adj u v ∧
      q+δ*q < wsum (normalizedCompletion H F μ u v) W

theorem raw_profile_bad_prob {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {b ε q δ : ℝ} (hb : 0 < b) (hε : ε ≤ 1/2)
    (hq : 0 < q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 0 < Fintype.card V)
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (hload : ∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) (j : V×V×Bool) :
    bprob q univ (rawProfileBad H F μ q δ j) ≤
      Real.exp (-(δ^2*q^2/(8*b)*Fintype.card V)) := by
  obtain ⟨u,v,s⟩ := j
  by_cases huv : H.G.Adj u v
  · obtain ⟨hc0,hcB,hc1,-,-⟩ := normalized_completion_bounds hb hε hμ hload huv
    have ht := unit_weight_tails hq hq1 (show 0 < 2*b by positivity)
      hδ hδ1 hn (normalizedCompletion H F μ u v) hc0 hcB hc1
    have heq : 4*(2*b) = 8*b := by ring
    rw [heq] at ht
    cases s
    · exact (bprob_mono hq.le hq1 (E := rawProfileBad H F μ q δ (u,v,false))
        (E' := fun W => q+δ*q < wsum (normalizedCompletion H F μ u v) W)
        (iE' := fun _ => inferInstance) (fun W hw => hw.2)).trans ht.2
    · exact (bprob_mono hq.le hq1 (E := rawProfileBad H F μ q δ (u,v,true))
        (E' := fun W => wsum (normalizedCompletion H F μ u v) W < q-δ*q)
        (iE' := fun _ => inferInstance) (fun W hw => hw.2)).trans ht.1
  · rw [bprob_false (fun W hw => by cases s <;> exact huv hw.1)]
    exact (Real.exp_pos _).le

theorem raw_profile_of_not_bad {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {b ε q δ : ℝ} (hb : 0 < b) (hε : ε ≤ 1/2)
    (hq : 0 < q) (hδ : 0 ≤ δ)
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (hload : ∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε)
    {W : Finset V} (hW : ∀ j, ¬ rawProfileBad H F μ q δ j W)
    {u v : V} (huv : H.G.Adj u v) :
    |sampW H.G H.lab F μ W u v/q-1| ≤ ε+2*δ := by
  obtain ⟨-, -, -, hSp, hS2⟩ := normalized_completion_bounds hb hε hμ hload huv
  have hlo := hW (u,v,true)
  have hhi := hW (u,v,false)
  simp only [rawProfileBad,not_and,not_lt] at hlo hhi
  have hnorm : |wsum (normalizedCompletion H F μ u v) W/q-1| ≤ δ := by
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le,le_div_iff₀ hq]; linarith [hlo huv]
    · rw [sub_le_iff_le_add,div_le_iff₀ hq]; linarith [hhi huv]
  have heq : wsum (normalizedCompletion H F μ u v) W =
      sampW H.G H.lab F μ W u v/bdry H F μ s(u,v) := by
    simp only [wsum,normalizedCompletion,sampW,sum_div]
  have hcenter : |sampW H.G H.lab F μ W u v/q-bdry H F μ s(u,v)| ≤ 2*δ := by
    have hscale := mul_le_mul_of_nonneg_right hnorm hSp.le
    have hident : (wsum (normalizedCompletion H F μ u v) W/q-1)*bdry H F μ s(u,v) =
        sampW H.G H.lab F μ W u v/q-bdry H F μ s(u,v) := by
      rw [heq]; field_simp
    rw [←abs_of_pos hSp,←abs_mul,hident] at hscale
    rw [abs_of_pos hSp] at hscale
    exact hscale.trans (by nlinarith)
  have he : s(u,v) ∈ edges H :=
    mem_filter.mpr ⟨mem_univ _,(SimpleGraph.mem_edgeSet H.G).2 huv⟩
  calc
    _ = |(sampW H.G H.lab F μ W u v/q-bdry H F μ s(u,v))+
        (bdry H F μ s(u,v)-1)| := by congr 1; ring
    _ ≤ |sampW H.G H.lab F μ W u v/q-bdry H F μ s(u,v)|+
        |bdry H F μ s(u,v)-1| := abs_add_le _ _
    _ ≤ ε+2*δ := by linarith [hload _ he]

end TypedTriangle.RawReference
