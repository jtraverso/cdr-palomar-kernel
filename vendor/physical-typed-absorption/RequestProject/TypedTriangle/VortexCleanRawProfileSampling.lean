/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHingeSampling
public import RequestProject.TypedTriangle.RawProfileSampling
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex
open RawReference CorePaid

theorem anchored_clean_raw_profile_tests_at_rate
    {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α q η θ b ε : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (hb : 0 < b) (hε : ε ≤ 1/2) (μ : Finset V → ℝ)
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (hLoad : ∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε)
    (h3 : CommonNbrCond H F α) (hClean : CleanHingeCond H F α h)
    (hθsize : θ ≤ η ^ 2 * q ^ 2 / 4)
    (hθpool : θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4)
    (hθhinge : ∀ i, 6 ≤ i → i ≤ h →
      θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))
    (hθraw : θ ≤ η ^ 2 * q ^ 2 / (8*b))
    {J : Type*} [Fintype J] (Eextra : J → Finset V → Prop)
    (hExtra : ∀ j, bprob q univ (Eextra j) ≤ Real.exp (-(θ * Fintype.card V)))
    (hbudget : (Fintype.card ((((V × V × V) ⊕ (V × V × V × V)) ⊕ (V × V × Bool)) ⊕ J) + 2 : ℝ) *
      Real.exp (-(θ * Fintype.card V)) < 1) :
    ∃ W : Finset V,
      (1 - η) * q * Fintype.card V ≤ W.card ∧
      (W.card : ℝ) < (1 + η) * q * Fintype.card V ∧
      (∀ u v, u ≠ v → ∀ k, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
        (1 - η) * α * q * Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) ∧
      (∀ u v a b, HingeTest H.G H.lab F u v a b →
        (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
          (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
            (((SparseEdge.hinges H.G H.lab F u v a b
              (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
                (fun J => freeV u v a b J ⊆ W)).card) ∧
      (∀ u v, H.G.Adj u v →
        |S07V48.sampW H.G H.lab F μ W u v/q-1| ≤ ε+2*η) ∧
      ∀ j, ¬ Eextra j W := by
  let E : ((((V × V × V) ⊕ (V × V × V × V)) ⊕ (V × V × Bool)) ⊕ J) → Finset V → Prop := fun j W =>
    match j with
    | Sum.inl (Sum.inl (Sum.inl (u, v, x))) =>
        if u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F then
          (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
            (1 - η) * α * q * Fintype.card V else False
    | Sum.inl (Sum.inl (Sum.inr (u, v, a, b))) =>
        if HingeTest H.G H.lab F u v a b then
          ((((SparseEdge.hinges H.G H.lab F u v a b
            (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
              (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
            (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
              (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) else False
    | Sum.inl (Sum.inr j) => RawReference.rawProfileBad H F μ q η j W
    | Sum.inr j => Eextra j W
  have hE : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θ * Fintype.card V)) := by
    intro j
    rcases j with ((⟨⟨u, v, x⟩⟩ | ⟨⟨u, v, a, b⟩⟩) | j) | j
    · by_cases ht : u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F
      · simpa only [E, ite_eq_left ht] using
          pool_tail_at_rate H F α q η θ hα hq hq1 hη hη1 hn h3 hθpool u v x ht.1 ht.2
      · simpa only [E, ite_eq_right ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
    · by_cases ht : HingeTest H.G H.lab F u v a b
      · simpa only [E, ite_eq_left ht] using
          clean_hinge_tail_at_rate H F α q η θ h hα hq hq1 hη hη1 hn hClean
            hθhinge u v a b ht
      · simpa only [E, ite_eq_right ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
    · have ht := RawReference.raw_profile_bad_prob hb hε hq hq1 hη hη1 hn hμ hLoad j
      have hRate : θ * Fintype.card V ≤
          η^2*q^2/(8*b)*Fintype.card V :=
        mul_le_mul_of_nonneg_right hθraw (by positivity)
      exact ht.trans (Real.exp_le_exp.mpr (neg_le_neg hRate))
    · exact hExtra j
  obtain ⟨W, hWlo, hWhi, hgood⟩ :=
    joint_sample_relative_size q η θ E hq hq1 hη hη1 hn hθsize hE hbudget
  refine ⟨W, hWlo, hWhi, ?_, ?_, ?_, ?_⟩
  · intro u v huv k hk
    have hcount := h3 u v huv k hk
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have hcountpos : 0 < (commonNbrs H k u v).card := by
      exact_mod_cast (show (0 : ℝ) < (commonNbrs H k u v).card by
        nlinarith [mul_pos hα hnR])
    obtain ⟨x, hx⟩ := card_pos.mp hcountpos
    have hxlab : H.lab x = k := (mem_filter.mp hx).2.2.2
    have ht : u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F := by
      simpa only [hxlab] using (show u ≠ v ∧
        ({H.lab u, H.lab v, k} : Multiset I) ∈ F from ⟨huv, hk⟩)
    have hgood' := hgood (Sum.inl (Sum.inl (Sum.inl (u, v, x))))
    simpa only [E, ite_eq_left ht, hxlab, not_lt] using hgood'
  · intro u v a b ht
    have hgood' := hgood (Sum.inl (Sum.inl (Sum.inr (u, v, a, b))))
    simpa only [E, ite_eq_left ht, not_lt] using hgood'

  · intro u v huv
    apply RawReference.raw_profile_of_not_bad hb hε hq hη.le hμ hLoad ?_ huv
    intro j
    simpa only [E] using hgood (Sum.inl (Sum.inr j))
  · intro j
    exact hgood (Sum.inr j)

#print axioms anchored_clean_raw_profile_tests_at_rate
end TypedTriangle.Vortex
