/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.UniformSampleTail
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! One Bernoulli sample simultaneously passes an arbitrary finite family of
tests and a relative size window. The caller must provide the joint
probability budget; concentration for geometric tests is a separate gate. -/

open Finset Classical S07V24
noncomputable section

namespace TypedTriangle.RawReference

theorem joint_sample_relative_size {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (q η θ : ℝ) (E : ι → Finset V → Prop)
    [∀ j, DecidablePred (E j)]
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V)
    (hθ : θ ≤ η^2*q^2/4)
    (hE : ∀ j, bprob q univ (E j) ≤
      Real.exp (-(θ*Fintype.card V)))
    (hbudget : (Fintype.card ι + 2 : ℝ) *
      Real.exp (-(θ*Fintype.card V)) < 1) :
    ∃ W : Finset V,
      (1-η)*q*Fintype.card V ≤ W.card ∧
      (W.card : ℝ) < (1+η)*q*Fintype.card V ∧
      ∀ j, ¬ E j W := by
  let bad : ι ⊕ Bool → Finset V → Prop := fun j W => match j with
    | Sum.inl j => E j W
    | Sum.inr true => (W.card : ℝ) < (1-η)*q*Fintype.card V
    | Sum.inr false => (1+η)*q*Fintype.card V ≤ W.card
  have hOne : ∀ j, bprob q univ (bad j) ≤
      Real.exp (-(θ*Fintype.card V)) := by
    intro j
    rcases j with j | b
    · have hj := hE j
      unfold bprob at hj ⊢
      refine (bexp_congr (fun W _ => ?_)).le.trans hj
      by_cases he : E j W
      · dsimp only [bad]
        simp [he]
      · dsimp only [bad]
        simp [he]
    · cases b
      · have hu := size_upper_tail_relative (V := V) q η hq hq1 hη hη1 hn
        exact hu.trans (Real.exp_le_exp.mpr (by
          have hnR : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hθ hnR]))
      · have hl := pool_tail_relative (V := V) q η 1 (univ : Finset V)
          hq hq1 hη hη1 (by norm_num) hn (by simp)
        have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
        have hexp : -(η^2 * (1 * (Fintype.card V : ℝ))^2 * q^2 /
            (4 * ((univ : Finset V).card : ℝ))) =
            -(η^2*q^2/4 * Fintype.card V) := by
          rw [Finset.card_univ]
          field_simp
        rw [hexp] at hl
        have hmul := mul_le_mul_of_nonneg_right hθ hnR.le
        have hb := hl.trans (Real.exp_le_exp.mpr (neg_le_neg hmul))
        simpa only [bad, Finset.univ_inter, one_mul, Finset.card_univ,
          mul_assoc, mul_comm, mul_left_comm] using hb
  have hsum : ∑ j : ι ⊕ Bool, bprob q univ (bad j) < 1 := by
    calc
      _ ≤ ∑ _j : ι ⊕ Bool, Real.exp (-(θ*Fintype.card V)) :=
          Finset.sum_le_sum fun j _ => hOne j
      _ = (Fintype.card ι + 2 : ℝ) * Real.exp (-(θ*Fintype.card V)) := by
          simp [Fintype.card_sum, Fintype.card_bool, nsmul_eq_mul]
      _ < 1 := hbudget
  obtain ⟨W, -, hgood⟩ := exists_good hq.le hq1 univ univ bad hsum
  refine ⟨W, ?_, ?_, ?_⟩
  · have h := hgood (Sum.inr true) (mem_univ _)
    simpa only [bad, not_lt] using h
  · have h := hgood (Sum.inr false) (mem_univ _)
    simpa only [bad, not_le] using h
  · intro j
    exact hgood (Sum.inl j) (mem_univ _)

#print axioms joint_sample_relative_size

end TypedTriangle.RawReference
