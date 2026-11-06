/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexAnchoredRelativeSample
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Convert the adjustable Bernstein tails for one pool and one hinge test to
the common rate used in the simultaneous parent-root sampler. -/

open Finset Classical S07V24 TypedTriangle.SparseEdge
noncomputable section

namespace TypedTriangle.RawReference

theorem pool_tail_at_rate {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I))
    (α q η θ : ℝ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V)
    (hH3 : CommonNbrCond H F α)
    (hθ : θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4)
    (u v x : V) (huv : u ≠ v)
    (hk : ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F) :
    bprob q univ (fun W =>
      (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
        (1 - η) * α * q * Fintype.card V) ≤
      Real.exp (-(θ * Fintype.card V)) := by
  let P := commonNbrs H (H.lab x) u v
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hP := hH3 u v huv (H.lab x) hk
  have hPpos : (0 : ℝ) < P.card := by
    dsimp [P] at *
    nlinarith [mul_pos hα hN]
  have hPcard : (P.card : ℝ) ≤ N := by
    dsimp [P,N]
    exact_mod_cast card_le_card (subset_univ P)
  have hfrac : θ * N ≤ η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * P.card) := by
    have hden : η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * N) ≤
        η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * P.card) := by gcongr
    have heq : η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * N) =
        η ^ 2 * α ^ 2 * q ^ 2 / 4 * N := by
      field_simp
    calc
      θ * N ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4 * N :=
        mul_le_mul_of_nonneg_right hθ hN.le
      _ = η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * N) := heq.symm
      _ ≤ _ := hden
  have htail := pool_tail_relative q η α P hq hq1 hη hη1 hα hn hP
  calc
    bprob q univ (fun W =>
        (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
          (1 - η) * α * q * Fintype.card V) ≤
      Real.exp (-(η ^ 2 * (α * N) ^ 2 * q ^ 2 / (4 * P.card))) := by
        convert htail using 1
        congr 1
        funext W
        apply propext
        dsimp only [P]
        have heq : (1 - η) * α * q * (Fintype.card V : ℝ) =
            (1 - η) * (α * (Fintype.card V : ℝ)) * q := by ring
        rw [heq]
    _ ≤ Real.exp (-(θ * N)) := Real.exp_le_exp.mpr (neg_le_neg hfrac)

theorem hinge_tail_at_rate {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I))
    (α q η θ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V)
    (hH4 : HingeCond H F α h)
    (hθ : ∀ i, 6 ≤ i → i ≤ h →
      θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))
    (u v a b : V) (ht : HingeTest H.G H.lab F u v a b) :
    bprob q univ (fun W =>
      (((SparseEdge.hinges H.G H.lab F u v a b
        (hOrd hH4 u v a b)).filter
          (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
        (1 - η) * α * q ^ (hOrd hH4 u v a b - 4) *
          (Fintype.card V : ℝ) ^ (hOrd hH4 u v a b - 4)) ≤
      Real.exp (-(θ * Fintype.card V)) := by
  let i := hOrd hH4 u v a b
  let N : ℝ := Fintype.card V
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hi := hOrd_spec hH4 ht
  have hroots := roots_distinct ht
  have htail := hinge_tail_linear hroots hi.1 hα hq hq1 hη hη1 hn hi.2.2
  have hfrac : θ * N ≤
      η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) * N /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by
    have hrate := mul_le_mul_of_nonneg_right (hθ i hi.1 hi.2.1) hN
    convert hrate using 1 <;> ring
  calc
    bprob q univ (fun W =>
        (((SparseEdge.hinges H.G H.lab F u v a b i).filter
          (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
          (1 - η) * α * q ^ (i - 4) * N ^ (i - 4)) ≤
      Real.exp (-(η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) * N /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))) := by
          convert htail using 1
          congr 1
          funext W
          apply propext
          congr 1
          dsimp [ccount, i, N]
          ring
    _ ≤ Real.exp (-(θ * N)) := Real.exp_le_exp.mpr (neg_le_neg hfrac)

/-- A single Bernoulli sample retains all parent-root pools and hinges with
adjustable relative error. The numerical rate inequalities can be met by
choosing `θ` below finitely many positive expressions (one per order 6..h). -/
theorem anchored_relative_sample_at_rate
    {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I))
    (α q η θ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (hθsize : θ ≤ η ^ 2 * q ^ 2 / 4)
    (hθpool : θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4)
    (hθhinge : ∀ i, 6 ≤ i → i ≤ h →
      θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))
    (hbudget :
      (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) + 2 : ℝ) *
        Real.exp (-(θ * Fintype.card V)) < 1) :
    ∃ W : Finset V,
      (1 - η) * q * Fintype.card V ≤ W.card ∧
      (W.card : ℝ) < (1 + η) * q * Fintype.card V ∧
      (∀ u v, u ≠ v → ∀ k,
        ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
        (1 - η) * α * q * Fintype.card V ≤
          ((commonNbrs H k u v) ∩ W).card) ∧
      (∀ u v a b, HingeTest H.G H.lab F u v a b →
        (1 - η) * α * q ^ (hOrd hH4 u v a b - 4) *
          (Fintype.card V : ℝ) ^ (hOrd hH4 u v a b - 4) ≤
            ((SparseEdge.hinges H.G H.lab F u v a b
              (hOrd hH4 u v a b)).filter
                (fun J => freeV u v a b J ⊆ W)).card) := by
  exact anchored_relative_sample_of_tail_bounds H F α q η θ h
    hα hq hq1 hη hη1 hn hH3 hH4 hθsize hbudget
    (fun u v x huv hk => pool_tail_at_rate H F α q η θ
      hα hq hq1 hη hη1 hn hH3 hθpool u v x huv hk)
    (fun u v a b ht => hinge_tail_at_rate H F α q η θ h
      hα hq hq1 hη hη1 hn hH4 hθhinge u v a b ht)

private theorem finite_positive_rate {S : Finset ℕ} {r : ℕ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i ∈ S, c ≤ r i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i S hi ih =>
    have hrS : ∀ j ∈ S, 0 < r j := by
      intro j hj
      exact hr j (mem_insert_of_mem hj)
    obtain ⟨c,hc,hbound⟩ := ih hrS
    refine ⟨min c (r i), lt_min hc (hr i (mem_insert_self i S)), ?_⟩
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

/-- The individual size, pool and hinge rates admit a common positive
coefficient independent of the sample tolerance `η` and host order. -/
theorem exists_common_relative_rate (α q : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧
      c ≤ q ^ 2 / 4 ∧ c ≤ α ^ 2 * q ^ 2 / 4 ∧
      ∀ i, 6 ≤ i → i ≤ h →
        c ≤ α ^ 2 * q ^ (2 * (i - 4)) /
          (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by
  let r : ℕ → ℝ := fun i =>
    α ^ 2 * q ^ (2 * (i - 4)) /
      (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ))
  have hr : ∀ i ∈ Icc 6 h, 0 < r i := by
    intro i hi
    have hi6 : 6 ≤ i := (mem_Icc.mp hi).1
    have hd : 0 < i - 4 := by omega
    dsimp [r]
    have hdr : (0 : ℝ) < ((i - 4 : ℕ) : ℝ) := by exact_mod_cast hd
    positivity
  obtain ⟨c,hc,hbound⟩ := finite_positive_rate hr
  refine ⟨min (q ^ 2 / 4) (min (α ^ 2 * q ^ 2 / 4) c), ?_, ?_, ?_, ?_⟩
  · apply lt_min
    · positivity
    · exact lt_min (by positivity) hc
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · intro i hi6 hih
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (hbound i (mem_Icc.mpr ⟨hi6,hih⟩)))

#print axioms pool_tail_at_rate
#print axioms hinge_tail_at_rate
#print axioms anchored_relative_sample_at_rate
#print axioms exists_common_relative_rate

end TypedTriangle.RawReference
