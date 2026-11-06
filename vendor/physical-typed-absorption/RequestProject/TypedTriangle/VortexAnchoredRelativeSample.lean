/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexJointRelativeSample
public import RequestProject.TypedTriangle.VortexHingeRelativeTail
public import RequestProject.TypedTriangle.ChildNormalizedGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! All parent-root pool and hinge tests can be placed in one relative sample.
The tail estimates remain explicit premises to keep the union bound separate
from their numerical exponents. Those estimates are supplied by
`pool_tail_relative` and `hinge_tail_linear`. -/

open Finset Classical S07V24 TypedTriangle.SparseEdge
noncomputable section

namespace TypedTriangle.RawReference

theorem anchored_relative_sample_of_tail_bounds
    {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I))
    (α q η θ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (hθ : θ ≤ η ^ 2 * q ^ 2 / 4)
    (hbudget :
      (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) + 2 : ℝ) *
        Real.exp (-(θ * Fintype.card V)) < 1)
    (hpoolTail : ∀ u v x : V,
      u ≠ v → ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F →
      bprob q univ (fun W =>
        (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
          (1 - η) * α * q * Fintype.card V) ≤
        Real.exp (-(θ * Fintype.card V)))
    (hhingeTail : ∀ u v a b : V,
      HingeTest H.G H.lab F u v a b →
      bprob q univ (fun W =>
        (((SparseEdge.hinges H.G H.lab F u v a b
          (hOrd hH4 u v a b)).filter
            (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
          (1 - η) * α * q ^ (hOrd hH4 u v a b - 4) *
            (Fintype.card V : ℝ) ^ (hOrd hH4 u v a b - 4)) ≤
        Real.exp (-(θ * Fintype.card V))) :
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
  let E : ((V × V × V) ⊕ (V × V × V × V)) → Finset V → Prop := fun j W =>
    match j with
    | Sum.inl (u,v,x) =>
        if u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F then
          (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
            (1 - η) * α * q * Fintype.card V
        else False
    | Sum.inr (u,v,a,b) =>
        if HingeTest H.G H.lab F u v a b then
          (((SparseEdge.hinges H.G H.lab F u v a b
            (hOrd hH4 u v a b)).filter
              (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
            (1 - η) * α * q ^ (hOrd hH4 u v a b - 4) *
              (Fintype.card V : ℝ) ^ (hOrd hH4 u v a b - 4)
        else False
  have hE : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θ * Fintype.card V)) := by
    intro j
    rcases j with ⟨⟨u,v,x⟩⟩ | ⟨⟨u,v,a,b⟩⟩
    · by_cases huv : u ≠ v
      · by_cases hk : ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F
        · have ht : u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F := ⟨huv,hk⟩
          simpa only [E, if_pos ht] using hpoolTail u v x huv hk
        · have ht : ¬(u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F) :=
            fun h => hk h.2
          simpa only [E, if_neg ht, bprob, ite_false, bexp_const] using
            (Real.exp_pos (-(θ * Fintype.card V))).le
      · have ht : ¬(u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F) :=
          fun h => huv h.1
        simpa only [E, if_neg ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
    · by_cases ht : HingeTest H.G H.lab F u v a b
      · simpa only [E, if_pos ht] using hhingeTail u v a b ht
      · simpa only [E, if_neg ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
  obtain ⟨W,hWlo,hWhi,hgood⟩ :=
    joint_sample_relative_size q η θ E hq hq1 hη hη1 hn hθ hE hbudget
  refine ⟨W,hWlo,hWhi,?_,?_⟩
  · intro u v huv k hk
    have hcount := hH3 u v huv k hk
    have hcountpos : 0 < (commonNbrs H k u v).card := by
      have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
      have : 0 < α * (Fintype.card V : ℝ) := mul_pos hα hnR
      exact_mod_cast (show (0 : ℝ) < (commonNbrs H k u v).card by linarith)
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hcountpos
    have hxlab : H.lab x = k := (Finset.mem_filter.mp hx).2.2.2
    have hgood' := hgood (Sum.inl (u,v,x))
    have ht : u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F := by
      simpa only [hxlab] using (show u ≠ v ∧
        ({H.lab u,H.lab v,k} : Multiset I) ∈ F from ⟨huv,hk⟩)
    have hlow : ¬ (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
        (1 - η) * α * q * Fintype.card V := by
      simpa only [E, if_pos ht] using hgood'
    simpa only [hxlab, not_lt] using hlow
  · intro u v a b ht
    have hgood' := hgood (Sum.inr (u,v,a,b))
    simpa only [E, if_pos ht, not_lt] using hgood'

#print axioms anchored_relative_sample_of_tail_bounds

end TypedTriangle.RawReference


