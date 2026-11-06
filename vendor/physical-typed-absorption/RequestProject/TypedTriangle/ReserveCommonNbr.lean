/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ProtectedWeightedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle
variable {V I : Type*} [Fintype V]

lemma blocked_neighbors_card_le (R : Finset (Sym2 V)) (v : V) :
    (univ.filter fun w => s(v,w) ∈ R).card ≤ degIn R v := by
  apply card_le_card_of_injOn (fun w => s(v,w))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2,by simp⟩
  · intro w _ w' _ he
    rcases Sym2.eq_iff.mp he with ⟨_,hh⟩ | ⟨h₁,h₂⟩
    · exact hh
    · exact h₂.trans h₁

/-- Sparse protected edges preserve H3 for the residual host. The loss is paid
per endpoint, so it is at most twice the maximum protected degree. -/
theorem residual_commonNbrCond {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) (R : Finset (Sym2 V)) (d : ℕ)
    (hdeg : ∀ v, degIn R v ≤ d) (hd : (d:ℝ) ≤ α/4*Fintype.card V) :
    CommonNbrCond (residual H R) F (α/2) := by
  intro u v huv k hlabels
  have hFull := h3 u v huv k hlabels
  let Bu := univ.filter fun w => s(u,w) ∈ R
  let Bv := univ.filter fun w => s(v,w) ∈ R
  have hBu : Bu.card ≤ d := (blocked_neighbors_card_le R u).trans (hdeg u)
  have hBv : Bv.card ≤ d := (blocked_neighbors_card_le R v).trans (hdeg v)
  have hcover : commonNbrs H k u v ⊆ commonNbrs (residual H R) k u v ∪ Bu ∪ Bv := by
    intro w hw
    obtain ⟨huw,hvw,hl⟩ := (mem_filter.mp hw).2
    by_cases hwu : s(u,w) ∈ R
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hwu⟩))
    by_cases hwv : s(v,w) ∈ R
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hwv⟩)
    apply mem_union_left
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_,hl⟩
    · simp only [residual,subHost,SimpleGraph.inf_adj,SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨mem_sdiff.mpr ⟨?_,hwu⟩,huw.ne⟩,huw⟩
      simpa [edges] using huw
    · simp only [residual,subHost,SimpleGraph.inf_adj,SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨mem_sdiff.mpr ⟨?_,hwv⟩,hvw.ne⟩,hvw⟩
      simpa [edges] using hvw
  have hcard : (commonNbrs H k u v).card ≤ (commonNbrs (residual H R) k u v).card+2*d := by
    have hh : (commonNbrs H k u v).card ≤ (commonNbrs (residual H R) k u v).card+Bu.card+Bv.card :=
      (card_le_card hcover).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    omega
  have hr : ((commonNbrs H k u v).card:ℝ) ≤ (commonNbrs (residual H R) k u v).card+2*d := by exact_mod_cast hcard
  linarith
end TypedTriangle
