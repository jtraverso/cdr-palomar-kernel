/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexBernoulliRestriction
public import RequestProject.TypedTriangle.VortexAvailablePathTail
public import RequestProject.TypedTriangle.UniformSampleTail
public import RequestProject.TypedTriangle.VertexZeroExtension
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open RawReference

/-- An event using only available auxiliary vertices has its original
Bernoulli law when sampled on the actual surviving subtype. -/
theorem bprob_survivor_available_event {V : Type*} [Fintype V]
    (A : Finset V) (q : ℝ) (E : Finset V → Prop)
    (hIgnore : ∀ W, E (W ∩ (univ \ A)) ↔ E W) :
    letI : DecidableEq (Survivors A) := Classical.decEq _
    bprob q univ (fun W : Finset (Survivors A) => E (liftVertexSet A W)) = bprob q univ E := by
  letI : DecidableEq (Survivors A) := Classical.decEq _
  have hGround : (univ : Finset (Survivors A)).map (survivingVertexEmbedding A) = univ \ A := by
    ext v
    simp only [mem_map,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨w,rfl⟩
      exact w.2
    · intro hv
      exact ⟨⟨v,hv⟩,rfl⟩
  have hMap := bprob_map q (univ : Finset (Survivors A)) (survivingVertexEmbedding A) E
  rw [hGround] at hMap
  have hInter := bprob_inter q (univ : Finset V) (univ \ A) E
  rw [univ_inter] at hInter
  have hErase : (bprob q univ (fun W => E (W ∩ (univ \ A)))) = bprob q univ E := by
    unfold bprob
    apply bexp_congr
    intro W _
    by_cases hE : E W
    · simp only [hIgnore W,hE,ite_true]
    · simp only [hIgnore W,hE,ite_false]
  exact hMap.symm.trans (hInter.symm.trans hErase)

theorem available_path_tail_on_survivors {V : Type*} [Fintype V]
    (A : Finset V) {a q : ℝ} {m : ℕ} (ha : 0 < a) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : 0 < m) (hn : 0 < Fintype.card V) (L : SimpleGraph V) [DecidableRel L.Adj]
    (x y : V) (I : Finset (L.Walk x y)) (hLength : ∀ p ∈ I, p.length = m+1)
    (hCount : a * (Fintype.card V : ℝ)^m ≤ I.card)
    (hAvoid : ∀ p ∈ I, intlSet m p ⊆ univ \ A) :
    letI : DecidableEq (Survivors A) := Classical.decEq _
    bprob q univ (fun W : Finset (Survivors A) =>
      ((I.filter (fun p => intlSet m p ⊆ liftVertexSet A W)).card : ℝ) <
        a * (Fintype.card V : ℝ)^m * q^m / 2) ≤
      Real.exp (-(a * q^(2*m) / (16 * m^2) * Fintype.card (Survivors A))) := by
  letI : DecidableEq (Survivors A) := Classical.decEq _
  let E : Finset V → Prop := fun W => ((I.filter (fun p => intlSet m p ⊆ W)).card : ℝ) <
    a * (Fintype.card V : ℝ)^m * q^m / 2
  have hIgnore (W : Finset V) : E (W ∩ (univ \ A)) ↔ E W := by
    have hs : I.filter (fun p => intlSet m p ⊆ W ∩ (univ \ A)) =
        I.filter (fun p => intlSet m p ⊆ W) := by
      apply filter_congr
      intro p hp
      simp only [subset_inter_iff,hAvoid p hp,and_true]
    dsimp only [E]
    rw [hs]
  have hLaw := bprob_survivor_available_event A q E hIgnore
  have hTail := fam_paths_for_available_family ha hq hq1 hm hn L x y I hLength hCount
  have hSize : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun v : Survivors A => v.1) (fun _ _ h => Subtype.ext h)
  have hRate : 0 ≤ a * q^(2*m) / (16 * (m : ℝ)^2) := by positivity
  have hExp := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hSize hRate))
  exact (hLaw.le.trans hTail).trans hExp

theorem available_pool_tail_on_survivors {V : Type*} [Fintype V]
    (A P : Finset V) (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hn : 0 < Fintype.card V) (hCount : κ * Fintype.card V ≤ P.card) (hAvoid : P ⊆ univ \ A) :
    letI : DecidableEq (Survivors A) := Classical.decEq _
    bprob q univ (fun W : Finset (Survivors A) => ((P ∩ liftVertexSet A W).card : ℝ) <
      κ * Fintype.card V * q / 2) ≤ Real.exp (-(κ^2 * q^2 / 16 * Fintype.card (Survivors A))) := by
  letI : DecidableEq (Survivors A) := Classical.decEq _
  let E : Finset V → Prop := fun W => ((P ∩ W).card : ℝ) < κ * Fintype.card V * q / 2
  have hIgnore (W : Finset V) : E (W ∩ (univ \ A)) ↔ E W := by
    have hs : P ∩ (W ∩ (univ \ A)) = P ∩ W := by
      ext v
      simp only [mem_inter]
      constructor
      · rintro ⟨hvP,hvW,hvS⟩
        exact ⟨hvP,hvW⟩
      · rintro ⟨hvP,hvW⟩
        exact ⟨hvP,hvW,hAvoid hvP⟩
    dsimp only [E]
    rw [hs]
  have hLaw := bprob_survivor_available_event A q E hIgnore
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hPpos : (0 : ℝ) < P.card := (mul_pos hκ hnR).trans_le hCount
  have hPsize : (P.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_card (subset_univ P)
  have hFrac : κ^2 * q^2 / 16 * Fintype.card V ≤
      (1 / 2 : ℝ)^2 * (κ * Fintype.card V)^2 * q^2 / (4 * P.card) := by
    have hd : (1 / 2 : ℝ)^2 * (κ * Fintype.card V)^2 * q^2 / (4 * Fintype.card V) ≤
        (1 / 2 : ℝ)^2 * (κ * Fintype.card V)^2 * q^2 / (4 * P.card) := by gcongr
    have heq : (1 / 2 : ℝ)^2 * (κ * Fintype.card V)^2 * q^2 / (4 * Fintype.card V) =
        κ^2 * q^2 / 16 * Fintype.card V := by field_simp; ring
    rwa [heq] at hd
  have hTail := pool_tail_relative q (1 / 2) κ P hq hq1 (by norm_num) (by norm_num) hκ hn hCount
  have hThreshold : (1 - (1 / 2 : ℝ)) * (κ * Fintype.card V) * q = κ * Fintype.card V * q / 2 := by ring
  rw [hThreshold] at hTail
  have hSize : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun v : Survivors A => v.1) (fun _ _ h => Subtype.ext h)
  have hRate : 0 ≤ κ^2 * q^2 / 16 := by positivity
  exact ((hLaw.le.trans hTail).trans (Real.exp_le_exp.mpr (neg_le_neg hFrac))).trans
    (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hSize hRate)))

#print axioms bprob_survivor_available_event
#print axioms available_path_tail_on_survivors
#print axioms available_pool_tail_on_survivors
end TypedTriangle.Vortex
