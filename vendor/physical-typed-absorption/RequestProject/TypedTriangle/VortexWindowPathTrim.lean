/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.RandomCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

/-- All free coordinates lie in W. A prescribed internal vertex therefore
costs |W|^(m-1), including when the roots lie outside W. -/
theorem card_through_window_le {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (x y : V) (A : Finset (G.Walk x y))
    (W Z : Finset V) (hLength : ∀ p ∈ A, p.length = m+1)
    (hInternal : ∀ p ∈ A, intlSet m p ⊆ W) :
    (A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z).card ≤
      Z.card*m*W.card^(m-1) := by
  let Abad := A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z
  let ZW : Finset {v // v ∈ W} := W.attach.filter fun z => z.val ∈ Z
  let T : Finset (Fin m → {v // v ∈ W}) := ZW.biUnion fun z =>
    univ.biUnion fun i : Fin m => univ.filter fun s => s i = z
  let f : {p // p ∈ Abad} → (Fin m → {v // v ∈ W}) := fun p i =>
    ⟨intl m p.val i,hInternal p.val (mem_filter.mp p.property).1
      ((mem_intlSet m p.val _).mpr ⟨i,rfl⟩)⟩
  have hfT : ∀ p, f p ∈ T := by
    intro p
    obtain ⟨i,hi⟩ := (mem_filter.mp p.property).2
    simp only [T,mem_biUnion,mem_univ,true_and,mem_filter]
    refine ⟨f p i,?_,i,rfl⟩
    exact mem_filter.mpr ⟨Finset.mem_attach _ _,hi⟩
  have hfinj : Function.Injective f := by
    intro p p' heq
    apply Subtype.ext
    apply intl_injOn m x y (hLength p.val (mem_filter.mp p.property).1)
      (hLength p'.val (mem_filter.mp p'.property).1)
    funext i
    exact congrArg Subtype.val (congrFun heq i)
  have hA : Abad.card ≤ T.card := by
    have hc := Fintype.card_le_of_injective
      (fun p : {p // p ∈ Abad} => (⟨f p,hfT p⟩ : {s // s ∈ T}))
      (fun p p' he => hfinj (congrArg Subtype.val he))
    simpa only [Fintype.card_coe] using hc
  have hZW : ZW.card ≤ Z.card := by
    apply card_le_card_of_injOn Subtype.val
    · intro z hz
      exact (mem_filter.mp hz).2
    · exact Subtype.val_injective.injOn
  have hT : T.card ≤ ZW.card*m*W.card^(m-1) := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      ∑ z ∈ ZW, (univ.biUnion fun i : Fin m =>
          univ.filter fun s : Fin m → {v // v ∈ W} => s i = z).card
          ≤ ∑ _z ∈ ZW, m*W.card^(m-1) := by
        apply sum_le_sum
        intro z hz
        exact Finset.card_biUnion_le.trans (by simp [card_hit])
      _ = ZW.card*m*W.card^(m-1) := by rw [sum_const,smul_eq_mul]; ring
  exact hA.trans (hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hZW)))

/-- Retain the actual path count after a later vertex trim. -/
theorem paths_in_trim_count {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V) (W Z : Finset V) :
    (pathsIn G m x y W).card ≤ (pathsIn G m x y (W \ Z)).card +
      Z.card*m*W.card^(m-1) := by
  let A := pathsIn G m x y W
  let Abad := A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z
  have hCover : A ⊆ pathsIn G m x y (W \ Z) ∪ Abad := by
    intro p hp
    by_cases hz : ∃ i : Fin m, intl m p i ∈ Z
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hz⟩)
    · apply mem_union_left
      obtain ⟨hpPath,hpW⟩ := mem_filter.mp hp
      apply mem_filter.mpr ⟨hpPath,?_⟩
      intro z hzi
      obtain ⟨i,rfl⟩ := (mem_intlSet m p z).mp hzi
      exact mem_sdiff.mpr ⟨hpW hzi,fun hc => hz ⟨i,hc⟩⟩
  have hBad := card_through_window_le m x y A W Z
    (fun p hp => (SimpleGraph.mem_finsetWalkLength_iff.mp
      (mem_filter.mp (mem_filter.mp hp).1).1))
    (fun p hp => (mem_filter.mp hp).2)
  exact (card_le_card hCover).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left hBad _))

/-- The admissible relative vertex trim is independent of q. -/
theorem relative_window_path_loss {a q β n w z : ℝ} (m : ℕ)
    (hm : 0 < m) (ha : 0 ≤ a) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hn : 0 ≤ n) (hw : 0 ≤ w) (hz : z ≤ β*w)
    (hWindow : w ≤ 2*q*n) (hBudget : β*(m:ℝ)*2^m ≤ a/4) :
    z*(m:ℝ)*w^(m-1) ≤ a*q^m*n^m/4 := by
  have hzmul := mul_le_mul_of_nonneg_right hz
    (show 0 ≤ (m:ℝ)*w^(m-1) by positivity)
  have hpow : w^m ≤ (2*q*n)^m := pow_le_pow_left₀ hw hWindow m
  have hpowId : w^(m-1)*w = w^m := by
    rw [← pow_succ,Nat.sub_add_cancel hm]
  calc
    z*(m:ℝ)*w^(m-1) ≤ β*(m:ℝ)*w^m := by
      calc
        z*(m:ℝ)*w^(m-1) = z*((m:ℝ)*w^(m-1)) := by ring
        _ ≤ β*w*((m:ℝ)*w^(m-1)) := hzmul
        _ = β*(m:ℝ)*w^m := by rw [← hpowId]; ring
    _ ≤ β*(m:ℝ)*(2*q*n)^m := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (β*(m:ℝ)*2^m)*(q^m*n^m) := by rw [mul_pow,mul_pow]; ring
    _ ≤ (a/4)*(q^m*n^m) := mul_le_mul_of_nonneg_right hBudget (by positivity)
    _ = a*q^m*n^m/4 := by ring

#print axioms card_through_window_le
#print axioms paths_in_trim_count
#print axioms relative_window_path_loss

end TypedTriangle.Vortex
