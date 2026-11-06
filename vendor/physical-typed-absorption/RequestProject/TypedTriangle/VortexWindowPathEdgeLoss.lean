/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexWindowPathTrim
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
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

/-- Count bad edges on the induced vertex set consisting of the window and
the two fixed roots. Its order is at most |W|+2, rather than the host order. -/
theorem card_edge_window_le {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (x y : V) (A : Finset (G.Walk x y))
    (W : Finset V) (hLength : ∀ p ∈ A, p.length = m+1)
    (hInternal : ∀ p ∈ A, intlSet m p ⊆ W)
    (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ) (hB : ∀ v, B.degree v ≤ d) :
    (A.filter fun p => ∃ k ∈ Finset.range (m+1),
      B.Adj (p.getVert k) (p.getVert (k+1))).card ≤
        (m+1)*d*(W.card+2)^(m-1) := by
  let C := insert x (insert y W)
  have hx : x ∈ C := by simp [C]
  have hy : y ∈ C := by simp [C]
  have hSupport : ∀ p ∈ A, ∀ z ∈ p.support, z ∈ C := by
    intro p hp z hz
    obtain ⟨k,hk,hkle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    rw [← hk]
    by_cases hk0 : k = 0
    · simp [hk0,C]
    by_cases hkLast : k = m+1
    · rw [hkLast,← hLength p hp,SimpleGraph.Walk.getVert_length]
      exact hy
    have hki : k-1 < m := by have := hLength p hp; omega
    have hIntl : p.getVert k ∈ intlSet m p :=
      (mem_intlSet m p _).mpr ⟨⟨k-1,hki⟩,by simp only [intl]; congr 1; omega⟩
    exact mem_insert_of_mem (mem_insert_of_mem (hInternal p hp hIntl))
  let Abad := A.filter fun p => ∃ k ∈ Finset.range (m+1),
    B.Adj (p.getVert k) (p.getVert (k+1))
  have memAbad (p : G.Walk x y) : p ∈ Abad ↔ p ∈ A ∧
      ∃ k ∈ Finset.range (m+1), B.Adj (p.getVert k) (p.getVert (k+1)) := by
    simp only [Abad,Finset.mem_filter]
  let Gc := G.induce (C : Set V)
  let Bc := B.induce (C : Set V)
  letI : DecidableRel Gc.Adj := Classical.decRel _
  letI : DecidableRel Bc.Adj := Classical.decRel _
  let xc : {v // v ∈ C} := ⟨x,hx⟩
  let yc : {v // v ∈ C} := ⟨y,hy⟩
  let f : {p // p ∈ Abad} → Gc.Walk xc yc := fun p =>
    p.val.induce (C : Set V) (hSupport p.val ((memAbad p.val).mp p.property).1)
  have hfMap : ∀ p, (f p).map (SimpleGraph.Embedding.induce (C : Set V)).toHom = p.val := by
    intro p
    exact SimpleGraph.Walk.map_induce p.val _
  have hfGet : ∀ p k, ((f p).getVert k).val = p.val.getVert k := by
    intro p k
    have he := congrArg (fun w => w.getVert k) (hfMap p)
    simpa only [SimpleGraph.Walk.getVert_map,SimpleGraph.Embedding.coe_toHom,SimpleGraph.Embedding.induce,SimpleGraph.Embedding.comap_apply,Function.Embedding.subtype_apply] using he
  have hfLength : ∀ p, (f p).length = m+1 := by
    intro p
    have he := congrArg (fun w => w.length) (hfMap p)
    simp only [SimpleGraph.Walk.length_map] at he
    exact he.trans (hLength p.val ((memAbad p.val).mp p.property).1)
  have hfInj : Function.Injective f := by
    intro p p' he
    apply Subtype.ext
    exact (hfMap p).symm.trans ((congrArg
      (fun w => w.map (SimpleGraph.Embedding.induce (C : Set V)).toHom) he).trans (hfMap p'))
  have hBcDegree : ∀ v, Bc.degree v ≤ d := by
    intro v
    apply le_trans (b := B.degree v.val) ?_ (hB v.val)
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    apply card_le_card_of_injOn Subtype.val
    · intro w hw
      have hadj : Bc.Adj v w := (Bc.mem_neighborFinset v w).mp hw
      exact (B.mem_neighborFinset v.val w.val).mpr hadj
    · exact Subtype.val_injective.injOn
  let A' := Abad.attach.image f
  have hA' : ∀ p ∈ A', p.length = m+1 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact hfLength q
  have hAllBad : ∀ p ∈ A', ∃ k ∈ Finset.range (m+1),
      Bc.Adj (p.getVert k) (p.getVert (k+1)) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨k,hk,hAdj⟩ := ((memAbad q.val).mp q.property).2
    refine ⟨k,hk,?_⟩
    change B.Adj ((f q).getVert k).val ((f q).getVert (k+1)).val
    simpa only [hfGet] using hAdj
  have hCount : A'.card ≤ (m+1)*d*Fintype.card {v // v ∈ C}^(m-1) := by
    apply (Finset.card_le_card ?_).trans (card_edgeB_le m xc yc A' hA' Bc d hBcDegree)
    intro p hp
    exact Finset.mem_filter.mpr ⟨hp,hAllBad p hp⟩
  have hCard : A'.card = Abad.card := by
    change (Abad.attach.image f).card = Abad.card
    rw [Finset.card_image_of_injective _ hfInj,Finset.card_attach]
  rw [hCard,Fintype.card_coe] at hCount
  have hCcard : C.card ≤ W.card+2 := by
    have hxCard := Finset.card_insert_le x (insert y W)
    have hyCard := Finset.card_insert_le y W
    dsimp [C]
    omega
  exact hCount.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hCcard (m-1)))

#print axioms card_edge_window_le

end TypedTriangle.Vortex
