/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.LatinReplacement

/-! # Replace a reserved Latin packing inside a completed system

The complement of the initial packing is fixed. Every Latin replacement
remains a decomposition and preserves every off-diagonal type count.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

theorem replace_latin_decomposition (l₀ l : Fin m → Fin m → Fin m)
    (hl₀ : _root_.STS.IsLatin l₀) (hl : _root_.STS.IsLatin l)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D)
    (hsub : latPackK r c s l₀ ⊆ D) :
    IsDecomposition (kHost lab) (bicF k) (edges (kHost lab))
      ((D \ latPackK r c s l₀) ∪ latPackK r c s l) ∧
    Disjoint (D \ latPackK r c s l₀) (latPackK r c s l) ∧
    ∀ A B, A ≠ B →
      kTypeCount lab ((D \ latPackK r c s l₀) ∪ latPackK r c s l) A B =
        kTypeCount lab D A B := by
  let Q₀ := latPackK r c s l₀
  let Q := latPackK r c s l
  let R := D \ Q₀
  let E := edges (kHost lab)
  let L := Q₀.biUnion triEdges
  have heq : Q.biUnion triEdges = L := (latPackK_edges_eq h l₀ l hl₀ hl).symm
  have hR : IsDecomposition (kHost lab) (bicF k) (E \ L) R := by
    convert hD.sdiff_sub hsub using 1 <;> ext z <;>
      simp only [E, L, R, Q₀, mem_sdiff, mem_biUnion]
  have hQ : IsDecomposition (kHost lab) (bicF k) L Q :=
    ⟨latPackK_allowed h l, latPackK_disj h hl, by
      ext e
      simpa only [mem_biUnion] using Finset.ext_iff.mp heq e⟩
  have hLE : L ⊆ E := by
    intro e he
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
    exact hD.subset (hsub hT) heT
  have hed : Disjoint (E \ L) L :=
    disjoint_left.mpr (fun _ he hL => (mem_sdiff.mp he).2 hL)
  have hnew : IsDecomposition (kHost lab) (bicF k) E (R ∪ Q) := by
    convert hR.union hQ hed using 1
    · ext e
      simp only [mem_union, mem_sdiff]
      have hh : e ∈ L → e ∈ E := fun he => hLE he
      tauto
    · ext T
      simp only [mem_union]
  have hRQ : Disjoint R Q := by
    apply disjoint_left.mpr
    intro T hTR hTQ
    obtain ⟨e, he⟩ := card_pos.mp (by rw [card_triEdges_three (hQ.1 T hTQ).1]; norm_num)
    exact disjoint_left.mp hed (hR.subset hTR he) (hQ.subset hTQ he)
  have hcount : ∀ (P : Finset (Finset (Fin n))) (hRP : Disjoint R P) A B,
      kTypeCount lab (R ∪ P) A B = kTypeCount lab R A B + kTypeCount lab P A B := by
    intro P hRP A B
    unfold kTypeCount
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hRP)]
  refine ⟨hnew, hRQ, fun A B hAB => ?_⟩
  have hRQ₀ : Disjoint R Q₀ :=
    disjoint_left.mpr (fun _ he hQ => (mem_sdiff.mp he).2 hQ)
  have hcover : R ∪ Q₀ = D := sdiff_union_of_subset hsub
  rw [hcount Q hRQ, ← typeCount_latPackK_eq h l₀ l A B hAB]
  rw [← hcount Q₀ hRQ₀, hcover]

end CDRBicolour.KBicolor
