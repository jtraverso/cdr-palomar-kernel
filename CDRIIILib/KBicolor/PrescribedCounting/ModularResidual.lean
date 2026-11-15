/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.PackingAttachment
public import CDRIIILib.KBicolor.PrescribedCounting.ModularTypes

/-! # Repair the actual residual congruences while leaving the cross family fixed -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
variable {n k m : ℕ}

theorem modular_residual (lab : Fin n → Fin k) (o : Fin k)
    [Fact m.Prime] (hm : 8 < m) (P : Place lab (Coord o) m) (hτ : P.τ=tau3 o)
    (C : Finset (Finset (Fin n)))
    (hC : IsPacking (kHost lab) (bicF k) C)
    (hCdiv : ∀ i j, i ≠ j → 3 ∣ kTypeCount lab C i j)
    (hQ : ∀ σ, IsPacking (rHostK lab (C.biUnion triEdges)) (bicF k) (packG P σ))
    (E : Finset (Finset (Fin n)))
    (hE : IsDecomposition (residual (rHostK lab (C.biUnion triEdges)) (leaveG P)) (bicF k)
      (edges (residual (rHostK lab (C.biUnion triEdges)) (leaveG P))) E)
    (t : Fin k → Fin k → ℕ)
    (hpair : ∀ i j, i ≠ j → 2*(t i j+t j i)=ksz lab i*ksz lab j)
    (hrow : ∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), t i j=ksz lab i*(ksz lab i-1)) :
    ∃ R, IsDecomposition (rHostK lab (C.biUnion triEdges)) (bicF k)
      (edges (rHostK lab (C.biUnion triEdges))) R ∧
      ∀ i j, i ≠ j → (3 : ℤ) ∣ ((t i j : ℤ)-kTypeCount lab R i j) := by
  let H := rHostK lab (C.biUnion triEdges)
  have hB : leaveG P ⊆ edges H := by
    intro e he
    have hp : e ∈ (packG P (fun _ => false)).biUnion triEdges := by
      rw [packG_leave]; exact he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp hp
    exact triEdges_subset_edges ((hQ _).1 T hT) heT
  have hQdec : ∀ σ, IsDecomposition H (bicF k) (leaveG P) (packG P σ) := by
    intro σ
    exact ⟨(hQ σ).1,(hQ σ).2,by
      have hh := packG_leave P σ
      ext e
      simpa only [mem_biUnion] using Finset.ext_iff.mp hh e⟩
  have hR : ∀ σ, IsDecomposition H (bicF k) (edges H) (E ∪ packG P σ) ∧
      Disjoint E (packG P σ) := by
    intro σ
    obtain ⟨ha,hb⟩ := attach_to_host H (bicF k) (leaveG P) (packG P σ) E hB (hQdec σ) hE
    refine ⟨?_,hb⟩
    convert ha using 1
    ext T
    simp only [mem_union]
  have hRC : ∀ σ, Disjoint (E ∪ packG P σ) C := by
    intro σ
    apply disjoint_left.mpr
    intro T hTR hTC
    obtain ⟨e,he⟩ := card_pos.mp (by rw [card_triEdges_three (hC.1 T hTC).1]; norm_num)
    exact disjoint_left.mp (disj_of_rHostK lab ((hR σ).1.1 T hTR)) he
      (mem_biUnion.mpr ⟨T,hTC,he⟩)
  have hfull : ∀ σ, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab))
      ((E ∪ packG P σ) ∪ C) := fun σ => union_decomp lab hC.1 hC.2 (hR σ).1
  obtain ⟨σ,hσ⟩ := choose_modular_trade_halves lab o hm P hτ E C t hfull
    (fun σ => (hR σ).2) hRC hpair hrow hCdiv
  exact ⟨E ∪ packG P σ,(hR σ).1,hσ⟩

end CDRBicolour.KBicolor.PrescribedCounting
