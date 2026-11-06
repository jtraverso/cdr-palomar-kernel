/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativePaidChild
public import RequestProject.TypedTriangle.G34NativePackingWithReference
public import RequestProject.S07V42.CompressionAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The paid child stays outside the dense reference chosen before packing,
provided the original bank is retained in the reference-avoiding stock. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem paid_child_inside_reference_avoiding_stock {V : Type} [Fintype V]
    (W : Finset V) (E₀ : Finset (Sym2 {x // x ∈ W}))
    (U F0 B Y Yb Bc : Finset (Sym2 V))
    (hF0U : F0 ⊆ U) (hBU : B ⊆ U)
    (hAvoid : Disjoint (SampledResource.lift W E₀) U)
    (hYF : Y ⊆ F0) (hPaid : B = Bc ∪ Yb) :
    Y ∪ Yb ⊆ U ∧
      Disjoint (SampledResource.lift W E₀) (Y ∪ Yb) := by
  have hYbB : Yb ⊆ B := by rw [hPaid]; exact subset_union_right
  have hYU : Y ∪ Yb ⊆ U := union_subset (hYF.trans hF0U) (hYbB.trans hBU)
  exact ⟨hYU, hAvoid.mono_right hYU⟩

theorem pulled_paid_child_avoids_reference {V : Type} [Fintype V]
    (W : Finset V) (E₀ : Finset (Sym2 {x // x ∈ W}))
    (Ytot : Finset (Sym2 V))
    (hAvoid : Disjoint (SampledResource.lift W E₀) Ytot) :
    Disjoint E₀ (SampledResource.pull W Ytot) := by
  apply disjoint_left.mpr
  intro e heE heY
  have heLift : SampledResource.edgeLift W e ∈ SampledResource.lift W E₀ :=
    mem_image.mpr ⟨e, heE, rfl⟩
  exact disjoint_left.mp hAvoid heLift (mem_preimage.mp heY)

theorem pulled_paid_child_is_physical {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (Ytot : Finset (Sym2 V))
    (hLam : SparseEdge.ind Ytot ∈ S07V42.LamCore H.G H.lab F W) :
    SparseEdge.ind (SampledResource.pull W Ytot) ∈
      SparseEdge.lattice (H.G.comap Subtype.val) (H.lab ∘ Subtype.val) F := by
  have hCore : SparseEdge.ind Ytot ∈
      SparseEdge.lattice (S07V42.indG H.G W) H.lab F := hLam
  have hp := S07V42.pull_lattice Subtype.val_injective
    (S07V42.edgesIn_indG H.G W) hCore
  rw [S07V42.indG_comap] at hp
  convert hp using 1
  funext e
  simp only [S07V42.pullL, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp, SparseEdge.ind, SampledResource.pull,
    Finset.mem_preimage, SampledResource.edgeLift]

theorem pulled_paid_child_degree_budget {V : Type} [Fintype V]
    (W : Finset V) (Y Yb B Bc : Finset (Sym2 V))
    (a b : ℝ)
    (hY : ∀ v, (SelSimul.edeg Y v : ℝ) ≤ a)
    (hB : ∀ v, (SelSimul.edeg B v : ℝ) ≤ b)
    (hPaid : B = Bc ∪ Yb) :
    ∀ v : {x // x ∈ W},
      (SelSimul.edeg (SampledResource.pull W (Y ∪ Yb)) v : ℝ) ≤ a + b := by
  intro v
  have hYbB : Yb ⊆ B := by rw [hPaid]; exact subset_union_right
  have hYb : (SelSimul.edeg Yb v.1 : ℝ) ≤ b := by
    have hc := Finset.card_le_card
      (Finset.filter_subset_filter (p := fun e => v.1 ∈ e) hYbB)
    exact (show (SelSimul.edeg Yb v.1 : ℝ) ≤ SelSimul.edeg B v.1 by
      exact_mod_cast hc).trans (hB v.1)
  have hPull := SampledResource.degree_pull_le W (Y ∪ Yb) v
  have hUnion := SelSimul.edeg_union_le Y Yb v.1
  have hPull' : (SelSimul.edeg (SampledResource.pull W (Y ∪ Yb)) v : ℝ) ≤
      SelSimul.edeg (Y ∪ Yb) v.1 := by exact_mod_cast hPull
  have hUnion' : (SelSimul.edeg (Y ∪ Yb) v.1 : ℝ) ≤
      SelSimul.edeg Y v.1 + SelSimul.edeg Yb v.1 := by exact_mod_cast hUnion
  have hBound : (SelSimul.edeg (Y ∪ Yb) v.1 : ℝ) ≤ a + b := by
    exact hUnion'.trans (add_le_add (hY v.1) hYb)
  exact hPull'.trans hBound

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.paid_child_inside_reference_avoiding_stock
#print axioms TypedTriangle.CatalogNative.pulled_paid_child_avoids_reference
#print axioms TypedTriangle.CatalogNative.pulled_paid_child_is_physical
#print axioms TypedTriangle.CatalogNative.pulled_paid_child_degree_budget
