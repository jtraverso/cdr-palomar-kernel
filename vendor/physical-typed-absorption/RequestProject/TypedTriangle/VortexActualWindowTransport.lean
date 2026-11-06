/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexActualWindowPools
public import RequestProject.TypedTriangle.VortexWindowRouteRate
public import RequestProject.TypedTriangle.VortexResidualWindowRoutes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

theorem graph_eq_raw_sdiff_holes {V I : Type*} [Fintype V]
    (Hraw Hact : Host V I) (hGraph : Hact.G ≤ Hraw.G) :
    Hact.G = Hraw.G \ SimpleGraph.fromEdgeSet
      ((edges Hraw \ edges Hact : Finset (Sym2 V)) : Set (Sym2 V)) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  change Hact.G.Adj x y ↔ Hraw.G.Adj x y ∧
    ¬ (SimpleGraph.fromEdgeSet ((edges Hraw \ edges Hact : Finset (Sym2 V)) :
      Set (Sym2 V))).Adj x y
  have hRawMem : s(x,y) ∈ edges Hraw ↔ Hraw.G.Adj x y := by simp only
    [edges,mem_filter,mem_univ,true_and,SimpleGraph.mem_edgeSet]
  have hActMem : s(x,y) ∈ edges Hact ↔ Hact.G.Adj x y := by simp only
    [edges,mem_filter,mem_univ,true_and,SimpleGraph.mem_edgeSet]
  constructor
  · intro hxy
    exact ⟨hGraph hxy,fun hc => (mem_sdiff.mp hc.1).2 (hActMem.mpr hxy)⟩
  · rintro ⟨hxy,hMissing⟩
    by_contra hNot
    exact hMissing ⟨mem_sdiff.mpr ⟨hRawMem.mpr hxy,fun he => hNot (hActMem.mp he)⟩,hxy.ne⟩

/-- A single adapter turns the stored raw window tests into the tests
needed by the paid parent, with the exact graph representation of its holes. -/
theorem actual_window_tests_after_sparse_payment {V I : Type} [Fintype V]
    (Hraw Hact : Host V I) (F : Set (Multiset I))
    (hGraph : Hact.G ≤ Hraw.G) (hLabels : Hact.lab = Hraw.lab)
    (W Z : Finset V) (a q ζ poolLower : ℝ) (m : ℕ)
    (ha : 0 < a) (hq : 0 < q) (hζ : 0 ≤ ζ) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : ((W \ Z).card : ℝ) ≤ 2*q*Fintype.card V)
    (hCap : ζ ≤ windowRouteRate a q m/4)
    (hHoles : ∀ v, (degIn (edges Hraw \ edges Hact) v : ℝ) ≤ ζ*Fintype.card V)
    (hPaths : ∀ v x y, OrigAdm Hraw.G Hraw.lab F v x y →
      a*(Fintype.card V : ℝ)^m*q^m/4 ≤
        (pathsIn (ComponentRows.link Hraw.G Hraw.lab F v) m x y (W \ Z)).card)
    (hPools : ∀ u v, u ≠ v → ∀ k, ({Hraw.lab u,Hraw.lab v,k} : Multiset I) ∈ F →
      poolLower ≤ ((commonNbrs Hraw k u v) ∩ W).card) :
    S07V27.RouteProp Hact.G Hact.lab F (m+1) (windowRouteRate a q m/4) (W \ Z) ∧
      ∀ u v, u ≠ v → ∀ k, ({Hact.lab u,Hact.lab v,k} : Multiset I) ∈ F →
        poolLower - Z.card - 2*(⌊ζ*Fintype.card V⌋₊ : ℝ) ≤
          ((commonNbrs Hact k u v) ∩ (W \ Z)).card := by
  letI : DecidableEq V := Classical.decEq _
  let C := edges Hraw \ edges Hact
  let D := SimpleGraph.fromEdgeSet (C : Set (Sym2 V))
  letI : DecidableRel D.Adj := Classical.decRel _
  let d := ⌊ζ*Fintype.card V⌋₊
  have hDeg : ∀ v, degIn C v ≤ d := fun v => Nat.le_floor (hHoles v)
  have hDegSparse : ∀ v, SparseEdge.degIn C v ≤ d := hDeg
  have hDegreeGraph : ∀ v, D.degree v ≤ d := by
    intro v
    have hv := CorePaid.fromEdges_degree_le C
      (CorePaid.edges_diagonal_free sdiff_subset) hDeg v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hd : (d : ℝ) ≤ windowRouteRate a q m/4*Fintype.card V :=
    (Nat.floor_le (mul_nonneg hζ (by positivity))).trans
      (mul_le_mul_of_nonneg_right hCap (by positivity))
  have hActualGraph : Hact.G = Hraw.G \ D := graph_eq_raw_sdiff_holes Hraw Hact hGraph
  have hSubGraph : (subHost Hraw (edges Hraw \ C)).G = Hact.G :=
    (StockEntry.g4_graph_sdiff_eq_subHost Hraw C).symm.trans hActualGraph.symm
  have hSubHost : subHost Hraw (edges Hraw \ C) = Hact :=
    congrArg₂ (fun G lab => (⟨G,lab⟩ : Host V I)) hSubGraph hLabels.symm
  have hRawRoute := routeProp_of_window_path_count Hraw.G Hraw.lab F (W \ Z)
    a q m ha hq hm hOrder hWindow hPaths
  constructor
  · rw [hLabels,hActualGraph]
    exact routeProp_after_sparse_payment Hraw.G D Hraw.lab F (W \ Z) (m+1) d
      (windowRouteRate a q m) (windowRouteRate_pos m ha hq) hRawRoute hDegreeGraph hd
  · intro u v huv k hk
    have hkRaw : ({Hraw.lab u,Hraw.lab v,k} : Multiset I) ∈ F := by
      simpa only [hLabels] using hk
    have hPool := hPools u v huv k hkRaw
    have hLoss := commonNbr_pool_after_vertex_and_edge_payment Hraw W Z C d hDegSparse u v k
    rw [hSubHost] at hLoss
    change poolLower - Z.card - 2*(d : ℝ) ≤ _
    linarith

#print axioms graph_eq_raw_sdiff_holes
#print axioms actual_window_tests_after_sparse_payment
end TypedTriangle.Vortex
