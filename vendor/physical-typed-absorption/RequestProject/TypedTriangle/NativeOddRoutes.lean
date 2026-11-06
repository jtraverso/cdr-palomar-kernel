/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeRobustLinks
public import RequestProject.Selectors.RobustOddRoute
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Join the native H3--H4 geometry to V20. Pending rc3 integration.
These are single-component paths; they do not assert the simultaneous catalogue. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.ActiveCover
open ComponentRows
variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

/-- Native geometry instantiates V20's robust-diameter contract exactly. -/
theorem native_robustDiam {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (a : V) (K : Finset V) (hK : IsActiveRow G lab F (a, K))
    (B : Finset (Sym2 V)) (d M : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hw1 : (M : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((M : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hw3 : (M : ℝ) + d ≤ α * Fintype.card V / 2) :
    SelRoute.RobustDiam (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B)
      K M (3 * ⌊2 / α⌋₊) :=
  native_component_robust_diameter hα hH3 hH4 a K hK B d M hdeg hw1 hw2 hw3

/-- Short odd SIMPLE paths from the original hypotheses, in a non-bipartite
active component, avoiding both the used edges and the prescribed vertices. -/
theorem native_odd_path_nonbip {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (a : V) (K : Finset V) (hK : IsActiveRow G lab F (a, K))
    (hNB : ¬ IsBip G lab F (a, K))
    (B : Finset (Sym2 V)) (d M b : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hw1 : (M : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((M : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hw3 : (M : ℝ) + d ≤ α * Fintype.card V / 2)
    (hbudget : b + 3 * (3 * ⌊2 / α⌋₊) + 1 ≤ M)
    (Z : Finset V) (hZ : Z.card ≤ b) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    ∃ p : (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B).Walk x y,
      p.IsPath ∧ Odd p.length ∧ p.length ≤ 4 * (3 * ⌊2 / α⌋₊) + 1 ∧
      ∀ z ∈ p.support, z ∈ K ∧ z ∉ Z := by
  exact SelRoute.odd_path_nonbip hbudget
    (native_robustDiam hα hH3 hH4 a K hK B d M hdeg hw1 hw2 hw3)
    (native_component_robust_nonbip hα hH3 hH4 a K hK hNB B d M hdeg hw1 hw2)
    Z hZ hx hy hxy hxZ hyZ

/-- Bipartite sides are fixed in the original link, before the paths.
Only pairs on opposite sides are claimed. -/
theorem native_odd_path_bip {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (a : V) (K : Finset V) (hK : IsActiveRow G lab F (a, K))
    (B : Finset (Sym2 V)) (d M : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hw1 : (M : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((M : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hw3 : (M : ℝ) + d ≤ α * Fintype.card V / 2)
    (X : Set V)
    (hbip : ∀ x ∈ K, ∀ y ∈ K, (link G lab F a).Adj x y → (x ∈ X ↔ y ∉ X))
    (Z : Finset V) (hZ : Z.card ≤ M) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : ¬ (x ∈ X ↔ y ∈ X))
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    ∃ p : (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B).Walk x y,
      p.IsPath ∧ Odd p.length ∧ p.length ≤ 3 * ⌊2 / α⌋₊ ∧
      ∀ z ∈ p.support, z ∈ K ∧ z ∉ Z := by
  exact SelRoute.odd_path_bip (B := M) le_rfl
    (native_robustDiam hα hH3 hH4 a K hK B d M hdeg hw1 hw2 hw3)
    X (fun x hx y hy hxy => hbip x hx y hy hxy.1) Z hZ hx hy hxy hxZ hyZ

end TypedTriangle.ActiveCover
