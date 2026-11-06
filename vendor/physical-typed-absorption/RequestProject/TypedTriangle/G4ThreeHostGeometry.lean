/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4CoreStratumGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The three actual restricted hosts needed by physical monitor localization. -/

open Finset Classical
noncomputable section

namespace TypedTriangle

theorem three_host_geometries {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W outer bad : Finset V) (hW : W = univ \ outer)
    {α β : ℝ} {h : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hCore3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β)
    (hCore4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β h)
    (hBad3 : (bad.card : ℝ) ≤ α * Fintype.card V / 2)
    (hBad4 : (bad.card : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤
      α / 2 * Fintype.card V)
    (hBadCore : (bad.card : ℝ) ≤ S07V42.coreDelta β h * W.card) :
    (CommonNbrCond (restrictedHost H bad) F (α / 2) ∧
     HingeCond (restrictedHost H bad) F (α / 2) h) ∧
    (CommonNbrCond (restrictedHost H outer) F (β / 2) ∧
     HingeCond (restrictedHost H outer) F (β / 2) h) ∧
    (CommonNbrCond (restrictedHost H (outer ∪ bad)) F (β / 2) ∧
     HingeCond (restrictedHost H (outer ∪ bad)) F (β / 2) h) := by
  have hBad := original_geometry_restrictedHost hα.le h3 h4 bad hBad3 hBad4
  have hZero : ((∅ : Finset V).card : ℝ) ≤
      S07V42.coreDelta β h * W.card := by
    simpa only [card_empty, Nat.cast_zero] using
      (mul_nonneg (S07V42.coreDelta_nonneg hβ h)
        (show (0 : ℝ) ≤ W.card by positivity))
  have hOuter := core_geometry_on_joint_restriction H F W outer ∅ hW
    hβ hCore3 hCore4 hZero
  have hOuter' : CommonNbrCond (restrictedHost H outer) F (β / 2) ∧
      HingeCond (restrictedHost H outer) F (β / 2) h := by
    have heq : outer ∪ (∅ : Finset V) = outer := by simp
    exact (congrArg (fun Z : Finset V =>
      CommonNbrCond (restrictedHost H Z) F (β / 2) ∧
      HingeCond (restrictedHost H Z) F (β / 2) h) heq).mp hOuter
  have hJoint := core_geometry_on_joint_restriction H F W outer bad hW
    hβ hCore3 hCore4 hBadCore
  exact ⟨hBad, hOuter', hJoint⟩

end TypedTriangle

#print axioms TypedTriangle.three_host_geometries
