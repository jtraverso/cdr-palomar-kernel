/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ThreeHostGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The native bank's existing stratum budget pays all three geometry inputs. -/

open Finset Classical
noncomputable section

namespace TypedTriangle

theorem bank_stratum_three_host_geometries {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W outer bad : Finset V) (hW : W = univ \ outer)
    {α β : ℝ} {h : ℕ} (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hCore3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β)
    (hCore4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β h)
    (z : ℕ) (hbad : bad.card ≤ z)
    (hzCore : (z : ℝ) ≤ S07V42.coreDelta β h * W.card)
    (hz3 : (z : ℝ) ≤ β / 2 * W.card)
    (hz4 : (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card) :
    (CommonNbrCond (restrictedHost H bad) F (α / 2) ∧
     HingeCond (restrictedHost H bad) F (α / 2) h) ∧
    (CommonNbrCond (restrictedHost H outer) F (β / 2) ∧
     HingeCond (restrictedHost H outer) F (β / 2) h) ∧
    (CommonNbrCond (restrictedHost H (outer ∪ bad)) F (β / 2) ∧
     HingeCond (restrictedHost H (outer ∪ bad)) F (β / 2) h) := by
  have hWn : (W.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ W)
  have hbadz : (bad.card : ℝ) ≤ z := by exact_mod_cast hbad
  have hscale : β / 2 * (W.card : ℝ) ≤
      α / 2 * Fintype.card V := by
    calc
      β / 2 * (W.card : ℝ) ≤ α / 2 * W.card :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ α / 2 * Fintype.card V :=
        mul_le_mul_of_nonneg_left hWn (by positivity)
  have hBad3 : (bad.card : ℝ) ≤ α * Fintype.card V / 2 := by
    calc (bad.card : ℝ) ≤ z := hbadz
      _ ≤ β / 2 * W.card := hz3
      _ ≤ α / 2 * Fintype.card V := hscale
      _ = α * Fintype.card V / 2 := by ring
  have hBad4 : (bad.card : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤
      α / 2 * Fintype.card V := by
    calc
      (bad.card : ℝ) * 2 ^ Nat.choose (h+1) 2
          ≤ (z : ℝ) * 2 ^ Nat.choose (h+1) 2 :=
            mul_le_mul_of_nonneg_right hbadz (by positivity)
      _ ≤ β / 2 * W.card := hz4
      _ ≤ α / 2 * Fintype.card V := hscale
  exact three_host_geometries H F W outer bad hW hα hβ h3 h4
    hCore3 hCore4 hBad3 hBad4 (hbadz.trans hzCore)

end TypedTriangle

#print axioms TypedTriangle.bank_stratum_three_host_geometries
