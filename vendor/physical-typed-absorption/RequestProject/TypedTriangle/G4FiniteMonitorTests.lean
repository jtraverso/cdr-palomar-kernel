/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G34NativePackingOneLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Index every local coordinate in every required bank stratum, together
with the full-monitor coordinates, in one finite family of packing tests. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open TypedTriangle.LocalizedCover

theorem finite_stratum_monitor_test_family {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (L K : ℕ) (Λ : ℝ)
    (bad : ℕ → Finset V)
    (loc : ℕ → Fin K → Sym2 V → ℝ)
    (full : Fin K → Sym2 V → ℝ)
    (hsize : (L + 2) * K ≤ Fintype.card V)
    (hloc : ∀ ℓ j T, IsAllowed H F T →
      |triSum (loc ℓ j) T| ≤ 3 * Λ * (T ∩ bad ℓ).card)
    (hfull : ∀ j T, IsAllowed H F T →
      |triSum (full j) T| ≤ 3 * Λ * T.card) :
    ((Fintype.card (Fin (L+1) × Fin K) + Fintype.card (Fin K) : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ) ∧
    (∀ k : Fin (L+1) × Fin K, ∀ T, IsAllowed H F T →
      |triSum (loc k.1.val k.2) T| ≤ 3 * Λ * (T ∩ bad k.1.val).card) ∧
    ∀ j : Fin K, ∀ T, IsAllowed H F T →
      |triSum (full j) T| ≤ 3 * Λ * T.card := by
  constructor
  · simpa only [Fintype.card_prod, Fintype.card_fin] using
      (show (((L + 1) * K + K : ℕ) : ℝ) ≤ Fintype.card V by
        exact_mod_cast (show (L + 1) * K + K ≤ Fintype.card V from by
          nlinarith only [hsize]))
  constructor
  · intro k T hT
    exact hloc k.1.val k.2 T hT
  · exact hfull

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.finite_stratum_monitor_test_family
