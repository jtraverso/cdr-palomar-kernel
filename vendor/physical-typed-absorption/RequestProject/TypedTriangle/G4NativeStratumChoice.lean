/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativeMonitorReady
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Uniform physical weights for a family of actual small strata.  The
abstract stratum function keeps the bank recursion out of this selection. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open S07V42 S07V44 S07V46 TypedTriangle.LocalizedCover

theorem choose_uniform_native_stratum_weights (α β q : ℝ)
    (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ n₁ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W outer : Finset V)
        (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ \ outer) d c E)
        (Z : ℕ → Finset V)
        (MonS : ∀ ℓ, PhysicalMonitors C0 R (Z ℓ) A M K)
        (Fm : FullMonitor C0 R A M K)
        (z : ℕ),
        n₁ ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (∀ ℓ, (Z ℓ).card ≤ z) →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc : ℕ → Fin K → Sym2 V → ℝ,
          ∃ full : Fin K → Sym2 V → ℝ,
          (∀ ℓ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R (Z ℓ)) (MonS ℓ).psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ ℓ j T, IsAllowed H F T →
            |triSum (loc ℓ j) T| ≤ 3 * Λ * (T ∩ Z ℓ).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * Λ * T.card := by
  obtain ⟨Λ,hΛ,n₁,hWeights⟩ :=
    uniform_native_stratum_weights α β q h d c E R A M K hα hβ hq hβα
  refine ⟨Λ,hΛ,n₁,?_⟩
  intro V I _ H F W outer hW C0 Z MonS Fm z hn hWlo h3 h4
    hCore3 hCore4 hSmall hzCore hz3 hz4 hzDel
  have hEach : ∀ ℓ, ∃ loc full : Fin K → Sym2 V → ℝ,
      (∀ j (x : MCore H.G H.lab F (univ \ outer)),
        ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
          physMonReal C0 (Dset C0 R (Z ℓ)) (MonS ℓ).psi j x) ∧
      (∀ j (x : MCore H.G H.lab F (univ \ outer)),
        ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
          physMonReal C0 ∅ Fm.psi j x) ∧
      (∀ j T, IsAllowed H F T →
        |triSum (loc j) T| ≤ 3 * Λ * (T ∩ Z ℓ).card) ∧
      ∀ j T, IsAllowed H F T →
        |triSum (full j) T| ≤ 3 * Λ * T.card := by
    intro ℓ
    exact hWeights H F W outer (Z ℓ) hW C0 (MonS ℓ) Fm z hn hWlo
      h3 h4 hCore3 hCore4 (hSmall ℓ) hzCore hz3 hz4 hzDel
  choose loc full hLocRep hFullRep hLocBound hFullBound using hEach
  exact ⟨loc, full 0, hLocRep, hFullRep 0, hLocBound, hFullBound 0⟩

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.choose_uniform_native_stratum_weights
