/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4StrataGeometry
public import RequestProject.TypedTriangle.G4UniformPhysicalWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Physical monitor weights on the actual bank stratum, using its native
geometry budget rather than extra host hypotheses. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open S07V42 S07V44 S07V46 TypedTriangle.LocalizedCover

theorem uniform_weights_on_native_stratum (α β : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) :
    ∃ L : ℝ, 0 < L ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (W outer bad : Finset V) (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
        (Fm : FullMonitor C0 R A M K)
        (z : ℕ),
        n₀ ≤ Fintype.card (Survivors bad) →
        n₀ ≤ Fintype.card (Survivors (outer ∪ bad)) →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        bad.card ≤ z →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        ((bad.subtype (· ∉ outer)).card : ℝ) ≤
          S07V37.delOf (β/2) h * Fintype.card (Survivors outer) →
        ∃ loc full : Fin K → Sym2 V → ℝ,
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ j T, IsAllowed H F T →
            |triSum (loc j) T| ≤ 3 * L * (T∩bad).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * L * T.card := by
  obtain ⟨L,hL,n₀,hWeights⟩ :=
    uniform_physical_monitor_weights (α/2) (β/2) h d c E R A M K
      (by positivity) (by positivity)
  refine ⟨L,hL,n₀,?_⟩
  intro V I _ H F W outer bad hW C0 Mon Fm z hnBad hnJoint h3 h4 hCore3
    hCore4 hbad hzCore hz3 hz4 hSmall
  obtain ⟨⟨hBad3,hBad4⟩,⟨hOuter3,hOuter4⟩,⟨hJoint3,hJoint4⟩⟩ :=
    bank_stratum_three_host_geometries H F W outer bad hW hα hβ hβα
      h3 h4 hCore3 hCore4 z hbad hzCore hz3 hz4
  exact hWeights H F outer bad C0 Mon Fm hnBad hnJoint hBad3 hBad4
    hJoint3 hJoint4 hOuter3 hOuter4 hSmall

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.uniform_weights_on_native_stratum
