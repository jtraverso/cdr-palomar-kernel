/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4WeightsOnActualStratum
public import RequestProject.TypedTriangle.G4StratumHostSizes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The native geometric and cardinal budgets supply physical weights for
the actual bank stratum. Only the bank's small deletion window is explicit. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open S07V42 S07V44 S07V46 TypedTriangle.LocalizedCover

theorem uniform_native_stratum_weights (α β q : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∃ L : ℝ, 0 < L ∧ ∃ n₁ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (W outer bad : Finset V) (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
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
        bad.card ≤ z →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
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
    uniform_weights_on_native_stratum α β h d c E R A M K hα hβ hβα
  let n₁ := ⌈4 * (n₀ : ℝ) / q⌉₊ + 1
  refine ⟨L,hL,n₁,?_⟩
  intro V I _ H F W outer bad hW C0 Mon Fm z hn hWlo h3 h4 hCore3
    hCore4 hbad hzCore hz3 hz4 hzDel
  have hnReal : (n₀ : ℝ) ≤ q * Fintype.card V / 4 := by
    have hceil : 4 * (n₀ : ℝ) / q ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast
        (show ⌈4 * (n₀ : ℝ) / q⌉₊ ≤ Fintype.card V from by dsimp [n₁] at hn; omega))
    have hmul := (div_le_iff₀ hq).mp hceil
    nlinarith only [hmul]
  have hzHalf : (z : ℝ) ≤ W.card / 2 := by
    have hδ := S07V42.coreDelta_le_half β h
    have hmul := mul_le_mul_of_nonneg_right hδ
      (show (0 : ℝ) ≤ W.card by positivity)
    nlinarith only [hzCore, hmul]
  obtain ⟨hnBad,hnJoint⟩ := native_stratum_host_sizes W outer bad hW
    z n₀ q hbad hzHalf hWlo hnReal
  have hSmall := native_stratum_deletion_window W outer bad hW
    z β h hbad hzDel
  exact hWeights H F W outer bad hW C0 Mon Fm z hnBad hnJoint
    h3 h4 hCore3 hCore4 hbad hzCore hz3 hz4 hSmall

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.uniform_native_stratum_weights
