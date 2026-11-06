/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativeStratumChoice
public import RequestProject.S07V47.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Instantiate uniform physical weights on every actual bank stratum.
The bank setting is abstract here, so its potentially large protected
definition is unfolded only when the caller supplies it. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open S07V40 S07V42 S07V44 S07V46 S07V47 TypedTriangle.LocalizedCover

theorem choose_weights_on_bank_strata (α β q : ℝ)
    (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ n₁ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W outer : Finset V)
        (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ \ outer) d c E)
        (S : MacroSetting V (ClassQ H.G H.lab F (univ \ outer) × ℤ) (Cat d R))
        (N L z : ℕ)
        (MonS : ∀ ℓ, PhysicalMonitors C0 R (Zstrat S N (ℓ+1)) A M K)
        (Fm : FullMonitor C0 R A M K)
        (hBank : MacroBank S L N) (hz : S.zmax = z),
        n₁ ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc : ℕ → Fin K → Sym2 V → ℝ,
          ∃ full : Fin K → Sym2 V → ℝ,
          (∀ ℓ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R (Zstrat S N (ℓ+1)))
                (MonS ℓ).psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ ℓ j T, IsAllowed H F T →
            |triSum (loc ℓ j) T| ≤
              3 * Λ * (T ∩ Zstrat S N (ℓ+1)).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * Λ * T.card := by
  obtain ⟨Λ,hΛ,n₁,hChoice⟩ :=
    choose_uniform_native_stratum_weights α β q h d c E R A M K
      hα hβ hq hβα
  refine ⟨Λ,hΛ,n₁,?_⟩
  intro V I _ H F W outer hW C0 S N L z MonS Fm hBank hz hn hWlo
    h3 h4 hCore3 hCore4 hzCore hz3 hz4 hzDel
  have hSmall : ∀ ℓ, (Zstrat S N (ℓ+1)).card ≤ z := by
    intro ℓ
    simpa only [Zstrat, hz] using
      (hBank.small _ ((preStrat_le (S := S) N (ℓ+1)).trans
        (numRounds_le (S := S) N)))
  exact hChoice H F W outer hW C0 (fun ℓ => Zstrat S N (ℓ+1))
    MonS Fm z hn hWlo h3 h4 hCore3 hCore4 hSmall hzCore hz3 hz4 hzDel

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.choose_weights_on_bank_strata
