/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformSampledPaidSchedule
public import RequestProject.TypedTriangle.VortexPreparedBankCatalog
public import RequestProject.TypedTriangle.VortexSampledQuarterSize
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex
open CatalogNative S07V40 S07V42 S07V43 S07V44

/-- The prepared core returned by the scheduled sample is large enough for
the fixed-window bank after one host-size threshold. This lemma also fixes
the parameter order: the bank's protection tolerance is selected before the
host and its actual protected edge set is supplied only afterwards. -/
theorem scheduled_prepared_bank_on_same_window (α β q τ : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q)
    (hτ : τ ≤ 1 / 2) :
    ∃ d c E d' c' E' Ecell : ℕ,
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      ∃ κ ε η : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ εcap ∧ 0 < η ∧
      ∃ n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (F0 : Finset (Sym2 V)),
          n₀ ≤ Fintype.card V →
          q * Fintype.card V / 2 ≤ W.card →
          (A.card : ℝ) ≤ τ * W.card →
          CommonNbrCond H F α → HingeCond H F α h →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F β →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F β h →
          (∀ v, (degIn F0 v : ℝ) ≤ η *
            (W \ liftVertexSet (univ \ W) A).card) →
          ∃ (C0 : CoreCompression H.G H.lab F
                (W \ liftVertexSet (univ \ W) A) d c E) (qm z : ℕ),
            0 < qm ∧ ε / 4 * (W \ liftVertexSet (univ \ W) A).card ≤ (qm : ℝ) ∧
            (z : ℝ) ≤ δcap * (W \ liftVertexSet (univ \ W) A).card ∧
            (∀ Z : Finset V, Z.card ≤ z →
              Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
            let Rc := catR β d c E d' c' E'
            let Setting := S07V47.protSetting C0 Rc P qm Ecell z F0
            let M := ⌊κ * ((W \ liftVertexSet (univ \ W) A).card : ℝ)^2⌋₊
            MacroBank Setting (Fintype.card (Cat d Rc)) M ∧
              Disjoint (Br Setting M) F0 ∧
              (∀ v, (deg (Br Setting M) v : ℝ) <
                ε * (W \ liftVertexSet (univ \ W) A).card) ∧
              ∀ j, CatalogGen C0 Rc (Zstrat Setting M j) := by
  obtain ⟨d,c,E,d',c',E',Ecell,hBank⟩ :=
    bank_on_prepared_fixed_window α β h hα hβ
  refine ⟨d,c,E,d',c',E',Ecell,?_⟩
  intro P εcap δcap hεcap hδcap
  obtain ⟨κ,ε,η,hκ,hε,hεcap,hη,nBank,hMake⟩ :=
    hBank P εcap δcap hεcap hδcap
  let n₀ := ⌈4 * (nBank : ℝ) / q⌉₊
  refine ⟨κ,ε,η,hκ,hε,hεcap,hη,n₀,?_⟩
  intro V I _ H F W A F0 hn hW hA h3 h4 h3A h4A hF0
  have hquarter := sampled_quarter_size_after_relative_trim W A q τ hW hA hτ
  have hnBank : nBank ≤ (W \ liftVertexSet (univ \ W) A).card := by
    have hceil : (n₀ : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    have hcalc : 4 * (nBank : ℝ) ≤ (n₀ : ℝ) * q :=
      (div_le_iff₀ hq).mp (Nat.le_ceil _)
    have hmul := mul_le_mul_of_nonneg_right hceil hq.le
    exact_mod_cast (show (nBank : ℝ) ≤
        (W \ liftVertexSet (univ \ W) A).card by
      nlinarith [hquarter,hcalc,hmul])
  exact hMake H F W A F0 hnBank h3 h4 h3A h4A hF0

#print axioms scheduled_prepared_bank_on_same_window

end TypedTriangle.Vortex
