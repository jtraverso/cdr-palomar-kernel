/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformSampledPaidScheduleWithPool
public import RequestProject.TypedTriangle.VortexFixedWindowStructuredResources
public import RequestProject.TypedTriangle.VortexPreparedBankCatalogEarlyProtection
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44

/-- Completion stock, physical selector, and protected geometric bank on
one prescribed prepared window. The only window inputs are precisely the
size, pool, route, and nested H3/H4 exported by the scheduled sample; no
stock or bank is assumed. All constants precede the host. -/
theorem stock_bank_on_prepared_window_with_structured_future_early_protection {I : Type}
    (F : Set (Multiset I)) (α C βBank : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank) :
    ∃ γS : ℝ, 0 < γS ∧ ∃ d c E d' c' E' Ecell : ℕ, ∃ ηBank : ℝ, 0 < ηBank ∧
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      ∃ κBank εBank : ℝ,
        0 < κBank ∧ 0 < εBank ∧ εBank ≤ εcap ∧
        ∀ (αPool qPool εRoute : ℝ) (t : ℕ),
          0 < αPool → 0 < qPool → 0 < εRoute → Odd t → 3 ≤ t →
        ∃ θT : ℝ, 0 < θT ∧
          ∀ ρcap τcap : ℝ, 0 < ρcap → 0 < τcap →
            ∃ ρ κStock τR : ℝ, 0 < ρ ∧ ρ ≤ ρcap ∧
              0 < κStock ∧ 0 < τR ∧ τR ≤ τcap ∧ ρ ≤ τR ∧
              ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V]
                (H : Host V I) (φ : Finset V → ℝ)
                (W : Finset V) (A : Finset (Survivors (univ \ W)))
                (U : Finset V) (T S : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT dS : ℕ),
                let W' := W \ liftVertexSet (univ \ W) A
                n₀ ≤ Fintype.card V →
                IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
                CommonNbrCond H F α → HingeCond H F α h →
                qPool * Fintype.card V / 2 ≤ W'.card →
                (∀ u v : V, u ≠ v → ∀ k : I,
                  ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
                  qPool * αPool * Fintype.card V / 2 ≤
                    ((commonNbrs H k u v) ∩ W').card) →
                S07V27.RouteProp H.G H.lab F t εRoute W' →
                CommonNbrCond
                  (restrictedHost (restrictedHost H (univ \ W)) A) F βBank →
                HingeCond
                  (restrictedHost (restrictedHost H (univ \ W)) A) F βBank h →
                IsDecomposition H F T DT → Disjoint T S →
                Disjoint W' U → (∀ e ∈ S, ∀ v ∈ e, v ∈ U) →
                (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ γS*Fintype.card V →
                (dS:ℝ) ≤ (ηBank/2)*W'.card →
                (∀ v, degIn T v ≤ dT) →
                (dT : ℝ) ≤ θT * Fintype.card V →
                ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V))
                  (C0 : CoreCompression H.G H.lab F W' d c E) (qm z : ℕ),
                  IsDecomposition H F (cover D) D ∧
                  Disjoint (cover D) (T ∪ S) ∧
                  (∀ v, (degIn (cover D) v : ℝ) < ρ * Fintype.card V) ∧
                  (∀ u v, H.G.Adj u v →
                    κStock * Fintype.card V ≤ (good H F D u v).card) ∧
                  Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
                  (∀ e ∈ R, ∃ v ∈ e, v ∈ W') ∧ Disjoint R S ∧
                  (∀ v, (edeg R v : ℝ) ≤ τR * Fintype.card V) ∧
                  (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                    (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W') ∧
                    ∀ v, (edeg Y0 v : ℝ) ≤ τR * Fintype.card V) ∧
                  (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
                    ∃ Ps Y : Finset (Sym2 V),
                      R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                      (∀ e ∈ Y, ∀ v ∈ e, v ∈ W') ∧
                      (∀ v, (edeg Y v : ℝ) ≤ τR * Fintype.card V) ∧
                      IsPhysical H F Y) ∧
                  0 < qm ∧ εBank / 4 * W'.card ≤ (qm : ℝ) ∧
                  (z : ℝ) ≤ δcap * W'.card ∧
                  (∀ Z : Finset V, Z.card ≤ z →
                    Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
                  let Rc := catR βBank d c E d' c' E'
                  let F0 := ((cover D ∪ R) ∪ T) ∪ S
                  let Setting := S07V47.protSetting C0 Rc P qm Ecell z F0
                  let M := ⌊κBank * (W'.card : ℝ)^2⌋₊
                  MacroBank Setting (Fintype.card (Cat d Rc)) M ∧
                    Disjoint (Br Setting M) F0 ∧
                    (∀ v, (deg (Br Setting M) v : ℝ) < εBank * W'.card) ∧
                    ∀ j, CatalogGen C0 Rc (Zstrat Setting M j) := by
  obtain ⟨γS,hγS,hResourcesBeforeRate⟩ :=
    uniform_fixed_window_resources_protecting_vertices F α C h hα hC
  obtain ⟨d,c,E,d',c',E',Ecell,ηBank,hηBank,hBankWindow⟩ :=
    bank_on_prepared_fixed_window_early_protection α βBank h hα hβBank
  refine ⟨γS,hγS,d,c,E,d',c',E',Ecell,ηBank,hηBank,?_⟩
  intro P εcap δcap hεcap hδcap
  obtain ⟨κBank,εBank,hκBank,hεBank,hεcap,nBank,hBank⟩ :=
    hBankWindow P εcap δcap hεcap hδcap
  refine ⟨κBank,εBank,hκBank,hεBank,hεcap,?_⟩
  intro αPool qPool εRoute t hαPool hqPool hεRoute ht ht3
  obtain ⟨θT,hθT,hResources⟩ :=
    hResourcesBeforeRate αPool qPool εRoute (ηBank/2) t
      hαPool hqPool hεRoute (by positivity) ht ht3
  refine ⟨θT,hθT,?_⟩
  intro ρcap τcap hρcap hτcap
  obtain ⟨ρ,κStock,τR,hρ,hρcap,hκStock,hτR,hτcap,hρτ,nResources,hMake⟩ :=
    hResources ρcap τcap hρcap hτcap
  let n₀ := max nResources ⌈2 * (nBank : ℝ) / qPool⌉₊
  refine ⟨ρ,κStock,τR,hρ,hρcap,hκStock,hτR,hτcap,hρτ,n₀,?_⟩
  intro V _ H φ W A U T S DT dT dS W' hn hSeed hPhys h3 h4 hW hPool hRoute
    h3A h4A hT hTS hWU hSU hSd hScap hSMacro hTd hTcap
  have hnResources : nResources ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  have hnCeil : ⌈2 * (nBank : ℝ) / qPool⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  have hnBank : nBank ≤ W'.card := by
    have hceil : (⌈2 * (nBank : ℝ) / qPool⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnCeil
    have h2n : 2 * (nBank : ℝ) ≤
        (⌈2 * (nBank : ℝ) / qPool⌉₊ : ℝ) * qPool :=
      (div_le_iff₀ hqPool).mp (Nat.le_ceil _)
    have hscale := mul_le_mul_of_nonneg_right hceil hqPool.le
    exact_mod_cast (show (nBank : ℝ) ≤ W'.card by
      nlinarith [hW,h2n,hscale])
  obtain ⟨D,R,hD,hDT,hDd,hSupply,hRdis,hR,hRinc,hRS,hRd,hFsmall,hY0,hMode⟩ :=
    hMake H φ W' U T S DT dT dS hnResources hSeed hPhys h3 h4 hW hPool
      hRoute hT hTS hWU hSU hSd hScap hTd hTcap
  let F0 := ((cover D ∪ R) ∪ T) ∪ S
  have hF0 : ∀ v, (degIn F0 v:ℝ) ≤ ηBank*W'.card := by
    intro v
    have hu := edeg_union_le ((cover D ∪ R) ∪ T) S v
    change degIn F0 v ≤ degIn ((cover D ∪ R) ∪ T) v + degIn S v at hu
    have huR : (degIn F0 v:ℝ) ≤ degIn ((cover D ∪ R) ∪ T) v + degIn S v := by
      exact_mod_cast hu
    have hs : (degIn S v:ℝ) ≤ dS := by exact_mod_cast hSd v
    nlinarith only [huR,hFsmall v,hs,hSMacro]
  obtain ⟨C0,qm,z,hqm,hql,hz,hCZ,hMacro,hBDis,hBDeg,hCat⟩ :=
    hBank H F W A F0 hnBank h3 h4 h3A h4A hF0
  exact ⟨D,R,C0,qm,z,hD,hDT,hDd,hSupply,hRdis,hR,hRinc,hRS,hRd,hY0,hMode,
    hqm,hql,hz,hCZ,hMacro,hBDis,hBDeg,hCat⟩

#print axioms stock_bank_on_prepared_window_with_structured_future_early_protection

end TypedTriangle.Vortex
