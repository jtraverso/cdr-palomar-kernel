/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativeOneLayerBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Native one-layer G3/G4 entry, with monitor weights, scales and the bank
chosen before the monitored packing. The terminal outcome uses its same Y. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open BasalIncidence StockEntry S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

theorem native_bank_entry_one_layer {I : Type} (F : Set (Multiset I))
    (α C ηChild : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hChild : 0 < ηChild)
    (hh : 6 ≤ h) :
    ∃ q : ℝ, 0 < q ∧
      ∃ (d c E d' c' E' Ecell A M K P : ℕ) (κ εBank : ℝ),
      0 < κ ∧ 0 < εBank ∧
      ∃ ηT : ℝ, 0 < ηT ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        ∃ W : Finset V,
          ∀ (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
            IsDecomposition H F T DT →
            (∀ v, SparseEdge.degIn T v ≤ dT) →
            (dT : ℝ) ≤ ηT * Fintype.card V →
            ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V))
              (qSel z N : ℕ)
              (C0 : CoreCompression H.G H.lab F W d c E),
              ∃ (Y : Finset (Sym2 V)) (x : MCore H.G H.lab F W) (J : ℕ),
                MacroBank (protSetting C0
                  (catR (α*q^h/4) d c E d' c' E')
                  P qSel Ecell z ((cover D ∪ R) ∪ T))
                  (Fintype.card (Cat d
                    (catR (α*q^h/4) d c E d' c' E'))) N ∧
                Y ⊆ ((cover D ∪ R) ∪ T) ∧
                Y ⊆ edges H ∧
                J ≤ Fintype.card (Cat
                  d (catR (α*q^h/4) d c E d' c' E')) ∧
                (x : Sym2 V → ℤ) = ind Y ∧
                ProtOutcome C0
                  (catR (α*q^h/4) d c E d' c' E')
                  P qSel Ecell z ((cover D ∪ R) ∪ T) N J x := by
  obtain ⟨q,hq,hq1,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,
    hκ,hεBank,hP,hG34⟩ :=
    native_monitored_packing_one_layer F α C ηChild h 1
      hα hC hChild hh
  let β := α*q^h/4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β ≤ α := by
    have hpow : q^h ≤ (1:ℝ) := pow_le_one₀ hq.le hq1
    have hmul := mul_le_mul_of_nonneg_left hpow hα.le
    dsimp [β]
    nlinarith only [hmul,hα]
  let Rc := catR β d c E d' c' E'
  let Lbank := Fintype.card (Cat d Rc)
  obtain ⟨Λ,hΛ,nWeights,hActivate⟩ :=
    activate_bank_after_g34_result α β q h d c E Rc A M K
      hα hβ hq hβα
  let Bstatic := 2*Ecell*(2*Lbank*P)
  obtain ⟨γ,η,δ,hγ,hη,hδ,hηκ,hcapacity,hqn,hKB,nBank,hlarge⟩ :=
    exists_native_bank_scale_cap κ q εBank Λ Bstatic K
      hκ hq hεBank hΛ.le
  let ε := δ/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε ≤ δ := by dsimp [ε]; linarith
  obtain ⟨ηT,hηT,τSel,hτSel,hτSelCap,nG34,hG34Entry⟩ :=
    hG34 ε ε Λ ε hε hε hΛ hε
  let n₀ := max nG34 (max nWeights (max nBank ((Lbank+2)*K)))
  refine ⟨q,hq,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,
    hκ,hεBank,ηT,hηT,n₀,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  have hnG34 : nG34 ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  have hnWeights : nWeights ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnBank : nBank ≤ Fintype.card V :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hsize : (Lbank+2)*K ≤ Fintype.card V :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨W,hWlo,_,hCore3,hCore4,hChildEntry⟩ :=
    hG34Entry H φ hnG34 hSeed hPhys h3 h4
  refine ⟨W,?_⟩
  intro T DT dT hT hTd hTs
  obtain ⟨D,R,hBankData,hNative⟩ := hChildEntry T DT dT hT hTd hTs
  obtain ⟨qSel,z,N,C0,Mon,Fm,hqSelPos,hqSelBound,hNDef,
    hzCore,hz3,hz4,_,hzDel,_,hBank,hgen⟩ := hBankData
  let F0 := (cover D ∪ R) ∪ T
  have hP' : P = 2 * gammaL A M Lbank := by
    simpa only [Lbank,Rc,β] using hP
  have hCap : η * ((2 * Ecell *
      (childSetting C0 Rc P qSel Ecell z).Bstar : ℕ) : ℝ) / γ ≤ 1 := by
    simpa only [S07V40.MacroSetting.Bstar, S07V43.childSetting,
      Bstatic, Lbank] using hcapacity
  have hqSelBound' : εBank * W.card / 4 ≤ qSel := by
    convert hqSelBound using 1 <;> ring
  have hQn : γ * Fintype.card V ≤ qSel :=
    hqn (Fintype.card V) W.card qSel hWlo hqSelBound'
  have hz3' : (z : ℝ) ≤ β / 2 * W.card := by
    convert hz3 using 1 <;> ring
  have hKB' : (K : ℝ) *
      (ε + (3 * Λ / 2) * (ε + 2 * ε + 2 * τSel)) ≤ η :=
    hKB ε ε ε τSel hεδ hεδ hεδ
      (hτSelCap.trans hεδ)
  have hN : (protSetting C0 Rc P qSel Ecell z F0).K
      (Zr (protSetting C0 Rc P qSel Ecell z F0) N) ≠ ⊥ →
      1 + η * (Fintype.card V : ℝ)^2 ≤ 2*N := by
    intro _
    rw [hNDef]
    exact final_bank_capacity_of_sample_size κ q η
      (Fintype.card V) W.card hκ hq hWlo hηκ (hlarge _ hnBank)
  obtain ⟨Y,x,J,hYF,hYE,hJ,hxY,hOutcome,_⟩ :=
    hActivate H F W D R C0 P qSel Ecell z N Lbank Mon Fm hP'
      F0 (subset_union_left) hBank hgen γ η ε ε ε τSel hnWeights hWlo h3 h4
      hCore3 hCore4 hzCore hz3' hz4 hzDel hsize hη.le hγ
      hQn hCap hKB' hN hNative
  exact ⟨D,R,qSel,z,N,C0,Y,x,J,
    by simpa only [Rc,β,F0,Lbank] using hBank,
    by simpa only [F0] using hYF,
    hYE,
    hJ,hxY,by simpa only [Rc,β,F0] using hOutcome⟩

#print axioms TypedTriangle.CatalogNative.native_bank_entry_one_layer

end TypedTriangle.CatalogNative
