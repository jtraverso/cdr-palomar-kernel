/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3NativeDenseReference
public import RequestProject.TypedTriangle.G4SampledReferenceComplement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Choose the sampled core before the terminal demand. For each admissible
demand, the native four-resource construction gives an exact basal deletion
whose complement has H1--H4 on the same host. This is one layer only. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open BasalIncidence S07V40 S07V42

theorem native_exact_complement_one_layer {I : Type} (F : Set (Multiset I))
    (α C η : ℝ) (h : ℕ) (hα : 0 < α) (hC : 1 ≤ C)
    (hη : 0 < η) (hh : 6 ≤ h) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ∃ (d c E d' c' E' Ecell A M K P : ℕ) (κ εBank : ℝ),
      0 < κ ∧ 0 < εBank ∧
      P = 2*S07V46.gammaL A M
        (Fintype.card (Cat d (catR (α*q^h/4) d c E d' c' E'))) ∧
      ∀ ρTarget : ℝ, 0 < ρTarget →
      ∃ ηT : ℝ, 0 < ηT ∧
      ∃ κX : ℝ, 0 < κX ∧ ∃ τ : ℝ, 0 < τ ∧ τ ≤ ρTarget ∧
        ∃ t : ℕ, Odd t ∧ 3 ≤ t ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        ∃ W : Finset V, q*Fintype.card V/2 ≤ W.card ∧
          (W.card:ℝ) < 2*q*Fintype.card V ∧
          S07V45.CorePathContract H.G H.lab F W t ∧
          SparseEdge.CommonNbrCond
            (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F (α*q^h/4) ∧
          SparseEdge.HingeCond
            (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F (α*q^h/4) h ∧
          ∀ (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
            IsDecomposition H F T DT →
            (∀ v, SparseEdge.degIn T v ≤ dT) →
            (dT:ℝ) ≤ ηT*Fintype.card V →
            ∃ (D : Finset (Finset V)) (R U : Finset (Sym2 V))
              (E₀ : Finset (Sym2 {x // x ∈ W}))
              (D₀ : Finset (Finset {x // x ∈ W}))
              (ψ : Finset V → ℝ),
              IsDecomposition H F (cover D) D ∧
              Disjoint (cover D) T ∧ Disjoint R (cover D∪T) ∧
              Basal H F R ∧
              (∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
                (q/64)*Fintype.card V) ∧
              (∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
                ρTarget*Fintype.card V) ∧
              (∀ v, (SelSimul.edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              (∀ u v, H.G.Adj u v →
                κX*Fintype.card V ≤ (good H F D u v).card) ∧
              (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
                ∃ Ps Y : Finset (Sym2 V), R∪L = Ps∪Y ∧
                  Disjoint Ps Y ∧ Basal H F Ps ∧
                  (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                  (∀ v, (SelSimul.edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧
                  IsPhysical H F Y) ∧
              (∃ (qSel z N : ℕ)
                (C0 : CoreCompression H.G H.lab F W d c E),
                let Rc := catR (α*q^h/4) d c E d' c' E'
                ∃ (Mon : ∀ Z : Finset V,
                    S07V44.CatalogGen C0 Rc Z →
                      S07V44.PhysicalMonitors C0 Rc Z A M K)
                  (Fm : S07V46.FullMonitor C0 Rc A M K),
                let S := S07V47.protSetting C0 Rc P qSel Ecell z
                  ((cover D∪R)∪T)
                0 < qSel ∧
                εBank/4 * W.card ≤ qSel ∧
                N = ⌊κ*(W.card:ℝ)^2⌋₊ ∧
                (z:ℝ) ≤ coreDelta (α*q^h/4) h * W.card ∧
                (z:ℝ) ≤ (α*q^h/4) * W.card / 2 ∧
                (z:ℝ) * 2 ^ Nat.choose (h+1) 2 ≤
                  (α*q^h/4) / 2 * W.card ∧
                (z:ℝ) ≤ S07V37.delOf (α*q^h/4) h * W.card ∧
                (z:ℝ) ≤ S07V37.delOf ((α*q^h/4)/2) h * W.card ∧
                (∀ Z : Finset V, Z.card ≤ z →
                  Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
                MacroBank S (Fintype.card (Cat d Rc)) N ∧
                (∀ j, S07V44.CatalogGen C0 Rc (Zstrat S N j)) ∧
                Br S N ⊆ U ∧
                (∀ v, (SparseEdge.degIn (Br S N) v : ℝ) ≤ εBank*W.card)) ∧
              ((cover D∪R)∪T) ⊆ U ∧
              Disjoint (SampledResource.lift W E₀) U ∧
              Basal H F (U∪SampledResource.lift W E₀) ∧
              (∃ (Rtail : Finset (Sym2 V)) (DR : Finset (Finset V)),
                IsDecomposition H F Rtail DR ∧
                Disjoint (cover D) Rtail ∧
                cover D∪Rtail = U∪SampledResource.lift W E₀) ∧
              letI : DecidableEq {x // x ∈ W} := Classical.decEq _
              let J : Host {x // x ∈ W} I :=
                ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
              E₀ ⊆ edges J ∧ IsDecomposition J F E₀ D₀ ∧
              (∀ v, (SparseEdge.degIn (edges J\E₀) v:ℝ) ≤ η*W.card) ∧
              let B := U∪SampledResource.lift W E₀
              IsDiffuseSeed (subHost H (edges H\B)) F (2*C) ψ ∧
              IsPhysical (subHost H (edges H\B)) F
                (edges (subHost H (edges H\B))) ∧
              CommonNbrCond (subHost H (edges H\B)) F (α/2) ∧
              HingeCond (subHost H (edges H\B)) F
                (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨ε,hε,nExact,hExact⟩ :=
    exact_complement_after_sampled_reference F C α h hC hα hh
  let q := min (1/2) (ε/8)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [min_le_left (1/2:ℝ) (ε/8)]
  have hqε : 4*q ≤ ε := by
    have hqbound : q ≤ ε/8 := min_le_right _ _
    linarith
  obtain ⟨d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,hκ,hεBank,hP,hNative⟩ :=
    native_dense_reference_one_layer F α q C η h hα hq hq1 hC hη hh
  refine ⟨q,hq,hq1,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,hκ,hεBank,hP,?_⟩
  intro ρTarget hρTarget
  obtain ⟨ηT,hηT,κX,hκX,τ,hτ,hτTarget,t,ht,ht3,nG,hG⟩ :=
    hNative ρTarget hρTarget
  refine ⟨ηT,hηT,κX,hκX,τ,hτ,hτTarget,t,ht,ht3,max nG nExact,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  obtain ⟨W,hWlo,hWhi,hCt,h3Core,h4Core,hNative⟩ :=
    hG H φ ((le_max_left _ _).trans hn) hSeed hPhys h3 h4
  refine ⟨W,hWlo,hWhi,hCt,h3Core,h4Core,?_⟩
  intro T DT dT hT hTd hTs
  obtain ⟨D,R,U,E₀,D₀,hD,hDT,hRdis,hRbasal,hDq,hDcap,hRd,hSupply,hMode,hBank,hSub,hAvoid,hBasal,hSplit,
    ⟨dU,hUd,hBudget⟩,hE,hEDec,hHole⟩ := hNative T DT dT hT hTd hTs
  have hnExact : nExact ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  have hSmall : ((dU+W.card:ℕ):ℝ) ≤ ε*Fintype.card V := by
    have hnNonneg : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hScale := mul_le_mul_of_nonneg_right hqε hnNonneg
    exact hBudget.trans (by nlinarith only [hScale])
  obtain ⟨ψ,hSeedJ,hPhysJ,h3J,h4J⟩ :=
    hExact H φ W U E₀ dU hnExact hSeed hPhys h3 h4 hBasal hE hUd hSmall
  exact ⟨D,R,U,E₀,D₀,ψ,hD,hDT,hRdis,hRbasal,hDq,hDcap,hRd,hSupply,hMode,hBank,hSub,hAvoid,hBasal,hSplit,
    hE,hEDec,hHole,hSeedJ,hPhysJ,h3J,h4J⟩

#print axioms native_exact_complement_one_layer

end TypedTriangle.CatalogNative
