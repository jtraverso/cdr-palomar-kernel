/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3UniformResources
public import RequestProject.TypedTriangle.G3ReferenceResourceAssembly
public import RequestProject.TypedTriangle.G3NativeResourceBasal
public import RequestProject.TypedTriangle.G3GlobalDeletionBudget
public import RequestProject.TypedTriangle.G3BasalRemainderSplit
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A sampled core is fixed before the terminal demand. The native stock,
selector and bank are then paid inside the reference window, so the dense
child reference avoids them all. This is one layer, without vortex iteration. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.CatalogNative

open BasalIncidence SelSimul S07V40 S07V42

theorem native_dense_reference_one_layer {I : Type} (F : Set (Multiset I))
    (α q C η : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q)
    (hq1 : q ≤ 1) (hC : 1 ≤ C) (hη : 0 < η)
    (hh : 6 ≤ h) :
    ∃ (d c E d' c' E' Ecell A M K P : ℕ) (κ εBank : ℝ),
      0 < κ ∧ 0 < εBank ∧
      P = 2*S07V46.gammaL A M
        (Fintype.card (Cat d (catR (α*q^h/4) d c E d' c' E'))) ∧
      ∀ ρTarget : ℝ, 0 < ρTarget →
    ∃ ηT : ℝ, 0 < ηT ∧ ∃ κX : ℝ, 0 < κX ∧
      ∃ τ : ℝ, 0 < τ ∧ τ ≤ ρTarget ∧
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
              (D₀ : Finset (Finset {x // x ∈ W})),
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
              (∃ dU : ℕ, (∀ v, SparseEdge.degIn U v ≤ dU) ∧
                ((dU+W.card:ℕ):ℝ) ≤ 4*q*Fintype.card V) ∧
              letI : DecidableEq {x // x ∈ W} := Classical.decEq _
              let J : Host {x // x ∈ W} I :=
                ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
              E₀ ⊆ edges J ∧ IsDecomposition J F E₀ D₀ ∧
              (∀ v, (SparseEdge.degIn (edges J\E₀) v:ℝ) ≤ η*W.card) := by
  let β := α*q^h/4
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨θRef,hθRef,hRefWindow⟩ :=
    dense_reference_for_four_basal_resources F C q β η h hC hq hβ hη
  obtain ⟨εRaw,γ,hεRaw,hγ,nRef,hRef⟩ := hRefWindow 1 (by norm_num)
  let γsmall := min γ 1
  have hγsmall : 0 < γsmall := lt_min hγ (by norm_num)
  have hγsmallLe : γsmall ≤ γ := min_le_left _ _
  have hγsmallOne : γsmall ≤ 1 := min_le_right _ _
  obtain ⟨d,c,E,d',c',E',Ecell,hNative⟩ :=
    native_shared_resources_uniform F α q C εRaw h hα hq hq1 hC hεRaw hh
  let Rc := catR β d c E d' c' E'
  let Lbank := Fintype.card (Cat d Rc)
  obtain ⟨A,M,K,P,hP,hAlloc⟩ :=
    S07V47.protSetting_allocation_constants.{0,0} d c E Rc Lbank
  let εcap := γsmall/8
  obtain ⟨δgeom,hδgeom,_,hGeomBudget⟩ :=
    original_geometry_vertex_budget hβ h
  let δcap := min δgeom (min (S07V37.delOf β h)
    (S07V37.delOf (β/2) h))
  have hδcap : 0 < δcap :=
    lt_min hδgeom (lt_min (S07V37.delOf_pos hβ h)
      (S07V37.delOf_pos (by positivity) h))
  let ηTcap := γsmall*q/64
  have hεcap : 0 < εcap := by dsimp [εcap]; positivity
  have hηTcap : 0 < ηTcap := by dsimp [ηTcap]; positivity
  obtain ⟨κ,εBank,ηBank,hκ,hεBank,hεBcap,hηBank,hNative'⟩ :=
    hNative P εcap δcap hεcap hδcap
  refine ⟨d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,hκ,hεBank,?_,?_⟩
  · simpa only [β,Rc,Lbank] using hP
  intro ρTarget hρTarget
  let ρcap := min (γsmall*q/64) ρTarget
  let τcap := min (γsmall*q/64) ρTarget
  have hρcap : 0 < ρcap := by dsimp [ρcap]; exact lt_min (by positivity) hρTarget
  have hτcap : 0 < τcap := by dsimp [τcap]; exact lt_min (by positivity) hρTarget
  obtain ⟨ηT,hηT,hηTbound,hNative''⟩ :=
    hNative' ρcap ηTcap hρcap hηTcap
  obtain ⟨ρ,κX,τ,hρ,hρbound,hκX,hτ,
    hτrho,hτbound,t,nG,ht,ht3,hG⟩ := hNative'' τcap hτcap
  let n₀ := max nG (max ⌈2*nRef/q⌉₊ ⌈4/(γsmall*q)⌉₊)
  have hτTarget : τ ≤ ρTarget := hτbound.trans (min_le_right _ _)
  refine ⟨ηT,hηT,κX,hκX,τ,hτ,hτTarget,t,ht,ht3,n₀,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  have hnG : nG ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnRefN : 2*nRef/q ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have hnLarge : 4/(γsmall*q) ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨W,hWlo,hWhi,hCt,hRaw,hJ3,hJ4,hTail⟩ :=
    hG H φ hnG hSeed hPhys h3 h4
  have hnRefW : nRef ≤ W.card := by
    have hval := (div_le_iff₀ hq).mp hnRefN
    exact_mod_cast (show (nRef:ℝ) ≤ W.card by nlinarith only [hval,hWlo])
  have hLargeSmall : 2 ≤ γsmall*W.card := by
    have hgq : 0 < γsmall*q := mul_pos hγsmall hq
    have hval := (div_le_iff₀ hgq).mp hnLarge
    nlinarith only [hval,hWlo,hγsmall.le,hq.le]
  have hLarge : 2 ≤ γ*W.card := by
    have hW0 : (0:ℝ) ≤ W.card := Nat.cast_nonneg _
    nlinarith only [hLargeSmall,hγsmallLe,hW0]
  refine ⟨W,hWlo,hWhi,hCt,by simpa only [β] using hJ3,
    by simpa only [β] using hJ4,?_⟩
  intro T DT dT hT hTd hTs
  obtain ⟨D,R,hD,hDT,hDd,hSupply,hRdis,hRbasal,hRd,hY0,hMode,
    C0,qSel,z,hqSel,hql,hzcap,hz,hDel,hM,hBankDis,hBankDeg,hCat⟩ :=
    hTail T DT dT hT hTd hTs
  let S := S07V47.protSetting C0 Rc P qSel Ecell z ((cover D∪R)∪T)
  let N := ⌊κ*(W.card:ℝ)^2⌋₊
  let Bank := Br S N
  let U := (((cover D∪R)∪T)∪Bank)
  have hBasal : Basal H F U :=
    native_stock_bank_basal C0 T R DT D hT hD hRbasal hDT hRdis hM hBankDis
  have hSumSmall : ρ+τ+ηT ≤ γsmall*q/8 := by
    have h1 : ρ ≤ γsmall*q/64 := hρbound.trans (min_le_left _ _)
    have h2 : τ ≤ γsmall*q/64 := hτbound.trans (min_le_left _ _)
    have h3' : ηT ≤ γsmall*q/64 := hηTbound
    nlinarith only [h1,h2,h3',hγsmall.le,hq.le]
  have hSum : ρ+τ+ηT ≤ γ*q/8 := by
    nlinarith only [hSumSmall,hγsmallLe,hq.le]
  have hBankCapSmall : εBank ≤ γsmall/4 := by
    dsimp [εcap] at hεBcap
    linarith
  have hBankCap : εBank ≤ γ/4 := by linarith only [hBankCapSmall,hγsmallLe]
  have hDdeg : ∀ v, (degIn (cover D) v:ℝ) ≤ ρ*Fintype.card V :=
    fun v => (hDd v).le
  have hRdeg : ∀ v, (degIn R v:ℝ) ≤ τ*Fintype.card V := by
    intro v
    simpa only [degIn, SelSimul.edeg] using hRd v
  have hρq : ρ ≤ q/64 := by
    have hρsmall : ρ ≤ γsmall*q/64 := hρbound.trans (min_le_left _ _)
    have hsmall := mul_le_mul_of_nonneg_right hγsmallOne hq.le
    nlinarith only [hρsmall,hsmall]
  have hDq : ∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
      (q/64)*Fintype.card V := by
    intro v
    have hs := mul_le_mul_of_nonneg_right hρq
      (Nat.cast_nonneg (Fintype.card V))
    exact (hDdeg v).trans (by simpa only [degIn,SparseEdge.degIn] using hs)
  have hDcap : ∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
      ρTarget*Fintype.card V := by
    intro v
    have hρtarget : ρ ≤ ρTarget := hρbound.trans (min_le_right _ _)
    have hs := mul_le_mul_of_nonneg_right hρtarget
      (Nat.cast_nonneg (Fintype.card V))
    exact (hDdeg v).trans (by simpa only [degIn,SparseEdge.degIn] using hs)
  have hTdeg : ∀ v, (degIn T v:ℝ) ≤ ηT*Fintype.card V := by
    intro v
    have ht : (degIn T v:ℝ) ≤ dT := by exact_mod_cast hTd v
    exact ht.trans hTs
  have hBankDegree : ∀ v, (degIn Bank v:ℝ) ≤ εBank*W.card := by
    intro v
    exact (hBankDeg v).le
  have hGlobal : 2*γsmall*q+2*q ≤ 4*q := by
    nlinarith only [hγsmallOne,hq.le]
  obtain ⟨dU,hUd,hGlobalBudget⟩ :=
    four_resource_global_deletion_budget W (cover D) R T Bank
      q γsmall (4*q) ρ τ ηT εBank hq hγsmall hWlo hWhi
      hSumSmall hBankCapSmall hDdeg hRdeg hTdeg hBankDegree
      hLargeSmall hGlobal
  obtain ⟨E₀,D₀,hE,hEDec,hAvoid,hUnion,hHole⟩ :=
    hRef H φ W (cover D) R T Bank ρ τ ηT εBank hnRefW hSeed
      hWlo hWhi hRaw hJ4 hSum hBankCap hDdeg hRdeg hTdeg
      hBankDegree hLarge hBasal
  have hBankBasal : Basal H F Bank := protected_bank_basal C0 ((cover D∪R)∪T) hM
  have hLiftBasal : Basal H F (SampledResource.lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hEDec⟩
  obtain ⟨DR,hRtail,hDtail,hSplitEq⟩ :=
    basal_remainder_split D DT R T Bank (SampledResource.lift W E₀)
      hRbasal hT hBankBasal hLiftBasal hDT hRdis hBankDis
      (by simpa only [U] using hAvoid)
  have hSplit : ∃ (Rtail : Finset (Sym2 V)) (DR : Finset (Finset V)),
      IsDecomposition H F Rtail DR ∧ Disjoint (cover D) Rtail ∧
      cover D∪Rtail = U∪SampledResource.lift W E₀ := by
    refine ⟨((R∪T)∪Bank)∪SampledResource.lift W E₀,DR,
      hRtail,hDtail,?_⟩
    simpa only [U] using hSplitEq
  have hBankWitness :
      ∃ (qSel z N : ℕ)
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
        (∀ v, (SparseEdge.degIn (Br S N) v : ℝ) ≤ εBank*W.card) := by
    obtain ⟨Mon,Fm,_⟩ := hAlloc C0
    have hW0 : (0:ℝ) ≤ W.card := Nat.cast_nonneg _
    have hzGeom : (z:ℝ) ≤ δgeom * W.card :=
      hzcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)
    have hGeom := hGeomBudget hW0 hzGeom
    have hzDel : (z:ℝ) ≤ S07V37.delOf β h * W.card :=
      hzcap.trans (mul_le_mul_of_nonneg_right
        ((min_le_right _ _).trans (min_le_left _ _)) hW0)
    have hzDelHalf : (z:ℝ) ≤ S07V37.delOf (β/2) h * W.card :=
      hzcap.trans (mul_le_mul_of_nonneg_right
        ((min_le_right _ _).trans (min_le_right _ _)) hW0)
    refine ⟨qSel,z,N,C0,Mon,Fm,hqSel,hql,rfl,?_,?_,?_,?_,?_,hDel,?_,?_,?_,?_⟩
    · simpa only [β] using hz
    · simpa only [β] using hGeom.1
    · simpa only [β] using hGeom.2
    · simpa only [β] using hzDel
    · simpa only [β] using hzDelHalf
    · simpa only [β,Rc,S,N] using hM
    · intro j
      simpa only [β,Rc,S,N] using hCat j
    · dsimp [U, Bank, N, S]
      exact subset_union_right
    · intro v
      simpa only [Bank, S, N, TypedTriangle.degIn, SparseEdge.degIn] using
        hBankDegree v
  refine ⟨D,R,U,E₀,D₀,hD,hDT,hRdis,hRbasal,hDq,hDcap,hRd,
    hSupply,hMode,hBankWitness,?_,hAvoid,hUnion,hSplit,
    ⟨dU,by simpa only [U, TypedTriangle.degIn, SparseEdge.degIn] using hUd,
      hGlobalBudget⟩,hE,hEDec,hHole⟩
  · dsimp [U]
    exact subset_union_left

#print axioms native_dense_reference_one_layer

end TypedTriangle.CatalogNative
