module
public import RequestProject.TypedTriangle.PaschConcreteLayerCore
public import RequestProject.TypedTriangle.G3ResourceUnionBudget
public import RequestProject.TypedTriangle.VortexActualBankBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.ConcreteLayer
open CatalogNative BasalIncidence AmbientBank

/-- Lift the chosen reference blocks themselves, not a later basal witness. -/
theorem sampled_reference_decomposition_literal {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (W : Finset X)
    (E : Finset (Sym2 {x // x∈W})) (D : Finset (Finset {x // x∈W}))
    (hD : IsDecomposition (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x∈W} I) F E D) :
    IsDecomposition H F (SampledResource.lift W E) (mapConfiguration (SampledResource.vertexEmb W) D) := by
  have hh := decomposition_lift _ H F (SampledResource.vertexEmb W)
    (fun _ _ ha => ha) (fun _ => rfl) hD
  have hEdges : liftEdges (SampledResource.vertexEmb W) E=SampledResource.lift W E := by
    simp only [liftEdges,SampledResource.lift,map_eq_image] <;> rfl
  rwa [hEdges] at hh

/-- The reference is built around the same bank and the three given resource
families. Its total protected decomposition is their literal union. The
coarse reserve budget precedes the later packing degree and moment budgets. -/
theorem same_bank_reference_with_literal_reserve {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (W Wcore : Finset X)
    (D DR DT Don : Finset (Finset X)) (R T Bank : Finset (Sym2 X))
    (hD : IsDecomposition H F (cover D) D) (hR : IsDecomposition H F R DR)
    (hT : IsDecomposition H F T DT) (hBank : IsDecomposition H F Bank Don)
    (hDT : Disjoint (cover D) T) (hRDT : Disjoint R (cover D∪T))
    (hBDis : Disjoint Bank ((cover D∪R)∪T))
    (a b αRef ρFuture ηRef εRef γRef q εBank ρ τ ηT εReserve : ℝ) (h nRef : ℕ)
    (hReference : Vortex.NakedReferenceAt F a b αRef ρFuture ηRef εRef γRef h nRef)
    (hq : 0 < q) (hγ : 0 < γRef) (hεBank : 0 ≤ εBank)
    (hεCap : εBank ≤ γRef/4) (hεQuarter : εBank ≤ 1/4)
    (hSum : ρ+τ+ηT ≤ γRef*q/8)
    (hLo : q*Fintype.card X/2 ≤ W.card) (hHi : (W.card:ℝ) ≤ 2*q*Fintype.card X)
    (hCore : Wcore ⊆ W) (hLarge : 2 ≤ γRef*W.card) (hReserve : 4*q ≤ εReserve)
    (hDcap : ∀x,(degIn (cover D) x:ℝ) ≤ ρ*Fintype.card X)
    (hRcap : ∀x,(degIn R x:ℝ) ≤ τ*Fintype.card X)
    (hTcap : ∀x,(degIn T x:ℝ) ≤ ηT*Fintype.card X)
    (hBankCap : ∀x,(degIn Bank x:ℝ) ≤ εBank*Wcore.card)
    (hDsmall : ∀x,(SparseEdge.degIn (cover D) x:ℝ) ≤ q/64*Fintype.card X)
    (hRsmall : ∀x,(SparseEdge.degIn R x:ℝ) ≤ q/64*Fintype.card X)
    (hTsmall : ∀x,(SparseEdge.degIn T x:ℝ) ≤ q/64*Fintype.card X) :
    letI : DecidableEq {x // x∈W} := Classical.decEq _
    let JW : Host {x // x∈W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    ∀ (μ : Finset {x // x∈W} → ℝ) (U : Finset {x // x∈W}),
    nRef ≤ W.card → CommonNbrCond JW F αRef → HingeCond JW F αRef h →
    (∀Q,IsAllowed JW F Q → a/W.card ≤ μ Q ∧ μ Q ≤ b/W.card) →
    (∀e∈edges JW,|bdry JW F μ e-1| ≤ εRef) → (U.card:ℝ) ≤ ρFuture*W.card →
    Disjoint (SampledResource.lift W (edges JW∩triEdges U)) (((cover D∪R)∪T)∪Bank) →
    ∃ (E0 : Finset (Sym2 {x // x∈W})) (D0 : Finset (Finset {x // x∈W})) (dTotal : ℕ),
    let Eref := SampledResource.lift W E0
    let Dtotal := ((((D∪DR)∪DT)∪Don)∪mapConfiguration (SampledResource.vertexEmb W) D0)
    edges JW∩triEdges U ⊆ E0 ∧ E0 ⊆ edges JW ∧ IsDecomposition JW F E0 D0 ∧
    Disjoint Eref (((cover D∪R)∪T)∪Bank) ∧
    IsDecomposition H F ((((cover D∪R)∪T)∪Bank)∪Eref) Dtotal ∧
    (∀x,degIn ((((cover D∪R)∪T)∪Bank)∪Eref) x ≤ dTotal) ∧
    (dTotal:ℝ) ≤ εReserve*Fintype.card X ∧
    (∀x,(degIn (edges JW\E0) x:ℝ) ≤ ηRef*W.card) ∧
    (subHost JW E0).G.comap (Subtype.val : {x // x∈U} → {x // x∈W})=
      JW.G.comap (Subtype.val : {x // x∈U} → {x // x∈W}) := by
  letI : DecidableEq {x // x∈W} := Classical.decEq _
  dsimp only
  intro μ U hn h3 h4 hμ hLoad hU hFuture
  let Actual := ((cover D∪R)∪T)∪Bank
  have hBankWindow : ∀x,(degIn Bank x:ℝ) ≤ εBank*W.card := by
    intro x
    exact (hBankCap x).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hCore)) hεBank)
  obtain ⟨dB,hBdeg,hBcap⟩ := four_resource_reference_window W (cover D) R T Bank q γRef ρ τ ηT εBank
    hq hγ hLo hSum hεCap hDcap hRcap hTcap hBankWindow hLarge
  have hDR : Disjoint (cover D) R := (hRDT.mono_right subset_union_left).symm
  have hDRT : Disjoint (cover D∪R) T := disjoint_union_left.mpr ⟨hDT,hRDT.mono_right subset_union_right⟩
  have hActual : IsDecomposition H F Actual (((D∪DR)∪DT)∪Don) :=
    ((hD.union hR hDR).union hT hDRT).union hBank hBDis.symm
  obtain ⟨E0,D0,hUin,hE,hDec,hAvoid,_,hHole,hGraph⟩ :=
    Vortex.naked_reference_at_preserving_future_core F a b αRef ρFuture ηRef εRef γRef h nRef
      hReference H W μ U Actual dB hn h3 h4 hμ hLoad hU hFuture ⟨_,hActual⟩ hBdeg hBcap
  have hRef := sampled_reference_decomposition_literal H F W E0 D0 hDec
  have hBankQuarter : ∀x,(SparseEdge.degIn Bank x:ℝ) ≤ (Wcore.card:ℝ)/4 := by
    intro x
    change (TypedTriangle.degIn Bank x:ℝ) ≤ (Wcore.card:ℝ)/4
    have hh := (hBankCap x).trans (mul_le_mul_of_nonneg_right hεQuarter (Nat.cast_nonneg Wcore.card))
    linarith only [hh]
  obtain ⟨dU,hActualDeg,hTotalCap⟩ := Vortex.actual_bank_union_budget D R T Bank W Wcore q εReserve
    hq hReserve hCore hHi hDsmall hRsmall hTsmall hBankQuarter
  have hTotal : IsDecomposition H F (Actual∪SampledResource.lift W E0)
      (((D∪DR)∪DT)∪Don∪mapConfiguration (SampledResource.vertexEmb W) D0) :=
    hActual.union hRef hAvoid.symm
  refine ⟨E0,D0,dU+W.card,hUin,hE,hDec,hAvoid,hTotal,?_,hTotalCap,hHole,hGraph⟩
  intro x
  exact SampledResource.full_reserved_degree_le H W Actual E0 dU hActualDeg hE x

end TypedTriangle.Pasch.ConcreteLayer
#print axioms TypedTriangle.Pasch.ConcreteLayer.sampled_reference_decomposition_literal
#print axioms TypedTriangle.Pasch.ConcreteLayer.same_bank_reference_with_literal_reserve
