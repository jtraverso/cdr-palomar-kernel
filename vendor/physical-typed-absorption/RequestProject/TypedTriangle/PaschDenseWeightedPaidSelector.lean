module
public import RequestProject.TypedTriangle.PaschPaidCoreFamily
public import RequestProject.TypedTriangle.PaschDenseWeightedSelectorFamily
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelSimul SelBridge SelTyped S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type} [Fintype V] [Fintype Ambient]

/-- Routing, simultaneous selection, and its common empty-mode H3 payment
are all constructed. Both the common payment and every mode retain their
literal decompositions. The stock supply is not an input. -/
theorem dense_weighted_paid_core_selector
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (ι : V ↪ Ambient) (a qRate : ℝ) (ha : 0 < a) (hqRate : 0 < qRate)
    (m : ℕ) (hm : 0 < m) (hOdd : Odd (m+1)) (W : Finset V)
    (hOrder : 2 ≤ qRate*Fintype.card V) (hWindow : (W.card:ℝ) ≤ 2*qRate*Fintype.card V)
    (hWindowLower : qRate*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : ∀ v x y, OrigAdm G lab F v x y →
      a*(Fintype.card V:ℝ)^m*qRate^m/4 ≤ (pathsIn (link G lab F v) m x y W).card)
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
    (Z : Finset V) (hZ : ∀ v∈Z, ∀ w∈Z, ¬X.Adj v w) (hZW : Disjoint Z W)
    (hLink : ∀ v∈Z, ∀ u, X.Adj v u → ∃ y, (link G lab F v).Adj u y)
    {A q r b : ℕ} (hA : 200*m+8 ≤ A) (hq : 0 < q)
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hBud : r+b+A*r*Fintype.card V/q+(A+1)*r+10*r+m*(200*r) ≤
      ⌊Vortex.windowRouteRate a qRate m*Fintype.card V⌋₊)
    (hρ : ((b+61*r+60*q+60:ℕ):ℝ) ≤ Vortex.windowRouteRate a qRate m*Fintype.card V)
    (αCore : ℝ) (hαCore : 0 < αCore)
    (hCore : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F αCore)
    (p : ℕ) (hp : 0 < p)
    (hPay : ((Fintype.card V*(61*r+60*q) : ℕ) : ℝ)/(p : ℝ)+
      2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) ≤
        (αCore/2)*Fintype.card (Survivors Z))
    (R0 : Finset (Finset Ambient)) (L0 : ℕ) (hCodeg : PairCodegreeBound R0 L0) :
    ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)) (DPaid : Finset (Finset V)),
      SimulFamily G lab F X B0 Z (rootAdm G lab F X) A q σ ∧
      (∀ v∈Z, (σ v).W⊆W) ∧
      Disjoint C (fuelU Z σ∪X.edgeFinset∪B0.edgeFinset) ∧
      Disjoint (fuelU Z σ∪C) (X.edgeFinset∪B0.edgeFinset) ∧
      IsDecomposition (⟨G,lab⟩ : Host V I) F (fuelU Z σ∪C) DPaid ∧
      Basal (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ ∅∪C) ∧
      (∀ e∈C, ∀ v∈e, v∉Z) ∧
      (∀ v, edeg (fuelU Z σ∪C) v ≤
        max (A*r) (60*r+61*q)+2*(61*r+60*q+p)) ∧
      (count (R0∪mapConfiguration ι (selectorUniverse Z σ∪DPaid)) : ℝ) ≤ count R0+
        ((r*Z.card : ℕ) : ℝ)*weightedCoreRoutePay a m (Fintype.card Ambient) W.card (L0+120)+
        2*((61*r+60*q : ℕ) : ℝ)*Fintype.card Ambient*((L0+61 : ℕ) : ℝ)^3/αCore ∧
      ∀ T : Finset (Sym2 V), T⊆X.edgeFinset → IsPhysical (⟨G,lab⟩ : Host V I) F T →
        (fuelU Z σ∪C)∪T=packEdges (packing X Z σ T)∪(SelSimul.residual X Z σ T∪C) ∧
        Disjoint (packEdges (packing X Z σ T)) (SelSimul.residual X Z σ T∪C) ∧
        IsDecomposition (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ T))
          ((packing X Z σ T).image (fun x => selectorTriangle x.1 x.2)) ∧
        (packing X Z σ T).image (fun x => selectorTriangle x.1 x.2) ⊆ selectorUniverse Z σ ∧
        (∀ e∈SelSimul.residual X Z σ T∪C, ∀ v∈e, v∉Z) ∧
        (∀ v, edeg (SelSimul.residual X Z σ T∪C) v ≤ 3*(61*r+60*q)+2*p) ∧
        IsPhysical (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ T∪C) := by
  letI : DecidableEq V := Classical.decEq _
  letI : DecidableEq Ambient := Classical.decEq _
  letI : DecidableEq (Survivors Z) := Classical.decEq _
  obtain ⟨σ,hFam,hAux,hRouteStat⟩ := dense_weighted_selector_family
    ι a qRate ha hqRate m hm hOdd W hOrder hWindow hWindowLower hPaths
    X B0 Z hZ hZW hLink hA hq hX hB hBud hρ R0 L0 hCodeg
  let Rfixed := R0∪mapConfiguration ι (selectorUniverse Z σ)
  have hUniverse : PairCodegreeBound (selectorUniverse Z σ) 60 :=
    fun x y hxy => selectorUniverse_pair_degree_le hFam hZ x y hxy
  have hFixed : PairCodegreeBound Rfixed (L0+60) :=
    hCodeg.union (pairCodegreeBound_mapConfiguration ι _ 60 hUniverse)
  have hAdm0 : ∀ v∈Z, rootAdm G lab F X v ∅ := fun v _ => rootAdm_empty G lab F X v
  have hAdmEmpty : ∀ v∈Z, rootAdm G lab F X v (demand X ∅ v) := by
    simpa [demand] using hAdm0
  have hKd := (hFam.layer_partition hZ hX (empty_subset _) hAdmEmpty).2.2.2.2.2.2
  have hKCard := CorePaid.card_le_order_mul_degree (SelSimul.residual X Z σ ∅) hKd
  have hPay' : ((SelSimul.residual X Z σ ∅).card : ℝ)/(p : ℝ)+
      2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) ≤
        (αCore/2)*Fintype.card (Survivors Z) := by
    have hc : ((SelSimul.residual X Z σ ∅).card : ℝ) ≤ (Fintype.card V*(61*r+60*q) : ℕ) :=
      Nat.cast_le.mpr hKCard
    have hdiv := div_le_div_of_nonneg_right hc (Nat.cast_nonneg p)
    linarith only [hdiv,hPay]
  obtain ⟨C,DPaid,hDPaid,hPaidStat,hCavoid,hAvoid,hBas,hEmpty,hCinside,hCdeg,hModes⟩ :=
    paid_core_family_with_ambient_pasch ι Rfixed (L0+60) hFixed hFam
      subset_union_right hαCore hCore hp hZ hX hB hAdm0 hPay'
  have hCubic : L0+60+1=L0+61 := by omega
  have hStat : (count (R0∪mapConfiguration ι (selectorUniverse Z σ∪DPaid)) : ℝ) ≤ count R0+
      ((r*Z.card : ℕ) : ℝ)*weightedCoreRoutePay a m (Fintype.card Ambient) W.card (L0+120)+
      2*((61*r+60*q : ℕ) : ℝ)*Fintype.card Ambient*((L0+61 : ℕ) : ℝ)^3/αCore := by
    have hUniverseEq : R0∪mapConfiguration ι (selectorUniverse Z σ∪DPaid)=
        Rfixed∪mapConfiguration ι DPaid := by
      unfold mapConfiguration
      rw [map_union]
      exact (union_assoc _ _ _).symm
    rw [hUniverseEq]
    let E := CorePayment.pullEdges Z (SelSimul.residual X Z σ ∅)
    have hEdeg : ∀ v, edeg E v ≤ 61*r+60*q := by
      intro v
      simpa only [CorePayment.edeg_eq_classical] using
        (CorePayment.degree_pull_le Z _ v).trans (hKd v.1)
    have hEcard := CorePaid.card_le_order_mul_degree E hEdeg
    have hn : 0 < Fintype.card (Survivors Z) := by
      by_contra hh
      have he : Fintype.card (Survivors Z)=0 := by omega
      have hpos : (0 : ℝ) < ((Fintype.card V*(61*r+60*q) : ℕ) : ℝ)/(p : ℝ)+
          2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) := by positivity
      simp only [he,Nat.cast_zero,mul_zero] at hPay
      linarith only [hPay,hpos]
    have hnR : (0 : ℝ)<Fintype.card (Survivors Z) := Nat.cast_pos.mpr hn
    have hRatio : (E.card : ℝ)/Fintype.card (Survivors Z) ≤ ((61*r+60*q : ℕ) : ℝ) := by
      apply (div_le_iff₀ hnR).mpr
      have hc : (E.card : ℝ) ≤ (Fintype.card (Survivors Z)*(61*r+60*q) : ℕ) := Nat.cast_le.mpr hEcard
      push_cast at hc ⊢
      nlinarith only [hc]
    have hScale : 0 ≤ 2*(Fintype.card Ambient : ℝ)*((L0+61 : ℕ) : ℝ)^3/αCore := by positivity
    have hCost := mul_le_mul_of_nonneg_right hRatio hScale
    have hCost' : 2*(E.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card (Survivors Z))*
        ((L0+61 : ℕ) : ℝ)^3/αCore ≤
        2*((61*r+60*q : ℕ) : ℝ)*Fintype.card Ambient*((L0+61 : ℕ) : ℝ)^3/αCore := by
      convert hCost using 1 <;> ring
    rw [hCubic] at hPaidStat
    linarith only [hPaidStat,hRouteStat,hCost']
  refine ⟨σ,C,DPaid,hFam,hAux,hCavoid,hAvoid,hDPaid,hEmpty,hCinside,?_,hStat,?_⟩
  · intro v
    exact (edeg_union_le _ _ v).trans
      (Nat.add_le_add (hFam.fuelU_edeg_le hZ hX v) (hCdeg v))
  · intro T hT hPhys
    have hAdm : ∀ v∈Z, rootAdm G lab F X v (demand X T v) :=
      fun v _ => SelectorEntry.rootAdm_of_physical X hT hPhys v
    obtain ⟨hEq,hDis,hBasal,hInside,hDeg,hPhysical⟩ := hModes T hT hAdm
    obtain ⟨_,_,_,hPacking,hTyped,_,_⟩ := hFam.layer_partition hZ hX hT hAdm
    have hDec := rooted_packing_decomposition (H := (⟨G,lab⟩ : Host V I)) (F := F)
      (packing X Z σ T) hPacking (fun x hx => by
        obtain ⟨_,u,v,he,_,hAllowed⟩ := hTyped x hx
        exact ⟨u,v,he,hAllowed⟩)
    exact ⟨hEq,hDis,hDec,selector_modes_subset_universe hFam T hAdm,hInside,hDeg,hPhysical hPhys⟩
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.dense_weighted_paid_core_selector
