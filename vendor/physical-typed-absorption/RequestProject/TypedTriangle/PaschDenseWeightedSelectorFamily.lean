module
public import RequestProject.TypedTriangle.PaschWeightedCoreRoot
public import RequestProject.TypedTriangle.PaschWeightedCoreSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelSimul SelBridge SelTyped S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type} [Fintype V] [Fintype Ambient] [DecidableEq V] [DecidableEq Ambient]

/-- The weighted scheduled family is constructed from the retained dense
paths. This endpoint has no weighted availability provider as an input. -/
theorem dense_weighted_selector_family
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
    (R0 : Finset (Finset Ambient)) (L0 : ℕ) (hCodeg : PairCodegreeBound R0 L0) :
    ∃ σ : V → LocalSel V,
      SimulFamily G lab F X B0 Z (rootAdm G lab F X) A q σ ∧
      (∀ v∈Z, (σ v).W⊆W) ∧
      (count (R0∪mapConfiguration ι (selectorUniverse Z σ)):ℝ) ≤
        count R0+((r*Z.card:ℕ):ℝ)*
          weightedCoreRoutePay a m (Fintype.card Ambient) W.card (L0+120) := by
  let pay := weightedCorePayShift (weightedCoreRoutePay a m (Fintype.card Ambient) W.card) 60
  have hPay : ∀ L, 0 ≤ pay L := fun L => weightedCoreRoutePay_nonneg a ha m _ _ (L+60)
  have hAvail : ∀ v∈Z, WeightedCoreAvail G lab F v (X.neighborFinset v)
      (rootAdm G lab F X v) A (r+b+A*r*Fintype.card V/q) (b+61*r+60*q) W ι pay := by
    intro v hv
    exact weighted_coreAvail_root ι a qRate ha hqRate m hm hOdd W hOrder hWindow hWindowLower
      hPaths X v (hLink v hv) hA (hX v) hBud hρ
  obtain ⟨σ,hFamily,hAux,hCount⟩ := weighted_schedule_core G lab F X B0 Z W hZ hZW
    (rootAdm G lab F X) ι pay hPay hAvail hq hX hB le_rfl le_rfl R0 L0 hCodeg
  refine ⟨σ,hFamily,hAux,?_⟩
  have hArg : L0+60+60=L0+120 := by omega
  simpa only [pay,weightedCorePayShift,hArg] using hCount

/-- The real all-roots frontend has ports in W: the fork reduction certifies
that every X-edge meets W. Thus every fuel edge meets W, including possible
port--port bases. No additional safety field is postulated in availability. -/
theorem weighted_selector_fuel_meets_window
    {G : SimpleGraph V} {lab : V→I} {F : Set (Multiset I)}
    {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj]
    (W : Finset V) (Adm : V→Finset V→Prop) (A q : ℕ) (σ : V→LocalSel V)
    (hFamily : SimulFamily G lab F X B0 (univ\W) Adm A q σ)
    (hXW : ∀ x y, X.Adj x y → x∈W ∨ y∈W) :
    ∀ e∈fuelU (univ\W) σ, ∃ v∈e, v∈W := by
  have hZ : ∀ x∈univ\W, ∀ y∈univ\W, ¬X.Adj x y := by
    intro x hx y hy hxy
    rcases hXW x y hxy with hxW | hyW
    · exact (mem_sdiff.mp hx).2 hxW
    · exact (mem_sdiff.mp hy).2 hyW
  have hOutside := hFamily.outside_Z hZ
  have hComp : ∀ x, x ∉ univ\W → x∈W := by
    intro x hx
    simpa only [mem_sdiff,mem_univ,true_and,not_not] using hx
  intro e he
  obtain ⟨r,hr,he⟩ := mem_biUnion.mp he
  change e∈(σ r).P∪SelBridge.radial r (σ r).W at he
  rcases mem_union.mp he with he | he
  · induction e using Sym2.ind with
    | h u v => exact ⟨u,by simp,hComp u ((hOutside r hr).2 _ he u (by simp))⟩
  · obtain ⟨w,hw,rfl⟩ := mem_image.mp he
    exact ⟨w,by simp,hComp w ((hOutside r hr).1 w hw)⟩

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.dense_weighted_selector_family
#print axioms TypedTriangle.Pasch.weighted_selector_fuel_meets_window
