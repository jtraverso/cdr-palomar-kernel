module
public import RequestProject.TypedTriangle.PaschWeightedSlotGadgetFresh
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- A fixed saturated set is excluded geometrically, while the potential
is charged only on the bounded local support U. -/
theorem exists_low_cost_slot_gadget_avoiding_vertices {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {T : Finset V} (hT : IsAllowed H F T) (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hUc : U.card ≤ Ub) (hTU : T ⊆ U)
    (Z : Finset V) (hUZ : Disjoint U Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Ub:ℝ)+Z.card+3+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ)+Z.card+1+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (ap : Sym2 V → V),
      (∀ e ∈ triEdges T, ap e ∉ U ∧ ap e ∉ e ∧ IsAllowed H F (slotTri e (ap e))) ∧
      (∀ e ∈ triEdges T, ∀ e' ∈ triEdges T, ap e = ap e' → e = e') ∧
      Basal H F Y ∧ Basal H F (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint Y ((triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))).card ≤ U.card+(2*h-2) ∧
      Y.card ≤ (2*h-2).choose 2 ∧
      (supportIncrementCost R U (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))):ℝ) ≤
        gadgetPotentialCost α h Ub L ∧
      Disjoint (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))) Z := by
  let Big := U ∪ Z
  have hBigNat : Big.card ≤ Ub+Z.card := (card_union_le _ _).trans (Nat.add_le_add_right hUc _)
  have hBig : (Big.card:ℝ) ≤ (Ub:ℝ)+Z.card := by exact_mod_cast hBigNat
  obtain ⟨Y,ap,hAp,hInj,hY,hYW,hDis,hB,hFresh,hCard,hYe,hPay,hInter,hSupport⟩ :=
    exists_low_cost_slot_gadget_fresh_support hα hH3 hH4 hT R L hL U Ub hUc hTU Big
      (hTU.trans subset_union_left) B d hdeg (by linarith only [hBig,hwin1])
      ((mul_le_mul_of_nonneg_right (by linarith only [hBig]) (by positivity)).trans hwin2)
  refine ⟨Y,ap,?_,hInj,hY,hYW,hDis,hB,hFresh.anti subset_union_left,
    (card_union_le _ _).trans (Nat.add_le_add_left hSupport _),hYe,hPay,?_⟩
  · intro e he
    obtain ⟨hNot,hEdge,hAllow⟩ := hAp e he
    exact ⟨fun hu => hNot (mem_union_left _ hu),hEdge,hAllow⟩
  · apply disjoint_left.mpr
    intro z hz hzZ
    exact disjoint_left.mp hUZ (hTU (hInter z (mem_union_right _ hzZ) hz)) hzZ

theorem exists_low_cost_composite_hinge_avoiding_vertices {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b) (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hUc : U.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ U)
    (Z : Finset V) (hUZ : Disjoint U Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Ub:ℝ)+Z.card+2+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ)+Z.card+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ J, IsHinge H F u v a b J ∧ Disjoint J B ∧ s(a,b) ∉ J ∧
      (∀ z ∈ U, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧
      (support J).card ≤ 2*h-3 ∧
      (supportIncrementCost R U (support J):ℝ) ≤ compositePotentialCost α h Ub L ∧
      Disjoint (support J) Z := by
  let Big := U ∪ Z
  have hBigNat : Big.card ≤ Ub+Z.card := (card_union_le _ _).trans (Nat.add_le_add_right hUc _)
  have hBig : (Big.card:ℝ) ≤ (Ub:ℝ)+Z.card := by exact_mod_cast hBigNat
  obtain ⟨J,hJ,hB,hNo,hFresh,hCard,hPay⟩ := exists_low_cost_robust_composite_hinge
    hα hH3 hH4 hab hTa hTb R L hL U Ub hUc hRoots Big B d hdeg
      (by linarith only [hBig,hwin1])
      ((mul_le_mul_of_nonneg_right (by linarith only [hBig]) (by positivity)).trans hwin2)
  refine ⟨J,hJ,hB,hNo,(fun z hz => hFresh z (mem_union_left _ hz)),hCard,hPay,?_⟩
  apply disjoint_left.mpr
  intro z hz hzZ
  exact disjoint_left.mp hUZ (hRoots (hFresh z (mem_union_right _ hzZ) hz)) hzZ

#print axioms exists_low_cost_slot_gadget_avoiding_vertices
#print axioms exists_low_cost_composite_hinge_avoiding_vertices
end TypedTriangle.Pasch
