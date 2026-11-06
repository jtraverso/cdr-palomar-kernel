module
public import RequestProject.TypedTriangle.PaschWeightedCoreProducers
public import RequestProject.TypedTriangle.VortexWindowRouteRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelBridge SelTyped SelSubdiv SelRoute ParitySel SelBalanced SelEmbed SelSimul S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45 S07V26
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type} [Fintype V] [Fintype Ambient] [DecidableEq V] [DecidableEq Ambient]

theorem WeightedCoreAvail.adm_congr
    {G : SimpleGraph V} {lab : V→I} {F : Set (Multiset I)} {v : V}
    {U W : Finset V} {Adm Adm' : Finset V→Prop} {A ζ ρ : ℕ}
    {ι : V↪Ambient} {pay : ℕ→ℝ}
    (h : WeightedCoreAvail G lab F v U Adm A ζ ρ W ι pay)
    (hAA : ∀S⊆U, Adm' S→Adm S) : WeightedCoreAvail G lab F v U Adm' A ζ ρ W ι pay := by
  intro R0 L0 hR0 Z0 Bf hZ hB
  obtain ⟨σ,hσ,hW,hCount⟩ := h R0 L0 hR0 Z0 Bf hZ hB
  exact ⟨σ,hσ.adm_weaken hAA,hW,hCount⟩

theorem weighted_coreAvail_empty (G : SimpleGraph V) (lab : V→I)
    (F : Set (Multiset I)) (v : V) (Adm : Finset V→Prop)
    (A ζ ρ : ℕ) (W : Finset V) (ι : V↪Ambient) (pay : ℕ→ℝ) :
    WeightedCoreAvail G lab F v ∅ Adm A ζ ρ W ι pay := by
  intro R0 L0 hR0 Z0 Bf hZ hB
  refine ⟨⟨∅,∅,fun _ => ∅⟩,SelSimul.valid_empty G lab F v Adm Z0 Bf A,by simp,?_⟩
  simp only [weightedCoreUniverse,image_empty,mapConfiguration,map_empty,union_empty,
    card_empty,Nat.cast_zero,zero_mul,add_zero,le_refl]

/-- H3/H4-produced dense paths discharge the weighted per-component
availability contract; no weighted selector provider is assumed. -/
theorem weighted_coreAvail_component
    {G : SimpleGraph V} {lab : V→I} {F : Set (Multiset I)}
    (ι : V↪Ambient) (a q : ℝ) (ha : 0  <  a) (hq : 0  <  q)
    (m : ℕ) (hm : 0  <  m) (hOdd : Odd (m+1)) (W : Finset V)
    (hOrder : 2 ≤ q*Fintype.card V) (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : ∀v x y, OrigAdm G lab F v x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn (link G lab F v) m x y W).card)
    (v : V) (C : Finset V) (hC : C∈activeComps G lab F v)
    (U : Finset V) (hUC : U⊆C) {A ζ ρ : ℕ}
    (hA : 200*m+8 ≤ A)
    (hBud : ζ+10*U.card+m*(200*U.card) ≤ ⌊Vortex.windowRouteRate a q m*Fintype.card V⌋₊)
    (hρ : (ρ:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V) :
    WeightedCoreAvail G lab F v U (compAdmC G lab F v C) A ζ ρ W ι
      (weightedCoreRoutePay a m (Fintype.card Ambient) W.card) := by
  let ε := Vortex.windowRouteRate a q m
  have hε : 0   <   ε := Vortex.windowRouteRate_pos m ha hq
  have ht3 : 3 ≤ m+1 := by obtain ⟨k,hk⟩ := hOdd; omega
  have hroute : RouteProp G lab F (m+1) ε W :=
    Vortex.routeProp_of_window_path_count G lab F W a q m ha hq hm hOrder hWindow hPaths
  have hBudReal : ((ζ+10*U.card+m*(200*U.card):ℕ):ℝ) ≤ ε*Fintype.card V :=
    (Nat.cast_le.mpr hBud).trans (Nat.floor_le (by positivity))
  set M := ⌊ε * Fintype.card V⌋₊ with hM
  set K := C.filter (fun z => z ∈ W ∪ U) with hK
  have hKC : K ⊆ C := filter_subset _ _
  have hUK : U ⊆ K := fun u hu => mem_filter.2 ⟨hUC hu, mem_union_right _ hu⟩
  have hKW : K ⊆ W ∪ U := fun z hz => (mem_filter.1 hz).2
  have hCWK : C ∩ W ⊆ K := fun z hz =>
    mem_filter.2 ⟨(mem_inter.1 hz).1, mem_union_left _ (mem_inter.1 hz).2⟩
  have hwing : ∀ a ∈ K, G.Adj v a := fun a ha => activeComp_wing hC (hKC ha)
  have h4 : (m) * (4 * U.card) ≤ (m) * (200 * U.card) :=
    Nat.mul_le_mul_left _ (by omega)
  by_cases hb : IsBip G lab F (v, C)
  · -- BAL
    set Xs := K.filter (fun z => colG G lab F v z = true) with hXs
    set Ys := K.filter (fun z => colG G lab F v z = false) with hYs
    have hconv : ∀ S ⊆ U, compAdmC G lab F v C S → (S ∩ Xs).card = (S ∩ Ys).card := by
      intro S hS h
      unfold compAdmC at h
      rw [if_pos hb] at h
      have e1 : S ∩ Xs = S.filter (fun x => colG G lab F v x = true) := by
        ext z; simp only [hXs, mem_inter, mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUK (hS h.1), h.2⟩⟩
      have e2 : S ∩ Ys = S.filter (fun x => colG G lab F v x = false) := by
        ext z; simp only [hYs, mem_inter, mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUK (hS h.1), h.2⟩⟩
      rw [e1, e2]; exact h
    rcases U.eq_empty_or_nonempty with hU | hU
    · subst hU
      exact weighted_coreAvail_empty G lab F v _ A ζ ρ W ι _
    have hside : ∀ c : Bool, ζ + 10 * U.card ≤ (K.filter (fun z => colG G lab F v z = c)).card := by
      intro c
      have h1 := route_side_large ht3 hε hroute hC hb c
      have h2 : (C ∩ W).filter (fun z => colG G lab F v z = c) ⊆
          K.filter (fun z => colG G lab F v z = c) := filter_subset_filter _ hCWK
      have := card_le_card h2
      omega
    refine WeightedCoreAvail.adm_congr (weighted_coreAvail_bal G lab F v U K Xs Ys W
      hm hOdd hU hA (filter_subset _ _) (filter_subset _ _) ?_ ?_
      (hside true) (hside false) hKW hwing ι a q ha hq hOrder hWindow hWindowLower
      ?_ hBudReal hρ) hconv
    · rw [Finset.disjoint_left]
      intro z hz hz'
      rw [mem_filter] at hz hz'
      rw [hz.2] at hz'; exact Bool.noConfusion hz'.2
    · intro u hu
      cases h : colG G lab F v u
      · exact mem_union_right _ (mem_filter.2 ⟨hUK hu, h⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hUK hu, h⟩)
    · intro a b hab
      rcases hab with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · rw [mem_filter] at ha hb'
        apply hPaths v _ _
        refine activeComp_admPair hC (hKC ha.1) (hKC hb'.1) ?_ ?_
        · intro h; rw [h, hb'.2] at ha; exact Bool.noConfusion ha.2
        · intro _; rw [ha.2, hb'.2]; decide
      · rw [mem_filter] at ha hb'
        apply hPaths v _ _
        refine activeComp_admPair hC (hKC ha.1) (hKC hb'.1) ?_ ?_
        · intro h; rw [h, hb'.2] at ha; exact Bool.noConfusion ha.2
        · intro _; rw [ha.2, hb'.2]; decide
  · -- PAR
    have hconv : ∀ S ⊆ U, compAdmC G lab F v C S → Even S.card := by
      intro S _ h
      unfold compAdmC at h
      rwa [if_neg hb] at h
    have hKc : ζ + 3 * U.card ≤ K.card := by
      have h1 := route_pool_large ht3 hε hroute hC
      have := card_le_card hCWK
      omega
    have hParNat : ζ+3*U.card+m*(4*U.card) ≤ ζ+10*U.card+m*(200*U.card) := by
      have hh := Nat.mul_le_mul_left m (by omega : 4*U.card ≤ 200*U.card)
      omega
    have hParReal : ((ζ+3*U.card+m*(4*U.card):ℕ):ℝ) ≤ ε*Fintype.card V :=
      (Nat.cast_le.mpr hParNat).trans hBudReal
    refine WeightedCoreAvail.adm_congr (weighted_coreAvail_par G lab F v U K W
      hm hOdd (by omega) hUK hKc hKW hwing ι a q ha hq hOrder hWindow hWindowLower
      ?_ hParReal hρ) hconv
    intro x y hxy
    obtain ⟨hx,hy,hne⟩ := hxy
    exact hPaths v x y (activeComp_admPair hC (hKC hx) (hKC hy) hne (fun h => absurd h hb))

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.WeightedCoreAvail.adm_congr
#print axioms TypedTriangle.Pasch.weighted_coreAvail_empty
#print axioms TypedTriangle.Pasch.weighted_coreAvail_component
