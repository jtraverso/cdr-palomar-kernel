module
public import RequestProject.TypedTriangle.PaschRoutingFanPayload
public import RequestProject.TypedTriangle.PaschRetainedPathData
public import RequestProject.TypedTriangle.PaschAmbientWeightedWindowPaths
public import RequestProject.TypedTriangle.PaschEmbeddingIncidence
public import RequestProject.TypedTriangle.PaschFiniteFamilyIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelEmbed SelSubdiv S07V24 S07V25
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {α V A : Type} [Fintype α] [Fintype V] [Fintype A] [DecidableEq α] [DecidableEq V] [DecidableEq A]

/-- Payment keeps the ambient/window ratio visible. Its density parameter
is independent of q; higher-new-block contributions stay constant. -/
def ambientWeightedRoutePayment (a : ℝ) (m L nAmbient nWindow : ℕ) : ℝ :=
  ((nAmbient:ℝ)/nWindow)*(((m+1:ℕ):ℝ)*(L:ℝ)^3)/(a/(2:ℝ)^(m+3)) +
    (9*L*((m+1).choose 2)+(m+1).choose 3+(m+1).choose 4:ℕ)

/-- The actual greedy routing, with each retained path chosen against the
fixed previous universe and all earlier paths. Geometry, forbidden edges,
window containment and the telescoping Pasch bound hold for the same data. -/
theorem exists_ambient_dense_weighted_routing
    (ι : V↪A) (H : SimpleGraph V) [DecidableRel H.Adj] (v : V)
    (φ : α → V) (src tgt : Sym2 α → α) (hφ : Function.Injective φ)
    (Q : Finset (Sym2 α)) (hEnds : ∀ e ∈ Q, s(src e,tgt e)=e)
    (hNe : ∀ e ∈ Q, src e ≠ tgt e)
    (d : ℕ) (hDegree : ∀ x, (Q.filter (fun e   =>   x ∈ e)).card  ≤  d)
    (m : ℕ) (hm : 0  <  m) (hOdd : Odd (m+1))
    (W Z0 : Finset V) (hφZ : ∀ x, φ x ∉ Z0)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hOrder : 2  ≤  q*Fintype.card V)
    (hWindow : (W.card:ℝ)  ≤  2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4  ≤  (W.card:ℝ))
    (hPaths : ∀ e ∈ Q, a*(Fintype.card V:ℝ)^m*q^m/4  ≤ 
      (pathsIn H m (φ (src e)) (φ (tgt e)) W).card)
    (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ)
    (hB : ∀ z, B.degree z  ≤  b)
    (hb : (b:ℝ)  ≤  Vortex.windowRouteRate a q m*Fintype.card V)
    (hBudget : ((Z0.card+Fintype.card α+m*Q.card:ℕ):ℝ)  ≤ 
      Vortex.windowRouteRate a q m*Fintype.card V)
    (R0 : Finset (Finset A)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    ∃ t int, RouteOK H φ src tgt (m+1) Z0 Q t int ∧
      (∀ e ∈ Q, ∀ j, 1 ≤ j → j ≤ 2*t e → int e j ∈ W) ∧
      (∀ e ∈ Q, ∀ j, j < 2*t e+1 →
        ¬B.Adj (pv φ src tgt t int e j) (pv φ src tgt t int e (j+1))) ∧
      (count (R0∪mapConfiguration ι (routingFanUniverse v φ src tgt Q t int)):ℝ)  ≤ 
        count R0+(Q.card:ℝ)*ambientWeightedRoutePayment a m (L0+max 2 d) (Fintype.card A) W.card := by
  let pay := ambientWeightedRoutePayment a m (L0+max 2 d) (Fintype.card A) W.card
  have key : ∀ Q' : Finset (Sym2 α), Q'⊆Q → ∃ t int,
      RouteOK H φ src tgt (m+1) Z0 Q' t int ∧
      (∀ e ∈ Q', ∀ j, 1 ≤ j → j ≤ 2*t e → int e j ∈ W) ∧
      (∀ e ∈ Q', ∀ j, j < 2*t e+1 →
        ¬B.Adj (pv φ src tgt t int e j) (pv φ src tgt t int e (j+1))) ∧
      (count (R0∪mapConfiguration ι (routingFanUniverse v φ src tgt Q' t int)):ℝ)  ≤  count R0+(Q'.card:ℝ)*pay := by
    intro Q'
    induction Q' using Finset.induction_on with
    | empty   =>  
      intro _
      refine ⟨fun _  =>  0,fun e _  =>  φ (src e),?_,by simp,by simp,?_⟩
      · exact ⟨by simp,by simp,by simp,by simp,by simp⟩
      · simp only [routingFanUniverse,biUnion_empty,union_empty,card_empty,Nat.cast_zero,
          zero_mul,add_zero,le_refl,mapConfiguration,map_empty]
    | insert e Q' he ih   =>  
      intro hSub
      have hQ' : Q'⊆Q := (subset_insert e Q').trans hSub
      have heQ := hSub (mem_insert_self e Q')
      obtain ⟨t,int,hOK,hW,hAvoid,hCount⟩ := ih hQ'
      let Z := forbidden φ Z0 Q' t int (φ (src e)) (φ (tgt e))
      have hZ : (Z.card:ℝ)  ≤  Vortex.windowRouteRate a q m*Fintype.card V := by
        have hCard : Z.card  ≤  Z0.card+Fintype.card α+m*Q.card := by
          have hh := forbidden_card_le (φ := φ) (Z0 := Z0) (int := int) hOK.len (φ (src e)) (φ (tgt e))
          have hQQ := card_le_card hQ'
          simpa only [Nat.add_sub_cancel] using hh.trans
            (Nat.add_le_add_left (Nat.mul_le_mul_left m hQQ) _)
        exact (Nat.cast_le.mpr hCard).trans hBudget
      have hPart : PairCodegreeBound (routingFanUniverse v φ src tgt Q' t int) (max 2 d) :=
        routingFanUniverse_pairCodegree hφ (fun f hf  =>  hEnds f (hQ' hf))
          (fun f hf  =>  hNe f (hQ' hf)) hOK d
          (fun x  =>  (card_le_card (filter_subset_filter _ hQ')).trans (hDegree x)) v
      have hPartA := pairCodegreeBound_mapConfiguration ι _ _ hPart
      let R := R0∪mapConfiguration ι (routingFanUniverse v φ src tgt Q' t int)
      have hR : PairCodegreeBound R (L0+max 2 d) := hR0.union hPartA
      obtain ⟨w,hw,hCost⟩ := exists_low_cost_ambient_relative_dense_window_path ι H W a q m v
        (φ (src e)) (φ (tgt e)) ha hq hm hOrder hWindow hWindowLower (hPaths e heQ)
        Z B b hZ hB hb R (L0+max 2 d) hR
      have hPathsW : w ∈ pathsIn H m (φ (src e)) (φ (tgt e)) W := (valid_window_path_data hw).1
      have hLength : w.length=m+1 := SimpleGraph.mem_finsetWalkLength_iff.mp
        (mem_filter.mp (mem_filter.mp hPathsW).1).1
      have hPath : w.IsPath := (mem_filter.mp (mem_filter.mp hPathsW).1).2
      obtain ⟨t0,ht0⟩ := hOdd
      have hLength0 : w.length=2*t0+1 := hLength.trans ht0
      have hm0 : 2*t0=m := by omega
      have hAvoidZ := (valid_window_path_data hw).2.1
      have hAvoidB := (valid_window_path_data hw).2.2
      have hInternal := (mem_filter.mp hPathsW).2
      have hEndsZ : φ (src e) ∉ Z ∧ φ (tgt e) ∉ Z := by
        constructor
        · simp only [Z,forbidden,mem_union,mem_erase,mem_biUnion,mem_image,not_or]
          refine ⟨⟨hφZ _,by tauto⟩,?_⟩
          rintro ⟨f,hf,j,hj,hjEq⟩
          rw [mem_Icc] at hj
          exact hOK.ne f hf j hj.1 hj.2 _ hjEq
        · simp only [Z,forbidden,mem_union,mem_erase,mem_biUnion,mem_image,not_or]
          refine ⟨⟨hφZ _,by tauto⟩,?_⟩
          rintro ⟨f,hf,j,hj,hjEq⟩
          rw [mem_Icc] at hj
          exact hOK.ne f hf j hj.1 hj.2 _ hjEq
      have hSupport : ∀ z∈w.support, z∉Z := by
        intro z hz
        have hLenPath : w∈pathsLen H (m+1) (φ (src e)) (φ (tgt e)) := (mem_filter.mp hPathsW).1
        rcases support_of_pathsLen hLenPath hz with rfl|rfl|hz
        · exact hEndsZ.1
        · exact hEndsZ.2
        · obtain ⟨j,rfl⟩ := (mem_intlSet _ _ _).mp hz
          exact hAvoidZ j
      let t' := Function.update t e t0
      let int' := Function.update int e (fun j  =>  w.getVert j)
      have hOK' : RouteOK H φ src tgt (m+1) Z0 (insert e Q') t' int' :=
        route_step_of_prescribed_walk he hOK w hPath t0 hLength0 (le_of_eq hLength) hSupport
      have hOldt : ∀ f∈Q', t' f=t f := fun f hf  =>  
        Function.update_of_ne (fun h : f = e => he (h ▸ hf)) _ _
      have hOldi : ∀ f∈Q', int' f=int f := fun f hf  =>  
        Function.update_of_ne (fun h : f = e => he (h ▸ hf)) _ _
      refine ⟨t',int',hOK',?_,?_,?_⟩
      · intro f hf j hj hj'
        rcases mem_insert.mp hf with hfe | hf
        · subst f
          simp only [int',Function.update_self]
          have hJe : t' e=t0 := Function.update_self ..
          rw [hJe] at hj'
          have hjm : j - 1  <  m := by omega
          have hh := hInternal ((mem_intlSet m w (intl m w ⟨j-1,hjm⟩)).mpr ⟨_,rfl⟩)
          simpa only [intl,Nat.sub_add_cancel hj] using hh
        · rw [hOldt f hf] at hj'; rw [hOldi f hf]
          exact hW f hf j hj hj'
      · intro f hf j hj
        rcases mem_insert.mp hf with hfe | hf
        · subst f
          have hJe : t' e=t0 := Function.update_self ..
          rw [hJe] at hj
          have hj0 : j  <  2*t0+1 := hj
          dsimp only [t',int']
          rw [updated_route_pv_eq_getVert w t0 hLength0 j (by omega),
            updated_route_pv_eq_getVert w t0 hLength0 (j+1) (by omega)]
          exact hAvoidB j (by omega)
        · rw [hOldt f hf] at hj
          rw [pv_congr φ src tgt (hOldt f hf) (hOldi f hf),
            pv_congr φ src tgt (hOldt f hf) (hOldi f hf)]
          exact hAvoid f hf j hj
      · have hUpdate := routingFanUniverse_update v Q' e he t int w t0 m hLength0 hm0
        let fan : Fin (m+1)→Finset A := fun k  => 
          {ι v,ι (w.getVert k.val),ι (w.getVert (k.val+1))}
        have hMappedFan : mapConfiguration ι (walkFanTriangles v m w)=univ.image fan := by
          unfold mapConfiguration walkFanTriangles
          rw [map_eq_image,image_image]
          apply image_congr
          intro k _
          change ({v,w.getVert k.val,w.getVert (k.val+1)}:Finset V).map ι=fan k
          simp only [map_insert,map_singleton,fan]
        have hInc := finite_family_count_increment fan R (L0+max 2 d) hR
        have hIncReal : (count (univ.image fan∪R):ℝ)  ≤  (count R:ℝ)+pay := by
          have hh : (count (univ.image fan∪R):ℝ)  ≤  (count R:ℝ)+
              ((∑k:Fin (m+1),rootedCount (insert (fan k) R) (fan k)):ℝ)+
              ((9*(L0+max 2 d)*((m+1).choose 2)+(m+1).choose 3+(m+1).choose 4:ℕ):ℝ) := by
            simpa only [Fintype.card_fin] using (show
              (count (univ.image fan∪R):ℝ)  ≤  (count R:ℝ)+
                ((∑k:Fin (m+1),rootedCount (insert (fan k) R) (fan k)):ℝ)+
                ((9*(L0+max 2 d)*((Fintype.card (Fin (m+1))).choose 2)+
                  (Fintype.card (Fin (m+1))).choose 3+(Fintype.card (Fin (m+1))).choose 4:ℕ):ℝ) from by
              norm_cast
              simpa only [Nat.add_assoc] using hInc)
          dsimp only [pay,ambientWeightedRoutePayment]
          change (count (univ.image fan∪R):ℝ)  ≤  (count R:ℝ)+_
          dsimp only [fan] at hh
          linarith only [hh,hCost]
        have hEq : R0∪mapConfiguration ι (routingFanUniverse v φ src tgt (insert e Q') t' int') =
            univ.image fan∪R := by
          rw [hUpdate]
          have hMapUnion : mapConfiguration ι (walkFanTriangles v m w∪
              routingFanUniverse v φ src tgt Q' t int)=
              mapConfiguration ι (walkFanTriangles v m w)∪
                mapConfiguration ι (routingFanUniverse v φ src tgt Q' t int) :=
            Finset.map_union _ _
          rw [hMapUnion]
          change R0∪(mapConfiguration ι (walkFanTriangles v m w)∪
            mapConfiguration ι (routingFanUniverse v φ src tgt Q' t int))=univ.image fan∪R
          rw [hMappedFan]
          dsimp only [R]
          ac_rfl
        rw [hEq,card_insert_of_notMem he,Nat.cast_add,Nat.cast_one]
        dsimp only [R] at hIncReal
        nlinarith only [hIncReal,hCount]
  exact key Q subset_rfl

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.exists_ambient_dense_weighted_routing
