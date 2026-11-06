module
public import RequestProject.TypedTriangle.PaschRetainedPathData
public import RequestProject.S07V49.EdgeRoutes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24 S07V25 S07V45 S07V49
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type} [Fintype V] [DecidableEq V]

/-- Sparse payment preserves an actual dense family, not only existence of
one route. Missing spokes and missing path edges are both charged before
transporting the same finite family injectively to the residual link. -/
theorem residual_window_path_count
    (G C : SimpleGraph V) [DecidableRel C.Adj] (lab : V→I) (F : Set (Multiset I))
    (W : Finset V) (a q : ℝ) (m : ℕ) (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V) (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hPaths : ∀v x y, OrigAdm G lab F v x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn (TypedTriangle.ComponentRows.link G lab F v) m x y W).card)
    (dC : ℕ) (hC : ∀v, C.degree v ≤ dC)
    (hCap : (dC:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V) :
    ∀v x y, OrigAdm (G\C) lab F v x y →
      (a/2)*(Fintype.card V:ℝ)^m*q^m/4 ≤ 
        (pathsIn (TypedTriangle.ComponentRows.link (G\C) lab F v) m x y W).card := by
  intro v x y hxy
  obtain ⟨hOriginal,hx,hy⟩ := resid_adm_orig hxy
  let NC := C.neighborFinset v
  have hNC : (NC.card:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V := by
    exact (Nat.cast_le.mpr (by simpa only [NC,SimpleGraph.card_neighborFinset_eq_degree] using hC v)).trans hCap
  let Fam := validWindowPaths (TypedTriangle.ComponentRows.link G lab F v) m x y W NC C
  have hFam : a*(Fintype.card V:ℝ)^m*q^m/8 ≤ Fam.card :=
    dense_validWindowPaths _ W a q m x y ha hq hm hOrder hWindow (hPaths v x y hOriginal)
      NC C dC hNC hC hCap
  have survive : ∀p∈Fam, ∃p' : (TypedTriangle.ComponentRows.link (G\C) lab F v).Walk x y,
      p'.length=p.length ∧ p'.support=p.support ∧ ∀j, p'.getVert j=p.getVert j := by
    intro p hp
    have hpW := (valid_window_path_data hp).1
    have hpLen := (mem_filter.mp hpW).1
    have hLength : p.length=m+1 := SimpleGraph.mem_finsetWalkLength_iff.mp (mem_filter.mp hpLen).1
    have hAV := (valid_window_path_data hp).2.1
    have hAE := (valid_window_path_data hp).2.2
    have hSpokes : ∀z∈p.support, ¬C.Adj v z := by
      intro z hz
      rcases support_of_pathsLen hpLen hz with rfl|rfl|hz
      · exact hx
      · exact hy
      · obtain ⟨j,rfl⟩ := (mem_intlSet _ _ _).mp hz
        intro hc
        apply hAV ⟨j.val,by omega⟩
        change C.Adj v (p.getVert (j.val+1)) at hc
        simpa only [NC,SimpleGraph.mem_neighborFinset,intl] using hc
    exact residual_walk p hSpokes (fun j hj => hAE j (hLength ▸ hj))
  let f : Fam → (TypedTriangle.ComponentRows.link (G\C) lab F v).Walk x y :=
    fun p  =>  Classical.choose (survive p.val p.property)
  have hData : ∀p:Fam, (f p).length=p.val.length ∧ (f p).support=p.val.support ∧
      ∀j, (f p).getVert j=p.val.getVert j := fun p => Classical.choose_spec (survive p.val p.property)
  have hfInj : Function.Injective f := by
    intro p r heq
    apply Subtype.ext
    apply SimpleGraph.Walk.ext_support
    exact (hData p).2.1.symm.trans ((congrArg SimpleGraph.Walk.support heq).trans (hData r).2.1)
  have hImage : univ.image f ⊆ pathsIn (TypedTriangle.ComponentRows.link (G\C) lab F v) m x y W := by
    intro r hr
    obtain ⟨p,_,rfl⟩ := mem_image.mp hr
    have hpW := (valid_window_path_data p.property).1
    have hpLen := (mem_filter.mp hpW).1
    have hLength : p.val.length=m+1 := SimpleGraph.mem_finsetWalkLength_iff.mp (mem_filter.mp hpLen).1
    have hPath : p.val.IsPath := (mem_filter.mp hpLen).2
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · exact SimpleGraph.mem_finsetWalkLength_iff.mpr ((hData p).1.trans hLength)
    · rw [SimpleGraph.Walk.isPath_def,(hData p).2.1]
      exact hPath.support_nodup
    · intro z hz
      obtain ⟨j,rfl⟩ := (mem_intlSet _ _ _).mp hz
      have hEq : intl m (f p) j=intl m p.val j := (hData p).2.2 _
      rw [hEq]
      exact (mem_filter.mp hpW).2 ((mem_intlSet _ _ _).mpr ⟨j,rfl⟩)
  have hCard : Fam.card ≤ (pathsIn (TypedTriangle.ComponentRows.link (G\C) lab F v) m x y W).card := by
    calc
      _ = (univ.image f).card := by rw [card_image_of_injective _ hfInj,card_univ,Fintype.card_coe]
      _  ≤  _ := card_le_card hImage
  have hCardReal : (Fam.card:ℝ) ≤ (pathsIn (TypedTriangle.ComponentRows.link (G\C) lab F v) m x y W).card :=
    Nat.cast_le.mpr hCard
  calc
    _ = a*(Fintype.card V:ℝ)^m*q^m/8 := by ring
    _  ≤  _ := hFam.trans hCardReal

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.residual_window_path_count
