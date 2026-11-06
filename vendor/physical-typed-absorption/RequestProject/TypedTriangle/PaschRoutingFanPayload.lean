module
public import RequestProject.TypedTriangle.PaschPartialRoutingCodegree
public import RequestProject.TypedTriangle.PaschWeightedRoutingStep
public import RequestProject.TypedTriangle.PaschWalkFanIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelEmbed SelSubdiv
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {α V : Type*} [DecidableEq α] [DecidableEq V]

def routingFanUniverse (v : V) (φ : α → V) (src tgt : Sym2 α → α)
    (Q : Finset (Sym2 α)) (t : Sym2 α → ℕ) (int : Sym2 α → ℕ → V) : Finset (Finset V) :=
  Q.biUnion (fun e => (range (2*t e+1)).image (fun j =>
    {v,pv φ src tgt t int e j,pv φ src tgt t int e (j+1)}))

theorem routingFanUniverse_eq_subdivision {H : SimpleGraph V} {Q : Finset (Sym2 α)}
    (v : V) (D : OddSubdivision H Q) :
    routingFanUniverse v D.φ D.src D.tgt Q D.t D.int =
      D.pathEdges.image (selectorTriangle v) := by
  simp only [routingFanUniverse,OddSubdivision.pathEdges,biUnion_image,image_image,
    Function.comp_def,OddSubdivision.pe,OddSubdivision.pathV,selectorTriangle,
    Sym2.toFinset_mk_eq]

theorem routingFanUniverse_pairCodegree {H : SimpleGraph V}
    {φ : α → V} {src tgt : Sym2 α → α} {ℓ : ℕ} {Z0 : Finset V}
    {Q : Finset (Sym2 α)} {t : Sym2 α → ℕ} {int : Sym2 α → ℕ → V}
    (hφ : Function.Injective φ) (hEnds : ∀ e ∈ Q, s(src e,tgt e) = e)
    (hNe : ∀ e ∈ Q, src e ≠ tgt e) (hOK : RouteOK H φ src tgt ℓ Z0 Q t int)
    (d : ℕ) (hDegree : ∀ x, (Q.filter (fun e => x ∈ e)).card ≤ d) (v : V) :
    PairCodegreeBound (routingFanUniverse v φ src tgt Q t int) (max 2 d) := by
  let D : OddSubdivision H Q := ⟨φ,src,tgt,t,int,hφ,hEnds,hNe,hOK.inj,hOK.ne,hOK.adj⟩
  rw [show routingFanUniverse v φ src tgt Q t int = D.pathEdges.image (selectorTriangle v)
    from routingFanUniverse_eq_subdivision v D]
  exact partial_routing_pairCodegree hφ hEnds hNe hOK d hDegree v

theorem walkFanTriangles_eq_range {G : SimpleGraph V} {x y : V} (v : V) (m : ℕ)
    (p : G.Walk x y) : walkFanTriangles v m p =
      (range (m+1)).image (fun k => {v,p.getVert k,p.getVert (k+1)}) := by
  ext T
  simp only [walkFanTriangles,mem_image,mem_univ,true_and,mem_range]
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k.val,k.isLt,hk⟩
  · rintro ⟨k,hk,hT⟩; exact ⟨⟨k,hk⟩,hT⟩

theorem updated_route_pv_eq_getVert {H : SimpleGraph V}
    {φ : α → V} {src tgt : Sym2 α → α} {t : Sym2 α → ℕ}
    {int : Sym2 α → ℕ → V} {e : Sym2 α}
    (w : H.Walk (φ (src e)) (φ (tgt e))) (t0 : ℕ) (hLength : w.length = 2*t0+1)
    (j : ℕ) (hj : j ≤ 2*t0+1) :
    pv φ src tgt (Function.update t e t0)
      (Function.update int e (fun j => w.getVert j)) e j = w.getVert j := by
  simp only [pv,Function.update_self]
  split_ifs with h0 h1
  · subst h0; exact w.getVert_zero.symm
  · subst h1; rw [← hLength]; exact w.getVert_length.symm
  · rfl

/-- The newly stored route changes the literal triangle universe by exactly
its own fan. The previous paths and their chosen coordinates are preserved. -/
theorem routingFanUniverse_update {H : SimpleGraph V}
    (v : V) {φ : α → V} {src tgt : Sym2 α → α}
    (Q : Finset (Sym2 α)) (e : Sym2 α) (he : e ∉ Q)
    (t : Sym2 α → ℕ) (int : Sym2 α → ℕ → V)
    (w : H.Walk (φ (src e)) (φ (tgt e))) (t0 m : ℕ)
    (hLength : w.length = 2*t0+1) (hm : 2*t0=m) :
    routingFanUniverse v φ src tgt (insert e Q)
      (Function.update t e t0) (Function.update int e (fun j => w.getVert j)) =
      walkFanTriangles v m w ∪ routingFanUniverse v φ src tgt Q t int := by
  unfold routingFanUniverse
  rw [biUnion_insert]
  congr 1
  · rw [Function.update_self,← hm,walkFanTriangles_eq_range]
    apply image_congr
    intro j hj
    dsimp only
    have hj' := mem_range.mp hj
    rw [updated_route_pv_eq_getVert w t0 hLength j (by omega),
      updated_route_pv_eq_getVert w t0 hLength (j+1) (by omega)]
  · apply biUnion_congr rfl
    intro f hf
    have hfe : f ≠ e := fun h => he (h ▸ hf)
    simp only [Function.update_of_ne hfe]
    apply image_congr
    intro j hj
    dsimp only
    rw [SelEmbed.pv_congr φ src tgt (Function.update_of_ne hfe _ _)
        (Function.update_of_ne hfe _ _),
      SelEmbed.pv_congr φ src tgt (Function.update_of_ne hfe _ _)
        (Function.update_of_ne hfe _ _)]

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.routingFanUniverse_eq_subdivision
#print axioms TypedTriangle.Pasch.routingFanUniverse_pairCodegree
#print axioms TypedTriangle.Pasch.walkFanTriangles_eq_range
#print axioms TypedTriangle.Pasch.updated_route_pv_eq_getVert
#print axioms TypedTriangle.Pasch.routingFanUniverse_update
