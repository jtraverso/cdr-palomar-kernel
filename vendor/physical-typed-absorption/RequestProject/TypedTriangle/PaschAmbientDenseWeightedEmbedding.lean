module
public import RequestProject.TypedTriangle.PaschAmbientDenseWeightedRouting
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelEmbed SelSubdiv S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {α V A : Type} [Fintype α] [Fintype V] [Fintype A] [DecidableEq α] [DecidableEq V] [DecidableEq A]

/-- The genuine prescribed-port embedding with weighted retained routes.
No auxiliary placement is repeated after the routing choice. -/
theorem ambient_dense_weighted_embedding
    (ι : V↪A) (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (Allowed : V→V→Prop)
    (Q : Finset (Sym2 α)) (hQ : ∀ e∈Q, ¬e.IsDiag)
    (Side : α→V→Prop)
    (hside : ∀ e∈Q, ∀ x y, s(x,y)=e → ∀ a b, a≠b → Side x a → Side y b → Allowed a b)
    (Ports : Finset α) (ψ : α→V) (hψ : Set.InjOn ψ Ports)
    (hψS : ∀x∈Ports, Side x (ψ x))
    (Z0 : Finset V) (hψZ : ∀x∈Ports, ψ x∉Z0)
    (Cand : α→Finset V) (hCS : ∀x∉Ports, ∀a∈Cand x, Side x a)
    (hCand : ∀x∉Ports, Z0.card+Fintype.card α ≤ (Cand x).card)
    (d : ℕ) (hDegree : ∀x, (Q.filter (fun e => x∈e)).card ≤ d)
    (m : ℕ) (hm : 0 < m) (hOdd : Odd (m+1))
    (W : Finset V) (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : ∀x y, Allowed x y → a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn H m x y W).card)
    (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ) (hB : ∀z, B.degree z ≤ b)
    (hb : (b:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (hBudget : ((Z0.card+Fintype.card α+m*Q.card:ℕ):ℝ) ≤ 
      Vortex.windowRouteRate a q m*Fintype.card V)
    (R0 : Finset (Finset A)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    ∃D : OddSubdivision H Q,
      (∀x∈Ports, D.φ x=ψ x) ∧ (∀x∉Ports, D.φ x∈Cand x) ∧
      (∀x, D.φ x∉Z0) ∧ (∀e∈Q, 2*D.t e+1 ≤ m+1) ∧
      (∀y∈D.internals, y∉Z0) ∧ D.internals⊆W ∧
      (∀f∈D.pathEdges, ∃x y, f=s(x,y) ∧ ¬B.Adj x y) ∧
      (count (R0∪mapConfiguration ι (D.pathEdges.image (selectorTriangle v))):ℝ) ≤ 
        count R0+(Q.card:ℝ)*ambientWeightedRoutePayment a m (L0+max 2 d) (Fintype.card A) W.card := by
  obtain ⟨φ, hφ, hP, hC, hZ⟩ := exists_placement Ports ψ hψ Z0 hψZ Cand hCand
  have hSide : ∀ x, Side x (φ x) := by
    intro x
    by_cases hx : x ∈ Ports
    · rw [hP x hx]; exact hψS x hx
    · exact hCS x hx _ (hC x hx)
  let src : Sym2 α → α := fun e  =>  e.out.1
  let tgt : Sym2 α → α := fun e  =>  e.out.2
  have hends : ∀ e, s(src e, tgt e) = e := fun e  =>  by
    change Quot.mk _ e.out = e
    exact e.out_eq
  have hne : ∀ e ∈ Q, src e ≠ tgt e := by
    intro e he h
    apply hQ e he
    rw [← hends e, h]
    exact Sym2.mk_isDiag_iff.mpr rfl
  have hall : ∀ e ∈ Q, Allowed (φ (src e)) (φ (tgt e)) := fun e he  => 
    hside e he _ _ (hends e) _ _ (fun h  =>  hne e he (hφ h)) (hSide _) (hSide _)
  obtain ⟨t,int,hOK,hW,hAvoid,hCount⟩ := exists_ambient_dense_weighted_routing ι H v φ src tgt hφ
    Q (fun e _ => hends e) hne d hDegree m hm hOdd W Z0 hZ a q ha hq hOrder
    hWindow hWindowLower (fun e he => hPaths _ _ (hall e he)) B b hB hb hBudget R0 L0 hR0
  let D : OddSubdivision H Q := ⟨φ,src,tgt,t,int,hφ,fun e _ => hends e,hne,hOK.inj,hOK.ne,hOK.adj⟩
  refine ⟨D,hP,hC,hZ,hOK.len,?_,?_,?_,?_⟩
  · intro y hy
    change y ∈ Q.biUnion (fun e => (Icc 1 (2*t e)).image (int e)) at hy
    obtain ⟨e,he,hy⟩ := mem_biUnion.mp hy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    exact hOK.avoid e he j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  · intro y hy
    change y ∈ Q.biUnion (fun e => (Icc 1 (2*t e)).image (int e)) at hy
    obtain ⟨e,he,hy⟩ := mem_biUnion.mp hy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    exact hW e he j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  · intro f hf
    change f ∈ Q.biUnion (fun e => (range (2*t e+1)).image (fun j =>
      s(pv φ src tgt t int e j,pv φ src tgt t int e (j+1)))) at hf
    obtain ⟨e,he,hf⟩ := mem_biUnion.mp hf
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hf
    exact ⟨_,_,rfl,hAvoid e he j (mem_range.mp hj)⟩
  · have hUniverse : D.pathEdges.image (selectorTriangle v) =
        routingFanUniverse v φ src tgt Q t int :=
      (routingFanUniverse_eq_subdivision v D).symm
    rw [hUniverse]
    exact hCount

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.ambient_dense_weighted_embedding
