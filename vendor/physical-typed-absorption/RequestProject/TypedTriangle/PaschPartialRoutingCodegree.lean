module
public import RequestProject.TypedTriangle.PaschSelectorUniverse
public import RequestProject.TypedTriangle.PaschModeUniverse
public import RequestProject.Selectors.GreedyEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelBridge SelEmbed SelSubdiv SelSimul
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Rooting every edge of a bounded-degree base graph gives bounded pair
codegree even before a whole simultaneous selector family has been built. -/
theorem rooted_edge_universe_pairCodegree (v : V) (P : Finset (Sym2 V))
    (d : ℕ) (hd : 1 ≤ d) (hP : ∀ x, edeg P x ≤ d) :
    PairCodegreeBound (P.image (selectorTriangle v)) d := by
  have atRoot : ∀ b, b ≠ v →
      ((P.image (selectorTriangle v)).filter (fun T => v ∈ T ∧ b ∈ T)).card ≤ d := by
    intro b hb
    have hSub : (P.image (selectorTriangle v)).filter (fun T => v ∈ T ∧ b ∈ T) ⊆
        (P.filter (fun e => b ∈ e)).image (selectorTriangle v) := by
      intro T hT
      obtain ⟨hT,_,hbT⟩ := mem_filter.mp hT
      obtain ⟨e,he,rfl⟩ := mem_image.mp hT
      have hbE : b ∈ e := by
        rcases mem_insert.mp hbT with h | h
        · exact False.elim (hb h)
        · exact Sym2.mem_toFinset.mp h
      exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hbE⟩,rfl⟩
    exact (card_le_card hSub).trans (card_image_le.trans (hP b))
  intro a b hab
  by_cases ha : a = v
  · subst a
    exact atRoot b hab.symm
  by_cases hb : b = v
  · subst b
    have hEq : (P.image (selectorTriangle v)).filter (fun T => a ∈ T ∧ v ∈ T) =
        (P.image (selectorTriangle v)).filter (fun T => v ∈ T ∧ a ∈ T) := by
      ext T; simp only [mem_filter,and_comm]
    rw [hEq]
    exact atRoot a ha
  have hOne : ((P.image (selectorTriangle v)).filter (fun T => a ∈ T ∧ b ∈ T)).card ≤ 1 := by
    apply card_le_one.mpr
    intro S hS T hT
    obtain ⟨hS,haS,hbS⟩ := mem_filter.mp hS
    obtain ⟨hT,haT,hbT⟩ := mem_filter.mp hT
    obtain ⟨e,he,rfl⟩ := mem_image.mp hS
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hT
    have haE : a ∈ e := Sym2.mem_toFinset.mp ((mem_insert.mp haS).resolve_left ha)
    have hbE : b ∈ e := Sym2.mem_toFinset.mp ((mem_insert.mp hbS).resolve_left hb)
    have haF : a ∈ f := Sym2.mem_toFinset.mp ((mem_insert.mp haT).resolve_left ha)
    have hbF : b ∈ f := Sym2.mem_toFinset.mp ((mem_insert.mp hbT).resolve_left hb)
    have heq : e = s(a,b) := Sym2.eq_of_ne_mem hab haE hbE (by simp) (by simp)
    have hfq : f = s(a,b) := Sym2.eq_of_ne_mem hab haF hbF (by simp) (by simp)
    rw [heq,hfq]
  exact hOne.trans hd

/-- Any partial actual routing has the same constant degree bound as its
abstract gadget. This prevents the averaging bound growing with path count. -/
theorem partial_routing_pairCodegree {α : Type*} [DecidableEq α]
    {H : SimpleGraph V} {φ : α → V} {src tgt : Sym2 α → α}
    {ℓ : ℕ} {Z0 : Finset V} {Q : Finset (Sym2 α)}
    {t : Sym2 α → ℕ} {int : Sym2 α → ℕ → V}
    (hφ : Function.Injective φ) (hEnds : ∀ e ∈ Q, s(src e,tgt e) = e)
    (hNe : ∀ e ∈ Q, src e ≠ tgt e) (hOK : RouteOK H φ src tgt ℓ Z0 Q t int)
    (d : ℕ) (hDegree : ∀ x, (Q.filter (fun e => x ∈ e)).card ≤ d) (v : V) :
    let D : OddSubdivision H Q := ⟨φ,src,tgt,t,int,hφ,hEnds,hNe,hOK.inj,hOK.ne,hOK.adj⟩
    PairCodegreeBound (D.pathEdges.image (selectorTriangle v)) (max 2 d) := by
  dsimp only
  apply rooted_edge_universe_pairCodegree
  · omega
  · exact OddSubdivision.pathEdges_degree_le (D := _) hDegree

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.rooted_edge_universe_pairCodegree
#print axioms TypedTriangle.Pasch.partial_routing_pairCodegree
