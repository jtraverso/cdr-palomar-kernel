module
public import RequestProject.TypedTriangle.PaschDenseWeightedWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelSimul SelBridge SelTyped S07V26 S07V27
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- Small potential and small cardinality are different statements. This
cardinality bound uses the actual edge support and pair-codegree. -/
theorem family_card_le_codegree_mul_edge_card (U : Finset (Finset V))
    (E : Finset (Sym2 V)) (L : ℕ) (hL : PairCodegreeBound U L)
    (hThree : ∀ Q∈U, Q.card=3) (hSupport : ∀ Q∈U, triEdges Q⊆E) :
    U.card≤L*E.card := by
  let fiber := fun e => U.filter (fun Q => e∈triEdges Q)
  have hFiber : ∀ e, (fiber e).card≤L := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      by_cases hab : a=b
      · subst b
        have hEmpty : fiber s(a,a)=∅ := by
          apply filter_eq_empty_iff.mpr
          intro Q hQ he
          exact (mem_triEdges.mp he).2.2 rfl
        rw [hEmpty,card_empty]
        exact Nat.zero_le L
      · have hEq : fiber s(a,b)=U.filter (fun Q => a∈Q ∧ b∈Q) := by
          ext Q
          simp only [fiber,mem_filter,mem_triEdges]
          tauto
        rw [hEq]
        exact hL a b hab
  have hSub : U⊆E.biUnion fiber := by
    intro Q hQ
    have hNonempty : (triEdges Q).Nonempty := card_pos.mp (by rw [card_triEdges_three (hThree Q hQ)]; omega)
    obtain ⟨e,he⟩ := hNonempty
    exact mem_biUnion.mpr ⟨e,hSupport Q hQ he,mem_filter.mpr ⟨hQ,he⟩⟩
  calc
    U.card≤(E.biUnion fiber).card := card_le_card hSub
    _≤∑ e∈E, (fiber e).card := card_biUnion_le
    _≤∑ _e∈E, L := sum_le_sum (fun e _ => hFiber e)
    _=L*E.card := by simp [mul_comm]

/-- The cover of a finite edge family is bounded by the sum of its vertex
incidences, without rounding a real degree cap up to a natural number. -/
theorem edge_card_le_real_degree_cap (E : Finset (Sym2 V)) (δ : ℝ)
    (hDeg : ∀ v, (edeg E v : ℝ)≤δ*Fintype.card V) :
    (E.card : ℝ)≤δ*(Fintype.card V : ℝ)^2 := by
  have hCover : E⊆univ.biUnion (fun v : V => E.filter (fun e => v∈e)) := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact mem_biUnion.mpr ⟨a,mem_univ _,mem_filter.mpr ⟨he,by simp⟩⟩
  have hNat : E.card≤∑ v : V, edeg E v :=
    (card_le_card hCover).trans card_biUnion_le
  have hReal : (E.card : ℝ)≤∑ v : V, (edeg E v : ℝ) := by exact_mod_cast hNat
  calc
    (E.card : ℝ)≤∑ v : V, (edeg E v : ℝ) := hReal
    _≤∑ _v : V, δ*Fintype.card V := sum_le_sum (fun v _ => hDeg v)
    _=δ*(Fintype.card V : ℝ)^2 := by simp; ring

/-- Reflect pair-codegree through an injective carrier map. -/
theorem pairCodegreeBound_of_mapConfiguration (ι : V ↪ Ambient) (U : Finset (Finset V))
    (L : ℕ) (hMap : PairCodegreeBound (mapConfiguration ι U) L) : PairCodegreeBound U L := by
  intro a b hab
  have hh := hMap (ι a) (ι b) (fun he => hab (ι.injective he))
  have hEq : ((mapConfiguration ι U).filter (fun Q => ι a∈Q ∧ ι b∈Q)).card=
      (U.filter (fun Q => a∈Q ∧ b∈Q)).card := by
    unfold mapConfiguration
    rw [filter_map,card_map]
    congr 1
    apply filter_congr
    intro Q _
    change (ι a∈Q.map ι ∧ ι b∈Q.map ι) ↔ (a∈Q ∧ b∈Q)
    simp only [mem_map']
  rwa [hEq] at hh

theorem selectorUniverse_edges_subset {G : SimpleGraph V} {lab : V→I}
    {F : Set (Multiset I)} {X B : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B.Adj]
    {Z : Finset V} {Adm : V→Finset V→Prop} {A q : ℕ} {σ : V→LocalSel V}
    (h : SimulFamily G lab F X B Z Adm A q σ) :
    ∀ Q∈selectorUniverse Z σ, triEdges Q⊆fuelU Z σ∪X.edgeFinset := by
  intro Q hQ f hf
  obtain ⟨v,hv,hQ⟩ := mem_biUnion.mp hQ
  obtain ⟨e,he,rfl⟩ := mem_image.mp hQ
  obtain ⟨x,y,rfl,_,hAllowed⟩ := (h.valid v hv).permitted he
  have hT : IsAllowed (⟨G,lab⟩ : Host V I) F {v,x,y} := hAllowed
  have hEq : selectorTriangle v s(x,y)=({v,x,y} : Finset V) := by
    simp only [selectorTriangle,Sym2.toFinset_mk_eq]
  rw [hEq,←Envelope.triE_eq_triEdges hT] at hf
  have hCases : f=s(x,y) ∨ f=s(v,x) ∨ f=s(v,y) := by
    simp only [triE,Sym2.lift_mk,wedge,mem_insert,mem_singleton] at hf
    tauto
  have hRadial : ∀ u∈s(x,y), s(v,u)∈fuelU Z σ∪X.edgeFinset := by
    intro u hu
    rcases (h.valid v hv).supp s(x,y) he u hu with hPort | hAux
    · apply mem_union_right
      exact (SimpleGraph.mem_edgeFinset).mpr ((SimpleGraph.mem_neighborFinset X v u).mp hPort)
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨v,hv,SelSimul.SimulFamily.mem_fuel.mpr (Or.inr ⟨u,hAux,rfl⟩)⟩
  rcases hCases with rfl | rfl | rfl
  · exact mem_union_left _ (mem_biUnion.mpr ⟨v,hv,SelSimul.SimulFamily.mem_fuel.mpr (Or.inl he)⟩)
  · exact hRadial x (by simp)
  · exact hRadial y (by simp)

theorem forkModes_edges_subset {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {X B : Finset (Sym2 V)} {fk : Sym2 V→Fork V}
    (hFS : ForkSystem H.G H.lab F W X B fk) :
    ∀ Q∈forkModes (XZ X W) fk, triEdges Q⊆forkUnion (XZ X W) fk∪X := by
  intro Q hQ f hf
  rcases mem_union.mp hQ with hOffQ | hOnQ
  · have hOff : IsDecomposition H F ((forkUnion (XZ X W) fk\QU fk ∅)∪∅)
        (modeDec fk (XZ X W) ∅) := (hFS.fork_modes (I':=∅) (empty_subset _)).1
    have hh := hOff.subset hOffQ hf
    have hRf : f∈forkUnion (XZ X W) fk\QU fk ∅ := (mem_union.mp hh).resolve_right (by intro h; simpa using h)
    exact mem_union_left _ (mem_sdiff.mp hRf).1
  · have hOn : IsDecomposition H F ((forkUnion (XZ X W) fk\QU fk (XZ X W))∪XZ X W)
        (modeDec fk (XZ X W) (XZ X W)) := (hFS.fork_modes (I':=XZ X W) subset_rfl).1
    rcases mem_union.mp (hOn.subset hOnQ hf) with hh | hh
    · exact mem_union_left _ (mem_sdiff.mp hh).1
    · exact mem_union_right _ (XZ_subset X W hh)

/-- The full universe stored by WeightedWithdrawalResult has actual support
in R plus the input stock. No choice of modes is made by this lemma. -/
theorem weighted_withdrawal_universe_edges_subset
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
    (fk : Sym2 V→Fork V) (σ : V→LocalSel V) (C : Finset (Sym2 V))
    (DPaid : Finset (Finset V)) (A q : ℕ) :
    let T := XZ X.edgeFinset W
    let Rf := forkUnion T fk
    let GX := SimpleGraph.fromEdgeSet ((((X.edgeFinset\T)∪QU fk T) : Finset (Sym2 V)) : Set (Sym2 V))
    let GB := SimpleGraph.fromEdgeSet (((X.edgeFinset∪B.edgeFinset∪Rf) : Finset (Sym2 V)) : Set (Sym2 V))
    let Z := univ\W
    ForkSystem H.G H.lab F W X.edgeFinset B.edgeFinset fk →
    SimulFamily H.G H.lab F GX GB Z (rootAdm H.G H.lab F GX) A q σ →
    IsDecomposition H F (Rf∪(fuelU Z σ∪C)) (modeDec fk T ∅∪DPaid) →
    ∀ Q∈forkModes T fk∪(selectorUniverse Z σ∪DPaid),
      triEdges Q⊆(Rf∪(fuelU Z σ∪C))∪X.edgeFinset := by
  intro T Rf GX GB Z hFS hFam hDR Q hQ f hf
  letI : Fintype GX.edgeSet := GX.fintypeEdgeSet
  letI : Fintype GB.edgeSet := GB.fintypeEdgeSet
  have hGX : GX.edgeFinset⊆X.edgeFinset∪Rf := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    change e∈(SimpleGraph.fromEdgeSet ((((X.edgeFinset\T)∪QU fk T) : Finset (Sym2 V)) : Set (Sym2 V))).edgeSet at he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    rcases mem_union.mp he.1 with he | he
    · exact mem_union_left _ (mem_sdiff.mp he).1
    · exact mem_union_right _ ((hFS.fork_modes (I':=T) subset_rfl).2.1 he)
  rcases mem_union.mp hQ with hFork | hOther
  · rcases mem_union.mp (forkModes_edges_subset hFS Q hFork hf) with hh | hh
    · exact mem_union_left _ (mem_union_left _ hh)
    · exact mem_union_right _ hh
  · rcases mem_union.mp hOther with hSelector | hPaid
    · rcases mem_union.mp (selectorUniverse_edges_subset hFam Q hSelector hf) with hh | hh
      · exact mem_union_left _ (mem_union_right _ (mem_union_left _ hh))
      · rcases mem_union.mp (hGX hh) with hh | hh
        · exact mem_union_right _ hh
        · exact mem_union_left _ (mem_union_left _ hh)
    · exact mem_union_left _ (hDR.subset (mem_union_right _ hPaid) hf)

/-- The cardinality needed for mixed masses follows from support and actual
degree caps; a small value of the Pasch potential is not used. -/
theorem weighted_universe_card_le_real_degree_caps
    (ι : V ↪ Ambient) (U : Finset (Finset V)) (R X : Finset (Sym2 V))
    (hCodeg : PairCodegreeBound (mapConfiguration ι U) 63)
    (hThree : ∀ Q∈U,Q.card=3) (hSupport : ∀ Q∈U,triEdges Q⊆R∪X)
    (τ ρ : ℝ) (hR : ∀ v,(edeg R v : ℝ)≤τ*Fintype.card V)
    (hX : ∀ v,(edeg X v : ℝ)≤ρ*Fintype.card V) :
    (U.card : ℝ)≤63*(τ+ρ)*(Fintype.card V : ℝ)^2 := by
  have hLocal := pairCodegreeBound_of_mapConfiguration ι U 63 hCodeg
  have hCard := family_card_le_codegree_mul_edge_card U (R∪X) 63 hLocal hThree hSupport
  have hDegree : ∀ v,(edeg (R∪X) v : ℝ)≤(τ+ρ)*Fintype.card V := by
    intro v
    have hh : (edeg (R∪X) v : ℝ)≤edeg R v+edeg X v := by exact_mod_cast edeg_union_le R X v
    have h1 := hR v
    have h2 := hX v
    nlinarith only [hh,h1,h2]
  have hEdges := edge_card_le_real_degree_cap (R∪X) (τ+ρ) hDegree
  have hCardR : (U.card : ℝ)≤63*(R∪X).card := by exact_mod_cast hCard
  nlinarith only [hCardR,hEdges]
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.family_card_le_codegree_mul_edge_card
#print axioms TypedTriangle.Pasch.edge_card_le_real_degree_cap
#print axioms TypedTriangle.Pasch.pairCodegreeBound_of_mapConfiguration
#print axioms TypedTriangle.Pasch.selectorUniverse_edges_subset
#print axioms TypedTriangle.Pasch.forkModes_edges_subset
#print axioms TypedTriangle.Pasch.weighted_withdrawal_universe_edges_subset
#print axioms TypedTriangle.Pasch.weighted_universe_card_le_real_degree_caps
