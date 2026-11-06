module
public import RequestProject.TypedTriangle.PaschAmbientBankSetting
public import RequestProject.TypedTriangle.PaschSeededCellPotential
public import RequestProject.TypedTriangle.PaschEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace TypedTriangle.Pasch.AmbientBank
variable {X V I : Type*} [Fintype X] [Fintype V]

theorem allowed_lift (J : Host X I) (H : Host V I) (F : Set (Multiset I)) (ι : X ↪ V)
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (ι x) (ι y))
    (hLab : ∀ x, J.lab x=H.lab (ι x)) {T : Finset X} (hT : IsAllowed J F T) :
    IsAllowed H F (T.map ι) := by
  refine ⟨by simpa only [card_map] using hT.1, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact hAdj a b (hT.2.1 a ha b hb (fun hh => hxy (congrArg ι hh)))
  · change (T.map ι).val.map H.lab∈F
    rw [Finset.map_val,Multiset.map_map]
    have hh : H.lab ∘ ι=J.lab := funext (fun x => (hLab x).symm)
    change T.val.map (H.lab ∘ ι)∈F
    rw [hh]
    exact hT.2.2

theorem triEdges_lift (ι : X ↪ V) (T : Finset X) : triEdges (T.map ι)=liftEdges ι (triEdges T) := by
  ext f
  constructor
  · intro hf
    induction f using Sym2.ind with
    | h x y =>
      obtain ⟨hx,hy,hxy⟩ := mem_triEdges.mp hf
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact mem_map.mpr ⟨s(a,b),mem_triEdges.mpr
        ⟨ha,hb,fun hh => hxy (congrArg ι hh)⟩,rfl⟩
  · intro hf
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    induction g using Sym2.ind with
    | h a b =>
      obtain ⟨ha,hb,hab⟩ := mem_triEdges.mp hg
      exact mem_triEdges.mpr ⟨mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩,
        fun hh => hab (ι.injective hh)⟩

/-- Lift the literal decomposition; no new decomposition is chosen from Basal. -/
theorem decomposition_lift (J : Host X I) (H : Host V I) (F : Set (Multiset I)) (ι : X ↪ V)
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (ι x) (ι y))
    (hLab : ∀ x, J.lab x=H.lab (ι x)) {E : Finset (Sym2 X)} {D : Finset (Finset X)}
    (hD : IsDecomposition J F E D) : IsDecomposition H F (liftEdges ι E) (mapConfiguration ι D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨U,hU,rfl⟩ := mem_mapConfiguration.mp hT
    exact allowed_lift J H F ι hAdj hLab (hD.1 U hU)
  · intro T hT U hU hne
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hT
    obtain ⟨B,hB,rfl⟩ := mem_mapConfiguration.mp hU
    change Disjoint (triEdges (A.map ι)) (triEdges (B.map ι))
    rw [triEdges_lift,triEdges_lift]
    rw [disjoint_left]
    intro f hfA hfB
    obtain ⟨a,ha,hae⟩ := mem_map.mp hfA
    obtain ⟨b,hb,hbe⟩ := mem_map.mp hfB
    have hab := (edgeEmbedding ι).injective (hae.trans hbe.symm)
    exact disjoint_left.mp (hD.2.1 hA hB (fun hh => hne (congrArg (fun T => T.map ι) hh))) ha (hab ▸ hb)
  · ext f
    constructor
    · intro hf
      obtain ⟨T,hT,hf⟩ := mem_biUnion.mp hf
      obtain ⟨U,hU,rfl⟩ := mem_mapConfiguration.mp hT
      rw [triEdges_lift] at hf
      obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
      exact mem_map.mpr ⟨g,hD.subset hU hg,rfl⟩
    · intro hf
      obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
      rw [←hD.2.2] at hg
      obtain ⟨T,hT,hg⟩ := mem_biUnion.mp hg
      exact mem_biUnion.mpr ⟨T.map ι,mem_mapConfiguration.mpr ⟨T,hT,rfl⟩,
        by rw [triEdges_lift]; exact mem_map.mpr ⟨g,hg,rfl⟩⟩

theorem support_lift (ι : X ↪ V) (E : Finset (Sym2 X)) : support (liftEdges ι E)=(support E).map ι := by
  ext v
  constructor
  · intro hv
    obtain ⟨_,f,hf,hvf⟩ := mem_filter.mp hv
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hvf
    exact mem_map.mpr ⟨x,mem_support_of_mem hg hx,rfl⟩
  · intro hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    obtain ⟨_,g,hg,hxg⟩ := mem_filter.mp hx
    exact mem_support_of_mem (mem_map.mpr ⟨g,hg,rfl⟩)
      (Sym2.mem_map.mpr ⟨x,hxg,rfl⟩)

theorem fresh_lift (ι : X ↪ V) {U : Finset X} {E : Finset (Sym2 X)} (h : Fresh U E) :
    Fresh (U.map ι) (liftEdges ι E) := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
  obtain ⟨x,hx,hxU⟩ := h g hg
  refine ⟨ι x,Sym2.mem_map.mpr ⟨x,hx,rfl⟩, ?_⟩
  intro hv
  obtain ⟨y,hy,hyx⟩ := mem_map.mp hv
  exact hxU (ι.injective hyx ▸ hy)

theorem inside_lift (ι : X ↪ V) {U : Finset X} {E : Finset (Sym2 X)} (h : Inside U E) :
    Inside (U.map ι) (liftEdges ι E) := by
  intro f hf v hvf
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
  obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hvf
  exact mem_map.mpr ⟨x,h g hg x hx,rfl⟩

/-- Generic support counting does not require a triangle-free condition on
an ambient host with isolated vertices. Its premises are proved from LOCAL
freshness and the LOCAL triangle-free input below. -/
theorem mode_cost_le_support {R N : Finset (Finset V)} {U0 U : Finset V}
    (hN : ∀ T ∈ N, T.card=3 ∧ T⊆U ∧ ¬ T⊆U0) :
    (∑ T ∈ N,rootedCount (insert T R) T) ≤ Pasch.supportIncrementCost R U0 U := by
  apply sum_le_sum_of_subset
  intro T hT
  obtain ⟨hCard,hSub,hNew⟩ := hN T hT
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hSub.trans subset_union_right,hCard⟩,hNew⟩

theorem count_union_without_disjoint (R N : Finset (Finset V)) (L : ℕ) (hR : PairCodegreeBound R L) :
    count (N∪R) ≤ count R+(∑ T ∈ N,rootedCount (insert T R) T)+cellUnionPolynomial L N.card := by
  have hb := count_union_le_potential_increment hR (N\R) sdiff_disjoint
  have hUnion : (N\R)∪R=N∪R := by ext T; simp only [mem_union,mem_sdiff]; tauto
  rw [hUnion] at hb
  have hSum : (∑ T ∈ N\R,rootedCount (insert T R) T) ≤ ∑ T ∈ N,rootedCount (insert T R) T :=
    sum_le_sum_of_subset sdiff_subset
  have hPoly := cellUnionPolynomial_mono (L:=L) le_rfl (card_le_card (sdiff_subset : N\R⊆N))
  unfold cellUnionPolynomial at hPoly ⊢
  omega

theorem lifted_mode_shape (J : Host X I) (F : Set (Multiset I)) (ι : X ↪ V)
    {A P : Finset (Sym2 X)} {U0 U : Finset X} {Doff Don : Finset (Finset X)}
    (hOff : IsDecomposition J F A Doff) (hOn : IsDecomposition J F (A∪P) Don)
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle J F P) (hInside : Inside U (A∪P)) :
    ∀ Q ∈ mapConfiguration ι Doff∪mapConfiguration ι Don,
      Q.card=3 ∧ Q⊆U.map ι ∧ ¬ Q⊆U0.map ι := by
  intro Q hQ
  have hPre : ∃ T : Finset X, Q=T.map ι ∧ IsAllowed J F T ∧ triEdges T ⊆ A∪P := by
    rcases mem_union.mp hQ with hQ | hQ
    · obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
      exact ⟨T,rfl,hOff.1 T hT,(hOff.subset hT).trans subset_union_left⟩
    · obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
      exact ⟨T,rfl,hOn.1 T hT,hOn.subset hT⟩
  obtain ⟨T,rfl,hT,hTE⟩ := hPre
  refine ⟨by simpa only [card_map] using hT.1,
    map_subset_map.mpr (triangle_subset_of_inside_edges hT hTE hInside), ?_⟩
  obtain ⟨x,hx,hxNot⟩ := allowed_triangle_meets_outside_of_fresh hFresh hFree hT hTE
  intro hSub
  have hxm := hSub (mem_map.mpr ⟨x,hx,rfl⟩)
  obtain ⟨y,hy,hyx⟩ := mem_map.mp hxm
  exact hxNot (ι.injective hyx ▸ hy)

/-- Local H3/H4 selected the support, and LOCAL freshness proves that its
literal mode blocks are paid by the AMBIENT potential. Both budgets retain
the factor |Vambient|/|X|; no ambient geometry premise is used. -/
theorem lifted_modes_two_budgets
    (J : Host X I) (H : Host V I) (F : Set (Multiset I)) (ι : X ↪ V)
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (ι x) (ι y)) (hLab : ∀ x, J.lab x=H.lab (ι x))
    {A P : Finset (Sym2 X)} {U0 U : Finset X} (Ub : ℕ) (hU : U.card ≤ Ub)
    {Doff Don : Finset (Finset X)} (hOff : IsDecomposition J F A Doff)
    (hOn : IsDecomposition J F (A∪P) Don) (hFresh : Fresh U0 A)
    (hFree : HasNoAllowedTriangle J F P) (hInside : Inside U (A∪P))
    (R0 R : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0)
    (hR : PairCodegreeBound R 2) (ratio baseCost : ℝ) (hRatio : 1≤ratio)
    (hPhi : (Pasch.supportIncrementCost (R0∪R) (U0.map ι) (U.map ι):ℝ) ≤ ratio*baseCost) :
    let N := mapConfiguration ι Doff∪mapConfiguration ι Don
    IsDecomposition H F (liftEdges ι A) (mapConfiguration ι Doff) ∧
    IsDecomposition H F (liftEdges ι (A∪P)) (mapConfiguration ι Don) ∧
    PairCodegreeBound N 2 ∧ N.card≤Ub.choose 3 ∧
    (count (N∪R):ℝ) ≤ count R+ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ)) ∧
    (count (N∪(R0∪R)):ℝ) ≤ count (R0∪R)+ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ)) := by
  let N := mapConfiguration ι Doff∪mapConfiguration ι Don
  have hShape := lifted_mode_shape J F ι hOff hOn hFresh hFree hInside
  have hCard : N.card≤Ub.choose 3 := by
    have hSub : N ⊆ (U.map ι).powersetCard 3 := by
      intro Q hQ
      exact mem_powersetCard.mpr ⟨(hShape Q hQ).2.1,(hShape Q hQ).1⟩
    have hh := card_le_card hSub
    rw [card_powersetCard,card_map] at hh
    exact hh.trans (Nat.choose_le_choose 3 hU)
  have hPhiLocal : (Pasch.supportIncrementCost R (U0.map ι) (U.map ι):ℝ) ≤ ratio*baseCost :=
    (show (Pasch.supportIncrementCost R (U0.map ι) (U.map ι):ℝ) ≤
      Pasch.supportIncrementCost (R0∪R) (U0.map ι) (U.map ι) by
      exact_mod_cast supportIncrementCost_mono_previous (subset_union_right : R⊆R0∪R) _ _).trans hPhi
  have hCountBound (B : Finset (Finset V)) (L : ℕ) (hB : PairCodegreeBound B L)
      (hLB : L≤L0+2)
      (hPB : (Pasch.supportIncrementCost B (U0.map ι) (U.map ι):ℝ) ≤ ratio*baseCost) :
      (count (N∪B):ℝ) ≤ count B+ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ)) := by
    have hSum := mode_cost_le_support (R:=B) (N:=N) hShape
    have hSumR : (∑ T ∈ N,(rootedCount (insert T B) T:ℝ)) ≤ ratio*baseCost :=
      (show (∑ T ∈ N,(rootedCount (insert T B) T:ℝ)) ≤
        (Pasch.supportIncrementCost B (U0.map ι) (U.map ι):ℝ) by exact_mod_cast hSum).trans hPB
    have hNat := count_union_without_disjoint B N L hB
    have hCast : (count (N∪B):ℝ) ≤ count B+(∑ T ∈ N,(rootedCount (insert T B) T:ℝ))+
        (cellUnionPolynomial L N.card:ℝ) := by
      have hh : (count (N∪B):ℝ) ≤
          ((count B+(∑ T ∈ N,rootedCount (insert T B) T)+cellUnionPolynomial L N.card:ℕ):ℝ) := by exact_mod_cast hNat
      simpa only [Nat.cast_add,Nat.cast_sum] using hh
    have hPolyNat := cellUnionPolynomial_mono hLB hCard
    have hPoly : (cellUnionPolynomial L N.card:ℝ) ≤
        ratio*(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by
      have hFirst : (cellUnionPolynomial L N.card:ℝ) ≤ (cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by exact_mod_cast hPolyNat
      have hSecond := mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg (cellUnionPolynomial (L0+2) (Ub.choose 3)))
      exact hFirst.trans (by simpa only [one_mul] using hSecond)
    nlinarith only [hCast,hSumR,hPoly]
  have hOffLift := decomposition_lift J H F ι hAdj hLab hOff
  have hOnLift := decomposition_lift J H F ι hAdj hLab hOn
  exact ⟨hOffLift,hOnLift,pairCodegreeBound_two_modes ⟨hOffLift.1,hOffLift.2.1⟩ ⟨hOnLift.1,hOnLift.2.1⟩,
    hCard,hCountBound R 2 hR (by omega) hPhiLocal,
    hCountBound (R0∪R) (L0+2) (hR0.union hR) le_rfl hPhi⟩

end TypedTriangle.Pasch.AmbientBank
#print axioms TypedTriangle.Pasch.AmbientBank.decomposition_lift
#print axioms TypedTriangle.Pasch.AmbientBank.support_lift
#print axioms TypedTriangle.Pasch.AmbientBank.fresh_lift
#print axioms TypedTriangle.Pasch.AmbientBank.count_union_without_disjoint
#print axioms TypedTriangle.Pasch.AmbientBank.lifted_modes_two_budgets
