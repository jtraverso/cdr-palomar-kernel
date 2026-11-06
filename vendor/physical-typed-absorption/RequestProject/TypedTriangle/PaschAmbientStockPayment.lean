module
public import RequestProject.TypedTriangle.PaschCoverDownPotential
public import RequestProject.TypedTriangle.PaschAmbientChildSupport
public import RequestProject.TypedTriangle.PaschEmbeddingIncidence
public import RequestProject.TypedTriangle.PaschCoverDownWindow
public import RequestProject.TypedTriangle.BasalStockEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Pasch
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/- The legacy construction of the packing and its degree bounds from a legal
center assignment, retained verbatim as a private helper. -/
private theorem cover_down_from_centers (H : Host V I) (F : Set (Multiset I)) (U X : Finset (Sym2 V))
    (hUX : Disjoint U X) (hU : ∀ e ∈ U, ¬ e.IsDiag) (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x, w) ∈ X)
    {d q : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (c : Sym2 V → V) (hc1 : ∀ e ∈ U, c e ∈ Cand e)
    (hc2 : ∀ w, (U.filter (c · = w)).card ≤ q)
    (hc3 : ∀ e ∈ U, ∀ e' ∈ U, ∀ x y, x ∈ e → y ∈ e' →
      s(x,c e) = s(y,c e') → e = e') :
    let C := U.image (fun e => insert (c e) e.toFinset)
    IsPacking H F C ∧ U ⊆ C.biUnion triEdges ∧ C.biUnion triEdges ⊆ U ∪ X ∧
      ∀ v, ((C.biUnion triEdges).filter (v ∈ ·)).card ≤ 2*d+2*q := by
  let tri : Sym2 V → Finset V := fun e => insert (c e) e.toFinset
  have hcw : ∀ e ∈ U, c e ∉ e := fun e he => (hCand e he (c e) (hc1 e he)).1
  have hmem : ∀ e ∈ U, ∀ f, f ∈ triEdges (tri e) ↔ f = e ∨ ∃ x ∈ e, f = s(x, c e) :=
    fun e he f => mem_triEdges_insert (hU e he) (hcw e he)
  have hwingX : ∀ e ∈ U, ∀ x ∈ e, s(x, c e) ∈ X :=
    fun e he => (hCand e he (c e) (hc1 e he)).2.2
  have hcommon : ∀ e ∈ U, ∀ e' ∈ U, ∀ f, f ∈ triEdges (tri e) → f ∈ triEdges (tri e') →
      e = e' := by
    intro e he e' he' f hf hf'
    rw [hmem e he] at hf
    rw [hmem e' he'] at hf'
    rcases hf with rfl | ⟨x, hx, rfl⟩ <;> rcases hf' with h' | ⟨y, hy, h'⟩
    · exact h'
    · exact absurd (h' ▸ hwingX e' he' y hy) (Finset.disjoint_left.1 hUX he)
    · exact absurd (h' ▸ he') (Finset.disjoint_left.1 hUX |> fun h => fun h2 =>
        h h2 (hwingX e he x hx))
    · exact hc3 e he e' he' x y hx hy h'
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
    exact (hCand e he (c e) (hc1 e he)).2.1
  · intro T hT T' hT' hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hT)
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hT')
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf hf'
    exact hne (by rw [hcommon e he e' he' f hf hf'])
  · intro e he
    exact Finset.mem_biUnion.2 ⟨tri e, Finset.mem_image_of_mem _ he,
      mem_triEdges_insert_self (hU e he) (hcw e he)⟩
  · intro f hf
    obtain ⟨T, hT, hfT⟩ := Finset.mem_biUnion.1 hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
    rcases (hmem e he f).1 hfT with rfl | ⟨x, hx, rfl⟩
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (hwingX e he x hx)
  · intro v
    have hsub : ((U.image tri).biUnion triEdges).filter (v ∈ ·) ⊆
        U.filter (v ∈ ·) ∪ (U.filter (v ∈ ·)).image (fun e => s(v, c e)) ∪
          (U.filter (c · = v)).biUnion (fun e => e.toFinset.image (fun x => s(x, c e))) := by
      intro f hf
      obtain ⟨hf, hvf⟩ := Finset.mem_filter.1 hf
      obtain ⟨T, hT, hfT⟩ := Finset.mem_biUnion.1 hf
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
      rcases (hmem e he f).1 hfT with rfl | ⟨x, hx, rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hvf⟩))
      · rw [Sym2.mem_iff] at hvf
        rcases hvf with rfl | hv
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨he, hx⟩, rfl⟩))
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e,
            Finset.mem_filter.2 ⟨he, hv.symm⟩,
            Finset.mem_image.2 ⟨x, Sym2.mem_toFinset.2 hx, rfl⟩⟩)
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := hdeg v
    have h2 : ((U.filter (v ∈ ·)).image (fun e => s(v, c e))).card ≤ d :=
      Finset.card_image_le.trans h1
    have h3 : ((U.filter (c · = v)).biUnion
        (fun e => e.toFinset.image (fun x => s(x, c e)))).card ≤ 2 * q := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ e ∈ U.filter (c · = v), (e.toFinset.image (fun x => s(x, c e))).card
          ≤ ∑ _e ∈ U.filter (c · = v), 2 := by
            refine Finset.sum_le_sum fun e _ => Finset.card_image_le.trans ?_
            rw [Sym2.card_toFinset]; split_ifs <;> omega
        _ = 2 * (U.filter (c · = v)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * q := Nat.mul_le_mul_left 2 (hc2 v)
    have := Finset.card_union_le (U.filter (v ∈ ·))
      ((U.filter (v ∈ ·)).image (fun e => s(v, c e)))
    omega


private theorem count_insert_le (R : Finset (Finset Ambient)) (T : Finset Ambient) :
    count (insert T R) ≤ count R + rootedCount (insert T R) T := by
  have hSub : configurations (insert T R) ⊆ configurations R ∪
      (configurations (insert T R)).filter (fun K => T ∈ K) := by
    intro K hK
    by_cases hTK : T ∈ K
    · exact mem_union_right _ (mem_filter.mpr ⟨hK,hTK⟩)
    · apply mem_union_left
      obtain ⟨hKR,hCard,hPasch⟩ := mem_configurations.mp hK
      apply mem_configurations.mpr
      refine ⟨?_,hCard,hPasch⟩
      intro Q hQ
      exact (mem_insert.mp (hKR hQ)).resolve_left (fun h => hTK (h ▸ hQ))
  exact (card_le_card hSub).trans (card_union_le _ _)

/-- The actual greedy uses the same legal centers and quotas. Its potential is
measured against a fixed universe containing P0, without assuming that universe
is a packing. Adding the partial packing raises pair-codegree by at most one. -/
theorem exists_center_choice_with_ambient_fixed_universe_pasch (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I))
    (P0 : Finset (Finset V)) (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset Ambient)) (hP0fixed : mapConfiguration ι P0 ⊆ Rfixed)
    (L : ℕ) (hL : PairCodegreeBound Rfixed L)
    (U X : Finset (Sym2 V)) (hUX : Disjoint U X)
    (hProtected : Disjoint (P0.biUnion triEdges) (U∪X)) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d q : ℕ} (hq : 0 < q) (κ : ℝ) (hκ : 0 < κ) (hn : 0 < Fintype.card V)
    (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hMargin : ∀ e ∈ U,
      (U.card : ℝ)+(q : ℝ)*(2*(d+2*q) : ℕ)+(q : ℝ)*κ*Fintype.card V ≤
        (q : ℝ)*(Cand e).card) :
    ∃ c : Sym2 V → V, (∀ e ∈ U, c e ∈ Cand e) ∧
      (∀ w, (U.filter (c · = w)).card ≤ q) ∧
      (∀ e ∈ U, ∀ e' ∈ U, ∀ x y, x ∈ e → y ∈ e' →
        s(x,c e) = s(y,c e') → e = e') ∧
      (count (Rfixed ∪ mapConfiguration ι (U.image (fun e => insert (c e) e.toFinset))) : ℝ) ≤
        count Rfixed+(U.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  suffices key : ∀ S ⊆ U, ∃ c : Sym2 V → V, (∀ e ∈ S, c e ∈ Cand e) ∧
      (∀ w, (S.filter (c · = w)).card ≤ q) ∧
      (∀ e ∈ S, ∀ e' ∈ S, ∀ x y, x ∈ e → y ∈ e' →
        s(x,c e) = s(y,c e') → e = e') ∧
      (count (Rfixed ∪ mapConfiguration ι (S.image (fun e => insert (c e) e.toFinset))) : ℝ) ≤
        count Rfixed+(S.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ from key U (subset_refl _)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun e => (Quot.out e).1,by simp,by simp,by simp,by simp [mapConfiguration]⟩
  | @insert e S he ih =>
    intro hsub
    have heU : e ∈ U := hsub (mem_insert_self e S)
    have hSU : S ⊆ U := (subset_insert e S).trans hsub
    obtain ⟨c,hc1,hc2,hc3,hStat⟩ := ih hSU
    let Old := S.image (fun e => insert (c e) e.toFinset)
    let R := Rfixed ∪ mapConfiguration ι Old
    have hPartial := cover_down_from_centers H F S X (hUX.mono_left hSU)
      (fun e he => hU e (hSU he)) Cand (fun e he => hCand e (hSU he))
      (fun x => (card_le_card (filter_subset_filter _ hSU)).trans (hdeg x)) c hc1 hc2 hc3
    have hOld : IsPacking H F Old := hPartial.1
    have hR : PairCodegreeBound R (L+1) :=
      hL.union (pairCodegreeBound_mapConfiguration ι Old 1 (pairCodegreeBound_of_linear (packing_linear hOld)))
    let Bad := saturated S c q ∪ badWing S c e
    let Good := Cand e\Bad
    have hSat := card_saturated_mul_le S c q
    have hWing := card_badWing_le hSU c hdeg hc2 e
    have hBad : q*Bad.card ≤ U.card+q*(2*(d+2*q)) := by
      calc
        q*Bad.card ≤ q*((saturated S c q).card+(badWing S c e).card) :=
          Nat.mul_le_mul_left q (card_union_le _ _)
        _ = q*(saturated S c q).card+q*(badWing S c e).card := by ring
        _ ≤ S.card+q*(2*(d+2*q)) := Nat.add_le_add hSat (Nat.mul_le_mul_left q hWing)
        _ ≤ _ := Nat.add_le_add_right (card_le_card hSU) _
    have hCandGood : (Cand e).card ≤ Good.card+Bad.card := by
      have hh := card_sdiff_add_card_inter (Cand e) Bad
      have hi := card_le_card (inter_subset_right : Cand e∩Bad ⊆ Bad)
      dsimp only [Good]
      omega
    have hGood : κ*(Fintype.card V : ℝ) ≤ Good.card := by
      have h1 : (q : ℝ)*Bad.card ≤ U.card+(q : ℝ)*(2*(d+2*q) : ℕ) := by exact_mod_cast hBad
      have h2 : (q : ℝ)*(Cand e).card ≤ (q : ℝ)*Good.card+(q : ℝ)*Bad.card := by
        have hh := Nat.mul_le_mul_left q hCandGood
        simp only [Nat.mul_add] at hh
        exact_mod_cast hh
      have h3 := hMargin e heU
      apply (mul_le_mul_iff_right₀ hqR).mp
      nlinarith only [h1,h2,h3]
    have hChoice : ∃ w ∈ Good,
        (rootedCount (insert ((insert w e.toFinset).map ι) R) ((insert w e.toFinset).map ι) : ℝ) ≤
          ((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
      induction e using Sym2.ind with
      | h a b =>
        have hab : a ≠ b := by
          intro h
          exact hU s(a,b) heU (by simp only [Sym2.mk_isDiag_iff]; exact h)
        obtain ⟨w,hw,hCost⟩ := exists_rooted_completion_in_embedded_child ι R (L+1) hR (ι a) (ι b) (fun h => hab (ι.injective h)) Good κ hκ hnR hGood
        refine ⟨w,hw,?_⟩
        have hSet : (insert w s(a,b).toFinset).map ι = ({ι a,ι b,ι w} : Finset Ambient) := by
          ext v
          simp [Sym2.toFinset_mk_eq,or_comm,or_left_comm,or_assoc]
        simpa only [hSet] using hCost
    obtain ⟨w,hw,hCost⟩ := hChoice
    have hwC := (mem_sdiff.mp hw).1
    have hwBad := (mem_sdiff.mp hw).2
    have hwsat : w ∉ saturated S c q := fun h => hwBad (mem_union_left _ h)
    have hwwing : w ∉ badWing S c e := fun h => hwBad (mem_union_right _ h)
    have hwsat' : (S.filter (c · = w)).card < q := by simpa [saturated] using hwsat
    have hwwing' : ∀ e' ∈ S, ∀ x y, x ∈ e → y ∈ e' → s(x,w) ≠ s(y,c e') := by
      intro e' he' x y hx hy h
      exact hwwing (by simp only [badWing,mem_filter,mem_univ,true_and]; exact ⟨e',he',x,y,hx,hy,h⟩)
    let c' := Function.update c e w
    have hc'e : c' e = w := Function.update_self e w c
    have hc'S : ∀ e' ∈ S, c' e' = c e' := fun e' he' =>
      Function.update_of_ne (by rintro rfl; exact he he') w c
    have hfilt : ∀ w', S.filter (c' · = w') = S.filter (c · = w') := fun w' =>
      filter_congr (fun e' he' => by rw [hc'S e' he'])
    refine ⟨c',?_,?_,?_,?_⟩
    · intro e' he'
      rcases mem_insert.mp he' with rfl | he'
      · rw [hc'e]; exact hwC
      · rw [hc'S e' he']; exact hc1 e' he'
    · intro w'
      rw [filter_insert]
      by_cases hw' : c' e = w'
      · rw [if_pos hw',card_insert_of_notMem (fun h => he (mem_filter.mp h).1),hfilt]
        rw [hc'e] at hw'
        subst w'
        omega
      · rw [if_neg hw',hfilt]
        exact hc2 w'
    · intro e1 he1 e2 he2 x y hx hy h
      rcases mem_insert.mp he1 with h1 | h1
      · rcases mem_insert.mp he2 with h2 | h2
        · rw [h1,h2]
        · subst e1
          rw [hc'e,hc'S e2 h2] at h
          exact False.elim (hwwing' e2 h2 x y hx hy h)
      · rcases mem_insert.mp he2 with h2 | h2
        · subst e2
          rw [hc'e,hc'S e1 h1] at h
          exact False.elim (hwwing' e1 h1 y x hy hx h.symm)
        · rw [hc'S e1 h1,hc'S e2 h2] at h
          exact hc3 e1 h1 e2 h2 x y hx hy h
    · have hImage : S.image (fun e => insert (c' e) e.toFinset) = Old := by
        apply image_congr
        intro e' he'
        exact congrArg (fun v => insert v e'.toFinset) (hc'S e' he')
      have hNew : Rfixed ∪ mapConfiguration ι ((insert e S).image (fun e => insert (c' e) e.toFinset)) =
          insert ((insert w e.toFinset).map ι) R := by
        rw [image_insert,hc'e,hImage]
        unfold mapConfiguration
        rw [map_insert]
        ext T
        simp only [R,mem_union,mem_insert]
        tauto
      have hStep : (count (insert ((insert w e.toFinset).map ι) R) : ℝ) ≤
          count R+rootedCount (insert ((insert w e.toFinset).map ι) R) ((insert w e.toFinset).map ι) := by
        exact_mod_cast count_insert_le R ((insert w e.toFinset).map ι)
      rw [hNew,card_insert_of_notMem he,Nat.cast_add,Nat.cast_one]
      change (count (insert ((insert w e.toFinset).map ι) R) : ℝ) ≤ count Rfixed+((S.card : ℝ)+1)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ
      have hStatR : (count R : ℝ) ≤ count Rfixed+(S.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := hStat
      have hDiv : ((S.card : ℝ)+1)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ =
          (S.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ+((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by ring
      rw [hDiv]
      linarith only [hStep,hCost,hStatR]

theorem cover_down_with_ambient_fixed_universe_pasch (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I))
    (P0 : Finset (Finset V)) (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset Ambient)) (hP0fixed : mapConfiguration ι P0 ⊆ Rfixed)
    (L : ℕ) (hL : PairCodegreeBound Rfixed L)
    (U X : Finset (Sym2 V)) (hUX : Disjoint U X)
    (hProtected : Disjoint (P0.biUnion triEdges) (U∪X)) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d q : ℕ} (hq : 0 < q) (κ : ℝ) (hκ : 0 < κ) (hn : 0 < Fintype.card V)
    (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hMargin : ∀ e ∈ U,
      (U.card : ℝ)+(q : ℝ)*(2*(d+2*q) : ℕ)+(q : ℝ)*κ*Fintype.card V ≤
        (q : ℝ)*(Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      U ⊆ C.biUnion triEdges ∧ C.biUnion triEdges ⊆ U∪X ∧
      (∀ v, ((C.biUnion triEdges).filter (v ∈ ·)).card ≤ 2*d+2*q) ∧
      (count (Rfixed∪mapConfiguration ι C) : ℝ) ≤ count Rfixed+(U.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
  obtain ⟨c,hc1,hc2,hc3,hStat⟩ := exists_center_choice_with_ambient_fixed_universe_pasch ι H F P0 hP0 Rfixed hP0fixed L hL U X hUX
    hProtected hU Cand hCand hq κ hκ hn hdeg hMargin
  let C := U.image (fun e => insert (c e) e.toFinset)
  have hC := cover_down_from_centers H F U X hUX hU Cand hCand hdeg c hc1 hc2 hc3
  have hDis : Disjoint (P0.biUnion triEdges) (C.biUnion triEdges) :=
    hProtected.mono_right hC.2.2.1
  have hUnion := hP0.isDecomposition.union hC.1.isDecomposition hDis
  exact ⟨C,hC.1,⟨hUnion.1,hUnion.2.1⟩,hC.2.1,hC.2.2.1,hC.2.2.2,hStat⟩

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.exists_center_choice_with_ambient_fixed_universe_pasch
#print axioms TypedTriangle.Pasch.cover_down_with_ambient_fixed_universe_pasch


namespace TypedTriangle.Pasch
open StockEntry.Explicit
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- The native cover-down budgets already leave the half-density margin used
by the actual low-Pasch-cost greedy. No cost-selection oracle is an input. -/
theorem cover_down_native_with_ambient_fixed_universe_pasch (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I)) (P0 : Finset (Finset V))
    (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset Ambient)) (hP0fixed : mapConfiguration ι P0 ⊆ Rfixed)
    (L : ℕ) (hL : PairCodegreeBound Rfixed L) (U X : Finset (Sym2 V)) (hUX : Disjoint U X)
    (hProtected : Disjoint (P0.biUnion triEdges) (U∪X)) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hOrder : coverDownOrder κ η ≤ Fintype.card V)
    (hCard : U.card ≤ Fintype.card V*d)
    (hSparse : (d : ℝ) ≤ coverDownBudget κ η*Fintype.card V)
    (hSupply : ∀ e ∈ U, κ*(Fintype.card V : ℝ) ≤ (Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      U ⊆ C.biUnion triEdges ∧ C.biUnion triEdges ⊆ U∪X ∧
      (∀ v, (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤ η*Fintype.card V) ∧
      (count (Rfixed∪mapConfiguration ι C) : ℝ) ≤ count Rfixed+2*(U.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
  let q := coverDownQuota κ η (Fintype.card V)
  obtain ⟨hq,hMargin,hDegree⟩ := cover_down_window_pasch_margin κ η hκ hη
    (Fintype.card V) U.card d hOrder hCard hSparse
  change 0 < q at hq
  change ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
    (q : ℝ)*κ*Fintype.card V at hMargin
  change ((2*d+2*q : ℕ) : ℝ) ≤ η*Fintype.card V at hDegree
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simpa [q,coverDownQuota,hz] using hq
  have hMargin' : ∀ e ∈ U,
      (U.card : ℝ)+(q : ℝ)*(2*(d+2*q) : ℕ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
        (q : ℝ)*(Cand e).card := by
    intro e he
    calc
      _ = ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V := by
        push_cast
        ring
      _ ≤ (q : ℝ)*κ*Fintype.card V := hMargin
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (hSupply e he) (Nat.cast_nonneg q)
        convert hh using 1 <;> ring
  obtain ⟨C,hC,hPC,hCover,hSub,hDeg,hStat⟩ := cover_down_with_ambient_fixed_universe_pasch ι H F P0 hP0 Rfixed hP0fixed L hL U X hUX
    hProtected hU Cand hCand hq (κ/2) (half_pos hκ) hn hdeg hMargin'
  refine ⟨C,hC,hPC,hCover,hSub,?_,?_⟩
  · intro v
    exact (by exact_mod_cast hDeg v : (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤
      (2*d+2*q : ℕ)).trans hDegree
  · have hnR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn
    have hEq : (U.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/(κ/2) =
        2*(U.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
      field_simp [ne_of_gt hκ,ne_of_gt hnR] <;> ring
    simpa only [hEq] using hStat

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.cover_down_native_with_ambient_fixed_universe_pasch


namespace TypedTriangle.StockEntry
open BasalIncidence
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- The original stock-entry operation, using the actual basal-incidence
candidates, with a Pasch increment bound against the fixed previous universe. -/
theorem enter_stock_native_with_ambient_fixed_universe_pasch (ι : V ↪ Ambient) {H : Host V I} {F : Set (Multiset I)}
    {D P0 : Finset (Finset V)} {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset Ambient)) (hP0fixed : Pasch.mapConfiguration ι P0 ⊆ Rfixed)
    (L : ℕ) (hL : Pasch.PairCodegreeBound Rfixed L)
    (J : Finset (Sym2 V)) (hJH : J ⊆ edges H) (hXJ : cover D ⊆ J)
    (hProtected : Disjoint (P0.biUnion triEdges) J)
    (hphys : IsPhysical H F J)
    (hSupply : ∀ u v, s(u,v) ∈ J\cover D → H.G.Adj u v →
      κ*Fintype.card V ≤ (good H F D u v).card) {d : ℕ}
    (hdeg : ∀ x, ((J\cover D).filter (fun e => x ∈ e)).card ≤ d)
    (hOrder : Explicit.coverDownOrder κ η ≤ Fintype.card V)
    (hCard : (J\cover D).card ≤ Fintype.card V*d)
    (hSparse : (d : ℝ) ≤ Explicit.coverDownBudget κ η*Fintype.card V) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      C.biUnion triEdges ⊆ J ∧ (J\C.biUnion triEdges) ⊆ cover D ∧
      IsPhysical H F (J\C.biUnion triEdges) ∧
      (∀ x, (((C.biUnion triEdges).filter (fun e => x ∈ e)).card : ℝ) ≤
        η*Fintype.card V) ∧
      (Pasch.count (Rfixed∪Pasch.mapConfiguration ι C) : ℝ) ≤ Pasch.count Rfixed+
        2*((J\cover D).card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*((L+1 : ℕ) : ℝ)^3/κ := by
  have hUH : J\cover D ⊆ edges H := sdiff_subset.trans hJH
  have hdiag : ∀ e ∈ J\cover D, ¬ e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using hUH he)
  have hSup : ∀ e ∈ J\cover D,
      κ*(Fintype.card V : ℝ) ≤ (candidates H F (cover D) e).card := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : H.G.Adj u v := by simpa [edges] using hUH he
      exact (hSupply u v he huv).trans (by
        exact_mod_cast card_le_card (good_subset_candidates H F D u v))
  obtain ⟨C,hC,hPC,hcov,hsub,hcd,hStat⟩ := Pasch.cover_down_native_with_ambient_fixed_universe_pasch κ η hκ hη
    ι H F P0 hP0 Rfixed hP0fixed L hL (J\cover D) (cover D) sdiff_disjoint
    (hProtected.mono_right (union_subset sdiff_subset hXJ)) hdiag
    (candidates H F (cover D)) (fun _ _ _ hw => (mem_filter.mp hw).2)
    hdeg hOrder hCard hSparse hSup
  have hCJ : C.biUnion triEdges ⊆ J := hsub.trans (union_subset sdiff_subset hXJ)
  refine ⟨C,hC,hPC,hCJ,?_,
    isPhysical_sdiff_of_decomposition hphys hC.isDecomposition hCJ,hcd,hStat⟩
  intro e he
  by_contra heX
  exact (mem_sdiff.mp he).2 (hcov (mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,heX⟩))

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.enter_stock_native_with_ambient_fixed_universe_pasch
