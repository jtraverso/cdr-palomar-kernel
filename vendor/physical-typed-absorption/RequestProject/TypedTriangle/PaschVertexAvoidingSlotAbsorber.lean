module
public import RequestProject.TypedTriangle.PaschVertexAvoidingSlotPhases
public import RequestProject.TypedTriangle.PaschWeightedSlotAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V] {ι : Type*}

theorem slot_absorber_avoiding_vertices_with_support_budget {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (Bad : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (O : Finset ι) (tri : ι → Finset V) (sgn : ι → Prop) (hO : ∀ o ∈ O, IsAllowed H F (tri o))
    (hOBad : ∀ o ∈ O, Disjoint (tri o) Bad)
    (hcert : ∀ e, ((O.filter (fun o => sgn o ∧ e ∈ triEdges (tri o))).card : ℤ) =
      (O.filter (fun o => ¬ sgn o ∧ e ∈ triEdges (tri o))).card + if e ∈ P then 1 else 0)
    (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + Bad.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Bad.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧ Fresh (Z ∪ O.biUnion tri) A ∧
      ((Z ∪ O.biUnion tri) ∪ support A).card ≤
        (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ∧
      A.card ≤ O.card * (4 * (2 * h - 2).choose 2 + 6) ∧
      (supportIncrementCost R (Z ∪ O.biUnion tri) (support A):ℝ) ≤
        (O.card:ℝ)*absorptionPotentialCost α h Ub L ∧ Disjoint (support A) Bad := by
  set U₀ := Z ∪ O.biUnion tri
  have htriU₀ : ∀ o ∈ O, tri o ⊆ U₀ := fun o ho =>
    (Finset.subset_biUnion_of_mem tri ho).trans Finset.subset_union_right
  have hZU₀ : Z ⊆ U₀ := Finset.subset_union_left
  have hU₀Bad : Disjoint U₀ Bad := by
    apply disjoint_union_left.mpr
    refine ⟨hZBad,?_⟩
    apply disjoint_left.mpr
    intro v hv hb
    obtain ⟨o,ho,hv⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hOBad o ho) hv hb
  obtain ⟨Y, ap, U₁, hU₀₁, hU₁c, hap, hinj, hYpos, hYneg, hYWd, hYB, hYU₀, hYin, hYe, hGadgetPay, hU₁Bad⟩ :=
    gadget_phase_avoiding_vertices_with_support_budget hα hH3 hH4 R L hL Bad B d hdeg tri sgn Ub hwin1 hwin2 O U₀ hU₀Bad
      (fun o ho => ⟨hO o ho, htriU₀ o ho⟩) (by omega)
  set Sl := occSlots O tri
  have hbaseU₀ : ∀ s ∈ Sl, ∀ p ∈ s.2, p ∈ U₀ := fun s hs p hp =>
    htriU₀ _ (mem_occSlots.1 hs).1 (mem_of_mem_triEdges (mem_occSlots.1 hs).2 hp)
  have hSF : SlotFamily H F Prod.snd ap Sl U₁ P :=
    ⟨fun s hs => ⟨not_isDiag_of_mem_triEdges (mem_occSlots.1 hs).2, (hap s hs).2.2.1,
      (hap s hs).2.2.2⟩, hinj, fun s hs s' hs' h' => (hap s hs).1 (hbaseU₀ s' hs' _ h'),
      fun s hs => ⟨fun p hp => hU₀₁ (hbaseU₀ s hs p hp), (hap s hs).2.1⟩,
      (hPZ.mono hZU₀).mono hU₀₁, fun e he s hs h' => (hap s hs).1 (hZU₀ (hPZ e he _ h'))⟩
  have hSC : SlotCount Prod.snd (fun s : ι × Sym2 V => sgn s.1) Sl P := by
    intro e
    have h1 := occSlots_filter_card (O := O) (tri := tri) sgn e
    have h2 := occSlots_filter_card (O := O) (tri := tri) (fun o => ¬ sgn o) e
    rw [h1, h2]; exact hcert e
  have hN : (Sl.filter (fun s => ¬ sgn s.1)).card ≤ 3 * O.card :=
    (Finset.card_filter_le _ _).trans (occSlots_card_le (fun o ho => (hO o ho).1))
  obtain ⟨J, hJneg, hJpos, hJB, hJU₁, hJc, hJe, hPairPay, hJBad⟩ :=
    pairing_phase_avoiding_vertices_with_support_budget hα hH3 hH4 R L hL Bad B d hdeg P Prod.snd ap (fun s => sgn s.1) Ub (by linarith)
      (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
      (3 * O.card) Sl U₁ hU₁Bad hN (by nlinarith) hSF hSC
  set Wpos := (Sl.filter (fun s => sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  set Wneg := (Sl.filter (fun s => ¬ sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  have hWall : Sl.biUnion (fun s => wedgeOf s.2 (ap s)) = Wpos ∪ Wneg := by
    show _ = (Sl.filter _).biUnion _ ∪ (Sl.filter _).biUnion _
    rw [← Finset.union_biUnion, Finset.filter_union_filter_not_eq]
  have hWposneg : Disjoint Wpos Wneg := by
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    exact hSF.wedge_disjoint_biUnion (Finset.mem_filter.1 hs).1 _ (Finset.filter_subset _ _)
      (fun h' => (Finset.mem_filter.1 h').2 (Finset.mem_filter.1 hs).2)
  have hWposin : Inside U₁ Wpos := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hWnegin : Inside U₁ Wneg := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hYWpos : Disjoint Y Wpos := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_left) hYWd
  have hYWneg : Disjoint Y Wneg := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_right) hYWd
  have hPU₁ : Inside U₁ P := hSF.insideP
  have hWP : ∀ X ⊆ Sl, Disjoint (X.biUnion (fun s => wedgeOf s.2 (ap s))) P := by
    intro X hX
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_right]
    intro f hf
    exact not_mem_wedgeOf_of_not_mem (hSF.apexP f hf s (hX hs))
  have hYP : Disjoint Y P := ((hPZ.mono hZU₀).disjoint_fresh hYU₀).symm
  have hJP : Disjoint J P := (hPU₁.disjoint_fresh hJU₁).symm
  refine ⟨Y ∪ (Wpos ∪ Wneg) ∪ J, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hYP,
      Finset.disjoint_union_left.2 ⟨hWP _ (Finset.filter_subset _ _),
        hWP _ (Finset.filter_subset _ _)⟩⟩, hJP⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J = (Y ∪ Wpos) ∪ (J ∪ Wneg) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYpos hJneg ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨hYin.disjoint_fresh hJU₁, hYWneg⟩, Finset.disjoint_union_right.2
      ⟨hWposin.disjoint_fresh hJU₁, hWposneg⟩⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J ∪ P = (Y ∪ Wneg) ∪ (J ∪ Wpos ∪ P) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYneg hJpos ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨Finset.disjoint_union_right.2 ⟨hYin.disjoint_fresh hJU₁, hYWpos⟩, hYP⟩,
      Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
      ⟨hWnegin.disjoint_fresh hJU₁, hWposneg.symm⟩, hWP _ (Finset.filter_subset _ _)⟩⟩
  · rw [← hWall]
    exact Finset.disjoint_union_left.2 ⟨hYB, hJB⟩
  · rw [← hWall]
    exact (hYU₀.union (fresh_wedges (fun s hs => (hap s hs).1))).union (hJU₁.anti hU₀₁)
  · have hsub : U₀ ∪ support (Y ∪ (Wpos ∪ Wneg) ∪ J) ⊆ U₁ ∪ support J := by
      rw [support_union, support_union, support_union]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hw | ((hw | hw | hw) | hw)
      · exact Or.inl (hU₀₁ hw)
      · exact Or.inl (support_subset_of_inside hYin hw)
      · exact Or.inl (support_subset_of_inside hWposin hw)
      · exact Or.inl (support_subset_of_inside hWnegin hw)
      · exact Or.inr hw
    refine (Finset.card_le_card hsub).trans (hJc.trans ?_)
    omega
  · have hSl : Sl.card ≤ 3 * O.card := occSlots_card_le (fun o ho => (hO o ho).1)
    have hW : (Wpos ∪ Wneg).card ≤ 2 * Sl.card := by
      rw [← hWall]
      refine Finset.card_biUnion_le.trans ?_
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun s _ => ?_
      refine Finset.card_image_le.trans ?_
      induction s.2 using Sym2.ind with
      | _ x y => rw [Sym2.toFinset_mk_eq]; exact Finset.card_le_two
    refine (Finset.card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
    have : 3 * O.card * (2 * h - 2).choose 2 = O.card * (3 * (2 * h - 2).choose 2) := by ring
    nlinarith

  · have hInsideAll : Inside (U₁ ∪ support J) (Y ∪ (Wpos ∪ Wneg) ∪ J) :=
      ((hYin.mono subset_union_left).union
        ((hWposin.mono subset_union_left).union (hWnegin.mono subset_union_left))).union
        ((inside_support J).mono subset_union_right)
    have hMono := supportIncrementCost_mono R U₀ (support_subset_of_inside hInsideAll)
    have hLedger : supportIncrementCost R U₀ (U₁ ∪ support J) =
        supportIncrementCost R U₀ U₁+supportIncrementCost R U₁ (support J) := by
      simpa only [union_eq_right.mpr hU₀₁] using supportIncrementCost_union R U₀ U₁ (support J)
    have hReal : (supportIncrementCost R U₀ (support (Y ∪ (Wpos ∪ Wneg) ∪ J)):ℝ) ≤
        (supportIncrementCost R U₀ U₁:ℝ)+(supportIncrementCost R U₁ (support J):ℝ) := by
      exact_mod_cast hMono.trans_eq hLedger
    calc (supportIncrementCost R U₀ (support (Y ∪ (Wpos ∪ Wneg) ∪ J)):ℝ)
        ≤ (supportIncrementCost R U₀ U₁:ℝ)+(supportIncrementCost R U₁ (support J):ℝ) := hReal
      _ ≤ (O.card:ℝ)*gadgetPotentialCost α h Ub L+
          ((3*O.card:ℕ):ℝ)*compositePotentialCost α h Ub L := add_le_add hGadgetPay hPairPay
      _ = (O.card:ℝ)*absorptionPotentialCost α h Ub L := by
        unfold absorptionPotentialCost
        push_cast
        ring

  · apply disjoint_left.mpr
    intro v hv hvBad
    rw [support_union,support_union,support_union] at hv
    simp only [mem_union] at hv
    rcases hv with (hv | hv | hv) | hv
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hYin hv) hvBad
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hWposin hv) hvBad
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hWnegin hv) hvBad
    · exact disjoint_left.mp hJBad hv hvBad

theorem slot_absorber_of_coeffs_avoiding_vertices_with_support_budget {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (Bad : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (S : Finset (Finset V)) (hS : ∀ T ∈ S, IsAllowed H F T) (c : Finset V → ℤ)
    (hSBad : ∀ T ∈ S, c T ≠ 0 → Disjoint T Bad)
    (hP : ∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e) (K : ℕ)
    (hK : ∑ T ∈ S, (c T).natAbs ≤ K) (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
      3 * K * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + Bad.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Bad.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
      Fresh (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) A ∧
      ((Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) ∪ support A).card ≤
        (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
          3 * K * (2 * h - 3) ∧
      A.card ≤ K * (4 * (2 * h - 2).choose 2 + 6) ∧
      (supportIncrementCost R (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) (support A):ℝ) ≤
        (K:ℝ)*absorptionPotentialCost α h Ub L ∧ Disjoint (support A) Bad := by
  set O := coeffOcc S c
  have hOS : O.biUnion Prod.fst = (S.filter (fun T => c T ≠ 0)).biUnion id := by
    ext x
    simp only [Finset.mem_biUnion, mem_coeffOcc, Finset.mem_filter, id, O]
    constructor
    · rintro ⟨⟨T, j⟩, ⟨hT, hj⟩, hx⟩
      exact ⟨T, ⟨hT, fun h0 => by simp [h0] at hj⟩, hx⟩
    · rintro ⟨T, ⟨hT, hc⟩, hx⟩
      exact ⟨(T, 0), ⟨hT, by simpa [Int.natAbs_pos] using hc⟩, hx⟩
  have hOcard : O.card ≤ K := by
    have := coeffOcc_filter_card S c (fun _ => True)
    simp only [Finset.filter_true] at this
    show (coeffOcc S c).card ≤ K
    rw [this]; exact hK
  have hcert : ∀ e, ((O.filter (fun o => 0 < c o.1 ∧ e ∈ triEdges o.1)).card : ℤ) =
      (O.filter (fun o => ¬ 0 < c o.1 ∧ e ∈ triEdges o.1)).card + if e ∈ P then 1 else 0 := by
    intro e
    rw [coeffOcc_filter_card S c (fun T => 0 < c T ∧ e ∈ triEdges T),
      coeffOcc_filter_card S c (fun T => ¬ 0 < c T ∧ e ∈ triEdges T)]
    have hind : (if e ∈ P then (1 : ℤ) else 0) = ∑ T ∈ S.filter (fun T => e ∈ triEdges T), c T := by
      have := hP e
      simp only [ind] at this
      rw [this, Finset.sum_filter]
      exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp
    rw [hind, ← Finset.sum_filter_add_sum_filter_not (S.filter (fun T => e ∈ triEdges T))
      (fun T => 0 < c T), Finset.filter_filter, Finset.filter_filter]
    push_cast
    have h1 : ∑ T ∈ S.filter (fun T => 0 < c T ∧ e ∈ triEdges T), |c T| =
        ∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ 0 < c T) =
        S.filter (fun T => 0 < c T ∧ e ∈ triEdges T) from Finset.filter_congr (fun _ _ => and_comm)]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_pos (Finset.mem_filter.1 hT).2.1]
    have h2 : ∑ T ∈ S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T), |c T| =
        -∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T) =
        S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T) from
          Finset.filter_congr (fun _ _ => and_comm), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_nonpos (not_lt.1 (Finset.mem_filter.1 hT).2.1)]
    rw [h1, h2]; ring
  have hUb' : (Z ∪ O.biUnion Prod.fst).card + O.card * (2 * h - 2) +
      3 * O.card * (2 * h - 3) ≤ Ub := by
    rw [hOS]
    have := Nat.mul_le_mul_right (2 * h - 2) hOcard
    have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
    omega
  obtain ⟨A, hA, hAB, hAF, hAc, hAe, hPay, hAvoid⟩ := slot_absorber_avoiding_vertices_with_support_budget hα hH3 hH4 R L hL Bad B d hdeg P O Prod.fst
    (fun o => 0 < c o.1) (fun o ho => hS _ (mem_coeffOcc.1 ho).1)
    (fun o ho => hSBad o.1 (mem_coeffOcc.mp ho).1 (by
      intro hc0
      have hj := (mem_coeffOcc.mp ho).2
      simpa [hc0] using hj)) (fun e => by convert hcert e)
    Z hZBad hPZ Ub hUb' hwin1 hwin2
  rw [hOS] at hAF hAc hPay
  refine ⟨A, hA, hAB, hAF, hAc.trans ?_, hAe.trans (Nat.mul_le_mul_right _ hOcard),
    hPay.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hOcard)
      (by unfold absorptionPotentialCost gadgetPotentialCost compositePotentialCost hingePotentialCost; positivity)),hAvoid⟩
  have := Nat.mul_le_mul_right (2 * h - 2) hOcard
  have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
  omega


#print axioms slot_absorber_avoiding_vertices_with_support_budget
#print axioms slot_absorber_of_coeffs_avoiding_vertices_with_support_budget
end TypedTriangle.Pasch
