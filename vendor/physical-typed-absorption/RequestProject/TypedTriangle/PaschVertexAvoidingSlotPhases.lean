module
public import RequestProject.TypedTriangle.PaschVertexAvoidingPrimitives
public import RequestProject.TypedTriangle.SlotAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V] {ι σ : Type*}

theorem gadget_phase_avoiding_vertices_with_support_budget {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (tri : ι → Finset V) (sgn : ι → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + Z.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Z.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (O : Finset ι) (U : Finset V), Disjoint U Z → (∀ o ∈ O, IsAllowed H F (tri o) ∧ tri o ⊆ U) →
      U.card + O.card * (2 * h - 2) ≤ Ub →
      ∃ (Y : Finset (Sym2 V)) (ap : ι × Sym2 V → V) (U' : Finset V),
        U ⊆ U' ∧ U'.card ≤ U.card + O.card * (2 * h - 2) ∧
        (∀ s ∈ occSlots O tri, ap s ∉ U ∧ ap s ∈ U' ∧ ap s ∉ s.2 ∧
          IsAllowed H F (slotTri s.2 (ap s))) ∧
        (∀ s ∈ occSlots O tri, ∀ s' ∈ occSlots O tri, ap s = ap s' → s = s') ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => ¬ sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint Y ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint (Y ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) B ∧
        Fresh U Y ∧ Inside U' Y ∧ Y.card ≤ O.card * (2 * h - 2).choose 2 ∧
        (supportIncrementCost R U U':ℝ) ≤ (O.card:ℝ)*gadgetPotentialCost α h Ub L ∧ Disjoint U' Z := by
  intro O
  induction O using Finset.induction_on with
  | empty =>
    intro U hUZ _ _
    refine ⟨∅, fun s => (Quot.out s.2).1, U, subset_refl _, by simp, by simp [occSlots],
      by simp [occSlots], ?_, ?_, by simp, by simp [occSlots], fun e he => by simp at he,
      fun e he => by simp at he, by simp, ?_, hUZ⟩
    · simpa [occSlots] using Basal.empty H F
    · simpa [occSlots] using Basal.empty H F
    · rw [supportIncrementCost_self]
      simp
  | @insert o O ho ih =>
    intro U hUZ hOU hU
    have hoU := hOU o (Finset.mem_insert_self _ _)
    have hcardins : (insert o O).card = O.card + 1 := Finset.card_insert_of_notMem ho
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by rw [hcardins] at hU; nlinarith
      exact_mod_cast this
    obtain ⟨Y₀, ap₀, hap₀, hinj₀, hY₀, hY₀W, hY₀Wd, hY₀B, hY₀U, hcard₀, hY₀e, hPay₀, hNoZ₀⟩ :=
      exists_low_cost_slot_gadget_avoiding_vertices hα hH3 hH4 hoU.1 R L hL U Ub
        (by exact_mod_cast hUb) hoU.2 Z hUZ B d hdeg hwin1 hwin2
    set W₀ := (triEdges (tri o)).biUnion (fun e => wedgeOf e (ap₀ e))
    set U₁ := U ∪ support (Y₀ ∪ W₀)
    have hUU₁ : U ⊆ U₁ := Finset.subset_union_left
    have hU₁Z : Disjoint U₁ Z := disjoint_union_left.mpr ⟨hUZ,hNoZ₀⟩
    have hin₁ : Inside U₁ (Y₀ ∪ W₀) := (inside_support _).mono Finset.subset_union_right
    obtain ⟨Y', ap', U', hU₁U', hU'c, hap', hinj', hY'pos, hY'neg, hY'Wd, hY'B, hY'U, hY'in,
      hY'e, hPay', hU'Z⟩ :=
      ih U₁ hU₁Z (fun o' ho' => ⟨(hOU o' (Finset.mem_insert_of_mem ho')).1,
        (hOU o' (Finset.mem_insert_of_mem ho')).2.trans hUU₁⟩) (by
          rw [hcardins] at hU
          have : (O.card + 1) * (2 * h - 2) = O.card * (2 * h - 2) + (2 * h - 2) := by ring
          have h0 : (U ∪ support (Y₀ ∪ W₀)).card ≤ U.card + (2 * h - 2) := hcard₀
          omega)
    set ap : ι × Sym2 V → V := fun s => if s.1 = o then ap₀ s.2 else ap' s
    have hap_o : ∀ e, ap (o, e) = ap₀ e := fun e => by simp [ap]
    have hap_O : ∀ s ∈ occSlots O tri, ap s = ap' s := fun s hs => by
      have : s.1 ≠ o := fun h' => ho (h' ▸ (mem_occSlots.1 hs).1)
      simp [ap, this]
    have hap₀U₁ : ∀ e ∈ triEdges (tri o), ap₀ e ∈ U₁ := fun e he =>
      Finset.mem_union_right _ (apex_mem_support (not_isDiag_of_mem_triEdges he)
        (fun f hf => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, hf⟩)))
    have hW'eq : ∀ (q : ι × Sym2 V → Prop) [DecidablePred q],
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap s)) =
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s)) := fun q _ =>
      Finset.biUnion_congr rfl (fun s hs => by rw [hap_O s (Finset.mem_filter.1 hs).1])
    have hW₀eq : (triEdges (tri o)).biUnion (fun e => wedgeOf (o, e).2 (ap (o, e))) = W₀ :=
      Finset.biUnion_congr rfl (fun e _ => by rw [hap_o])
    have hfresh' : ∀ (q : ι × Sym2 V → Prop) [DecidablePred q],
        Fresh U₁ (((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fun q _ => fresh_wedges (fun s hs => (hap' s (Finset.mem_filter.1 hs).1).1)
    have hsplit : ∀ (q : ι → Prop) [DecidablePred q],
        ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s)) = (if q o then W₀ else ∅) ∪
        ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      intro q _
      rw [biUnion_filter_insert, hW'eq (fun s => q s.1)]
      congr 1
      split_ifs
      · exact hW₀eq
      · rfl
    have hWall : (occSlots (insert o O) tri).biUnion (fun s => wedgeOf s.2 (ap s)) =
        W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      have := hsplit (fun _ => True)
      simp only [if_true, Finset.filter_true] at this
      exact this
    have hY'U₁ : Fresh U₁ Y' := hY'U
    have hfreshall : Fresh U₁ ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fresh_wedges (fun s hs => (hap' s hs).1)
    have hdisj₁ : ∀ X, Fresh U₁ X → Disjoint (Y₀ ∪ W₀) X := fun X hX => hin₁.disjoint_fresh hX
    have hmode : ∀ (q : ι → Prop) [DecidablePred q],
        Basal H F (Y' ∪ ((occSlots O tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap' s))) →
        Basal H F ((Y₀ ∪ Y') ∪ ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) := by
      intro q _ hq
      rw [hsplit q]
      set X0 : Finset (Sym2 V) := if q o then W₀ else ∅ with hX0
      set R := ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s))
      have heq : Y₀ ∪ Y' ∪ (X0 ∪ R) = (Y₀ ∪ X0) ∪ (Y' ∪ R) := by
        ext; simp only [Finset.mem_union]; tauto
      have hX0sub : Y₀ ∪ X0 ⊆ Y₀ ∪ W₀ := by
        intro f hf
        rw [hX0] at hf
        split_ifs at hf
        · exact hf
        · exact Finset.mem_union_left _ (by simpa using hf)
      have hq0 : Basal H F (Y₀ ∪ X0) := by
        rw [hX0]; split_ifs
        · exact hY₀W
        · simpa using hY₀
      rw [heq]
      exact Basal.union hq0 hq (Disjoint.mono_left hX0sub (hdisj₁ _ (hY'U₁.union (hfresh' (fun s => q s.1)))))
    have hcardU₁ : U₁.card ≤ U.card + (2 * h - 2) := hcard₀
    refine ⟨Y₀ ∪ Y', ap, U', hUU₁.trans hU₁U', ?_, ?_, ?_, hmode sgn hY'pos, hmode (fun o => ¬ sgn o) hY'neg, ?_, ?_,
      hY₀U.union (hY'U.anti hUU₁),
      ((hin₁.subset Finset.subset_union_left).mono hU₁U').union hY'in, ?_, ?_, hU'Z⟩
    · rw [hcardins]
      have : U.card + (O.card + 1) * (2 * h - 2) = U.card + (2 * h - 2) + O.card * (2 * h - 2) :=
        by ring
      omega
    · intro s hs
      rw [mem_occSlots, Finset.mem_insert] at hs
      obtain ⟨hs1 | hs1, hs2⟩ := hs
      · obtain ⟨o', e⟩ := s
        simp only at hs1 hs2; subst hs1
        rw [hap_o]
        obtain ⟨h1, h2, h3⟩ := hap₀ e hs2
        exact ⟨h1, hU₁U' (hap₀U₁ e hs2), h2, h3⟩
      · have hs' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_O s hs']
        obtain ⟨h1, h2, h3, h4⟩ := hap' s hs'
        exact ⟨fun h' => h1 (hUU₁ h'), h2, h3, h4⟩
    · intro s hs s' hs' hss'
      rw [mem_occSlots, Finset.mem_insert] at hs hs'
      obtain ⟨hs1 | hs1, hs2⟩ := hs <;> obtain ⟨hs1' | hs1', hs2'⟩ := hs'
      · obtain ⟨o₁, e₁⟩ := s; obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1 hs2 hs1' hs2' hss'; subst hs1; subst hs1'
        rw [hap_o, hap_o] at hss'
        rw [hinj₀ e₁ hs2 e₂ hs2' hss']
      · exfalso
        obtain ⟨o₁, e₁⟩ := s
        simp only at hs1 hs2 hss'; subst hs1
        have hs'' : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_o, hap_O s' hs''] at hss'
        exact (hap' s' hs'').1 (hss' ▸ hap₀U₁ e₁ hs2)
      · exfalso
        obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1' hs2' hss'; subst hs1'
        have hs'' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_o, hap_O s hs''] at hss'
        exact (hap' s hs'').1 (hss' ▸ hap₀U₁ e₂ hs2')
      · have h1 : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        have h2 : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_O s h1, hap_O s' h2] at hss'
        exact hinj' s h1 s' h2 hss'
    · rw [hWall]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨hY₀Wd, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, hY'Wd⟩⟩
      · exact Disjoint.mono_left Finset.subset_union_left (hdisj₁ _ hfreshall)
      · exact (Disjoint.mono_left Finset.subset_union_right (hdisj₁ _ hY'U₁)).symm
    · rw [hWall]
      have h1 := Finset.disjoint_union_left.1 hY₀B
      have h2 := Finset.disjoint_union_left.1 hY'B
      have heq : Y₀ ∪ Y' ∪ (W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) =
          (Y₀ ∪ W₀) ∪ (Y' ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      exact Finset.disjoint_union_left.2 ⟨hY₀B, hY'B⟩
    · rw [hcardins, Nat.succ_mul]
      exact (Finset.card_union_le _ _).trans (by omega)

    · have hLocal : supportIncrementCost R U U₁ =
          supportIncrementCost R U (support (Y₀ ∪ W₀)) := by
        unfold supportIncrementCost
        dsimp only [U₁]
        rw [←union_assoc,union_self]
      have hPay0 : (supportIncrementCost R U U₁:ℝ) ≤ gadgetPotentialCost α h Ub L := by
        simpa only [hLocal] using hPay₀
      have hSplit : supportIncrementCost R U U' =
          supportIncrementCost R U U₁+supportIncrementCost R U₁ U' := by
        simpa only [union_eq_right.mpr hU₁U',union_eq_right.mpr hUU₁] using
          supportIncrementCost_union R U U₁ U'
      have hSplitReal : (supportIncrementCost R U U':ℝ) =
          (supportIncrementCost R U U₁:ℝ)+(supportIncrementCost R U₁ U':ℝ) := by exact_mod_cast hSplit
      calc (supportIncrementCost R U U':ℝ) =
            (supportIncrementCost R U U₁:ℝ)+(supportIncrementCost R U₁ U':ℝ) := hSplitReal
        _ ≤ gadgetPotentialCost α h Ub L+(O.card:ℝ)*gadgetPotentialCost α h Ub L :=
          add_le_add hPay0 hPay'
        _ = ((insert o O).card:ℝ)*gadgetPotentialCost α h Ub L := by
          rw [hcardins,Nat.cast_add,Nat.cast_one]
          ring

theorem pairing_phase_avoiding_vertices_with_support_budget {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (base : σ → Sym2 V) (ap : σ → V) (pos : σ → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + Z.card + 2 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Z.card + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (N : ℕ) (Sl : Finset σ) (U : Finset V), Disjoint U Z →
      (Sl.filter (fun s => ¬ pos s)).card ≤ N → U.card + N * (2 * h - 3) ≤ Ub →
      SlotFamily H F base ap Sl U P → SlotCount base pos Sl P →
      ∃ J, Basal H F (J ∪ (Sl.filter (fun s => ¬ pos s)).biUnion
          (fun s => wedgeOf (base s) (ap s))) ∧
        Basal H F (J ∪ (Sl.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) ∧
        Disjoint J B ∧ Fresh U J ∧ (U ∪ support J).card ≤ U.card + N * (2 * h - 3) ∧
        J.card ≤ N * (2 * h - 2).choose 2 ∧
        (supportIncrementCost R U (support J):ℝ) ≤ (N:ℝ)*compositePotentialCost α h Ub L ∧ Disjoint (support J) Z := by
  have hCostNonneg : 0 ≤ compositePotentialCost α h Ub L := by
    unfold compositePotentialCost hingePotentialCost
    positivity
  intro N
  induction N with
  | zero =>
    intro Sl U hUZ hN _ hS hC
    have hneg : Sl.filter (fun s => ¬ pos s) = ∅ := Finset.card_eq_zero.1 (by omega)
    refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp, ?_, by simp [support]⟩
    · rw [hneg]; simpa using Basal.empty H F
    · simpa using basal_pos_slots hS hC hneg
    · have hz : supportIncrementCost R U ∅ ≤ 0 := by
        simpa only [supportIncrementCost_self] using supportIncrementCost_mono R U (empty_subset U)
      have hzR : (supportIncrementCost R U ∅:ℝ) ≤ 0 := by exact_mod_cast hz
      simpa [support] using hzR
  | succ N ih =>
    intro Sl U hUZ hN hU hS hC
    by_cases hneg : Sl.filter (fun s => ¬ pos s) = ∅
    · refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp, ?_, by simp [support]⟩
      · rw [hneg]; simpa using Basal.empty H F
      · simpa using basal_pos_slots hS hC hneg
      · have hz : supportIncrementCost R U ∅ ≤ 0 := by
          simpa only [supportIncrementCost_self] using supportIncrementCost_mono R U (empty_subset U)
        have hzR : (supportIncrementCost R U ∅:ℝ) ≤ 0 := by exact_mod_cast hz
        simpa [support] using hzR.trans (mul_nonneg (Nat.cast_nonneg (N+1)) hCostNonneg)
    obtain ⟨sn, hsn⟩ := Finset.nonempty_iff_ne_empty.2 hneg
    rw [Finset.mem_filter] at hsn
    -- un slot positivo con la misma base
    obtain ⟨sp, hsp⟩ : (Sl.filter (fun s => pos s ∧ base s = base sn)).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := hC (base sn)
      have h2 : 0 < (Sl.filter (fun s => ¬ pos s ∧ base s = base sn)).card :=
        Finset.card_pos.2 ⟨sn, Finset.mem_filter.2 ⟨hsn.1, hsn.2, rfl⟩⟩
      split_ifs at h1 <;> omega
    rw [Finset.mem_filter] at hsp
    obtain ⟨hspS, hspp, hspb⟩ := hsp
    have hne : sn ≠ sp := fun h' => hsn.2 (h' ▸ hspp)
    obtain ⟨u, v, he⟩ := Sym2.exists_mk_eq (base sn)
    have hTn := (hS.tri sn hsn.1).2.2
    have hTp := (hS.tri sp hspS).2.2
    rw [he, slotTri_mk] at hTn
    rw [hspb, he, slotTri_mk] at hTp
    have hab : ap sn ≠ ap sp := fun h' => hne (hS.inj sn hsn.1 sp hspS h')
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by nlinarith
      exact_mod_cast this
    have hRoots : ({u,v,ap sn,ap sp}:Finset V) ⊆ U := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hS.inside sn hsn.1).1 _ (by rw [he]; simp)
      · exact (hS.inside sn hsn.1).1 _ (by rw [he]; simp)
      · exact (hS.inside sn hsn.1).2
      · exact (hS.inside sp hspS).2
    obtain ⟨J₀, hJ₀, hJ₀B, hJ₀ab, hJ₀U, hJ₀c, hPay₀, hNoZ₀⟩ :=
      exists_low_cost_composite_hinge_avoiding_vertices hα hH3 hH4 hab hTn hTp R L hL
        U Ub (by exact_mod_cast hUb) hRoots Z hUZ B d hdeg hwin1 hwin2
    set Sl' := (Sl.erase sn).erase sp
    set U' := U ∪ support J₀
    have hU'Z : Disjoint U' Z := disjoint_union_left.mpr ⟨hUZ,hNoZ₀⟩
    have hSl'sub : Sl' ⊆ Sl := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hsnSl' : sn ∉ Sl' := fun h' => by
      simp [Sl'] at h'
    have hspSl' : sp ∉ Sl' := fun h' => by simp [Sl'] at h'
    have hU'c : U'.card ≤ U.card + (2 * h - 3) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left hJ₀c _)
    have hS' : SlotFamily H F base ap Sl' U' P := hS.mono hSl'sub Finset.subset_union_left
    have hC' : SlotCount base pos Sl' P := by
      intro e
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => pos s ∧ base s = e) hne
      have h2 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s ∧ base s = e) hne
      have h3 := hC e
      by_cases hb : base sn = e
      · rw [if_neg (fun h' => hsn.2 h'.2.1), if_pos ⟨hspS, hspp, hspb.trans hb⟩] at h1
        rw [if_pos ⟨hsn.1, hsn.2, hb⟩, if_neg (fun h' => h'.2.1 hspp)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
      · have hb' : base sp ≠ e := hspb ▸ hb
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h1
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
    have hN' : (Sl'.filter (fun s => ¬ pos s)).card ≤ N := by
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s) hne
      rw [if_pos ⟨hsn.1, hsn.2⟩, if_neg (fun h' => h'.2 hspp)] at h1
      simp only [Sl']; omega
    have hU' : U'.card + N * (2 * h - 3) ≤ Ub := by
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    obtain ⟨J', hJ'neg, hJ'pos, hJ'B, hJ'U, hJ'c, hJ'e, hPay', hNoZ'⟩ := ih Sl' U' hU'Z hN' hU' hS' hC'
    have hJ₀e : J₀.card ≤ (2 * h - 2).choose 2 := by
      have h6 : 6 ≤ h := by
        obtain ⟨i, hi6, hih, -⟩ := hH4 u v (ap sn) (ap sp) hab hTn hTp
        omega
      have := card_le_choose_of_support_le hJ₀c
      rwa [show 2 * h - 3 + 1 = 2 * h - 2 by omega] at this
    -- piezas
    have hJ₀fresh : Fresh U J₀ := hJ₀.fresh hJ₀ab U hJ₀U
    have hJ₀in : Inside U' J₀ := (inside_support J₀).mono Finset.subset_union_right
    have hWn : wedgeOf (base sn) (ap sn) = wedge u v (ap sn) := by rw [he, wedgeOf_mk]
    have hWp : wedgeOf (base sp) (ap sp) = wedge u v (ap sp) := by rw [hspb, he, wedgeOf_mk]
    have hWnin : Inside U (wedgeOf (base sn) (ap sn)) :=
      inside_wedgeOf (hS.inside sn hsn.1).1 (hS.inside sn hsn.1).2
    have hWpin : Inside U (wedgeOf (base sp) (ap sp)) :=
      inside_wedgeOf (hS.inside sp hspS).1 (hS.inside sp hspS).2
    have hnegeq : Sl.filter (fun s => ¬ pos s) = insert sn (Sl'.filter (fun s => ¬ pos s)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sn
        · exact Or.inl h1
        · exact Or.inr ⟨⟨fun h2 => hps (h2 ▸ hspp), h1, hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hsn.1, hsn.2⟩
        · exact ⟨hs, hps⟩
    have hposeq : Sl.filter pos = insert sp (Sl'.filter pos) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sp
        · exact Or.inl h1
        · exact Or.inr ⟨⟨h1, fun h2 => hsn.2 (h2 ▸ hps), hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hspS, hspp⟩
        · exact ⟨hs, hps⟩
    have hnegsub : Sl'.filter (fun s => ¬ pos s) ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    have hpossub : Sl'.filter pos ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    refine ⟨J₀ ∪ J', ?_, ?_, Finset.disjoint_union_left.2 ⟨hJ₀B, hJ'B⟩,
      hJ₀fresh.union (hJ'U.anti Finset.subset_union_left), ?_, ?_, ?_,
      by rw [support_union]; exact disjoint_union_left.mpr ⟨hNoZ₀,hNoZ'⟩⟩
    · rw [hnegeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sn) (ap sn) ∪
          (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) =
          (J₀ ∪ wedgeOf (base sn) (ap sn)) ∪
          (J' ∪ (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWn]; exact hJ₀.2.2.1) hJ'neg ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hnegsub).disjoint_fresh hJ₀fresh).symm
      · exact (hWnin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hsn.1 _ hnegsub (fun h' => hsnSl'
          (Finset.mem_filter.1 h').1)
    · rw [hposeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sp) (ap sp) ∪
          (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s))) ∪ P =
          (J₀ ∪ wedgeOf (base sp) (ap sp)) ∪
          (J' ∪ (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWp]; exact hJ₀.2.2.2) hJ'pos ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩, Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hpossub).disjoint_fresh hJ₀fresh).symm
      · exact (hS.insideP.disjoint_fresh hJ₀fresh).symm
      · exact (hWpin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hspS _ hpossub (fun h' => hspSl'
          (Finset.mem_filter.1 h').1)
      · rw [Finset.disjoint_right]
        intro f hf
        exact not_mem_wedgeOf_of_not_mem (hS.apexP f hf sp hspS)
    · have heq : U ∪ support (J₀ ∪ J') = U' ∪ support J' := by
        rw [support_union]; simp only [U', Finset.union_assoc]
      rw [heq]
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Nat.succ_mul]
      omega

    · rw [support_union,supportIncrementCost_union,Nat.cast_add]
      change (supportIncrementCost R U (support J₀):ℝ)+
        (supportIncrementCost R U' (support J'):ℝ) ≤ _
      calc (supportIncrementCost R U (support J₀):ℝ)+
            (supportIncrementCost R U' (support J'):ℝ)
          ≤ compositePotentialCost α h Ub L+(N:ℝ)*compositePotentialCost α h Ub L :=
            add_le_add hPay₀ hPay'
        _ = ((N+1:ℕ):ℝ)*compositePotentialCost α h Ub L := by push_cast; ring

#print axioms gadget_phase_avoiding_vertices_with_support_budget
#print axioms pairing_phase_avoiding_vertices_with_support_budget
end TypedTriangle.Pasch
