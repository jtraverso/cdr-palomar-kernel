/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Completion

/-!
# Trade copies avoiding a prescribed packing

Only copies whose common edge set avoids the occupied edges are retained.
Each rejected copy can be charged to a different occupied edge. Thus deleting
`L` loses at most `L.card` copies, without assuming that the whole placement
avoids `L`. All earlier spectrum and completion modules remain unchanged.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact

variable {V : Type*} [Fintype V] [DecidableEq V] {k m : ℕ}
  {J : Type*} [Fintype J] [DecidableEq J] {lab : V → Fin k}
  (P : Place lab J m) [NeZero m]

/-- Common occupied edge set of a single trade copy. -/
def copyLeave (c : J × ZMod m × ZMod m) : Finset (Sym2 V) :=
  (half1 (phiGE P c)).biUnion triEdges

/-- The copies whose edges avoid `L`. -/
def goodCopies (L : Finset (Sym2 V)) : Finset (J × ZMod m × ZMod m) :=
  univ.filter fun c => Disjoint (copyLeave P c) L

/-- Select either half in each retained copy. -/
def packSelected (S : Finset (J × ZMod m × ZMod m))
    (σ : J × ZMod m × ZMod m → Bool) : Finset (Finset V) :=
  S.biUnion (halfOfG P σ)

/-- The common edge set of the retained copies. -/
def leaveSelected (S : Finset (J × ZMod m × ZMod m)) : Finset (Sym2 V) :=
  S.biUnion (copyLeave P)

theorem packSelected_subset (S : Finset (J × ZMod m × ZMod m)) (σ) :
    packSelected P S σ ⊆ packG P σ := by
  intro T hT
  obtain ⟨c, _, hc⟩ := mem_biUnion.mp hT
  exact mem_biUnion.mpr ⟨c, mem_univ _, hc⟩

theorem packSelected_allowed (S : Finset (J × ZMod m × ZMod m)) (σ) :
    ∀ T ∈ packSelected P S σ, IsAllowed (kHost lab) (bicF k) T :=
  fun T hT => packG_allowed P σ T (packSelected_subset P S σ hT)

theorem packSelected_disj [Fact m.Prime] (hm : 8 < m)
    (S : Finset (J × ZMod m × ZMod m)) (σ) :
    (packSelected P S σ : Set (Finset V)).PairwiseDisjoint triEdges := by
  intro T hT T' hT' hne
  exact packG_disj P hm σ (packSelected_subset P S σ hT)
    (packSelected_subset P S σ hT') hne

theorem packSelected_leave (S : Finset (J × ZMod m × ZMod m)) (σ) :
    (packSelected P S σ).biUnion triEdges = leaveSelected P S := by
  unfold packSelected leaveSelected copyLeave
  rw [biUnion_biUnion]
  refine biUnion_congr rfl fun c _ => ?_
  unfold halfOfG
  split_ifs
  · rfl
  · exact (union_eq (phiGE P c)).symm

/-- Type counts in a retained subfamily; rejected copies contribute nothing. -/
theorem packSelected_count [Fact m.Prime] (hm : 8 < m)
    (S : Finset (J × ZMod m × ZMod m)) (σ) (X Y : Fin k) :
    (kTypeCount lab (packSelected P S σ) X Y : ℤ) =
      ∑ c ∈ S, (mcnt (P.τ c.1) T0m X Y : ℤ) +
        ∑ c ∈ S, (if σ c then
          ((mcnt (P.τ c.1) T1m X Y : ℤ) - mcnt (P.τ c.1) T0m X Y) else 0) := by
  have h : kTypeCount lab (packSelected P S σ) X Y =
      ∑ c ∈ S, kTypeCount lab (halfOfG P σ c) X Y := by
    unfold kTypeCount packSelected
    rw [filter_biUnion, card_biUnion]
    intro c hc c' hc' hcc
    exact disjoint_filter_filter (halves_pairwiseG P hm σ (mem_univ c) (mem_univ c') hcc)
  rw [h]
  push_cast
  rw [← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  unfold halfOfG half1 half0
  split_ifs
  · rw [half_count]; ring
  · rw [half_count]; ring

theorem leaveSelected_subset (S : Finset (J × ZMod m × ZMod m)) :
    leaveSelected P S ⊆ leaveG P := by
  intro e he
  simp only [leaveSelected, leaveG, copyLeave, mem_biUnion] at he ⊢
  obtain ⟨c, _, hc⟩ := he
  exact ⟨c, mem_univ _, hc⟩

theorem degL_mono' {L L' : Finset (Sym2 V)} (h : L ⊆ L') (v : V) :
    degL L v ≤ degL L' v := by
  apply card_le_card
  intro w hw
  exact mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hw).2⟩

theorem degL_leaveSelected (S : Finset (J × ZMod m × ZMod m)) (v : V) :
    degL (leaveSelected P S) v ≤ 9 * m :=
  (degL_mono' (leaveSelected_subset P S) v).trans (degL_leaveG P v)

theorem leaveSelected_good_disjoint (L : Finset (Sym2 V)) :
    Disjoint (leaveSelected P (goodCopies P L)) L := by
  rw [leaveSelected, disjoint_biUnion_left]
  intro c hc
  exact (mem_filter.mp hc).2

set_option linter.constructorNameAsVariable false in
theorem copyLeave_disjoint [Fact m.Prime] (hm : 8 < m) :
    (Set.univ : Set (J × ZMod m × ZMod m)).PairwiseDisjoint (copyLeave P) := by
  intro c _ c' _ hcc
  change Disjoint (copyLeave P c) (copyLeave P c')
  rw [Finset.disjoint_left]
  intro e he he'
  rw [copyLeave, mem_biUnion] at he he'
  obtain ⟨T, hT, he⟩ := he
  obtain ⟨U, hU, he'⟩ := he'
  have hTc : T ∈ halfOfG P (fun _ => true) c := by simpa only [halfOfG, ite_true] using hT
  have hUc : U ∈ halfOfG P (fun _ => true) c' := by simpa only [halfOfG, ite_true] using hU
  by_cases hTU : T = U
  · exact disjoint_left.mp
      (halves_pairwiseG P hm (fun _ => true) (mem_univ _) (mem_univ _) hcc) (hTU ▸ hTc) hUc
  · have hTp : T ∈ packG P (fun _ => true) := mem_biUnion.mpr ⟨c, mem_univ _, hTc⟩
    have hUp : U ∈ packG P (fun _ => true) := mem_biUnion.mpr ⟨c', mem_univ _, hUc⟩
    exact disjoint_left.mp (packG_disj P hm (fun _ => true) hTp hUp hTU) he he'

/-- Edge-disjoint objects meeting `L` inject into `L` by choosing a witness edge. -/
theorem card_rejected_le {C E : Type*} [Fintype C] [DecidableEq C] [DecidableEq E]
    (S : Finset C) (F : C → Finset E) (L : Finset E)
    (hF : (S : Set C).PairwiseDisjoint F) :
    #(S.filter fun c => ¬ Disjoint (F c) L) ≤ #L := by
  classical
  let B := S.filter fun c => ¬ Disjoint (F c) L
  have hex (c : {c // c ∈ B}) : ∃ e, e ∈ F c.val ∧ e ∈ L :=
    not_disjoint_iff.mp (mem_filter.mp c.property).2
  let f : {c // c ∈ B} → {e // e ∈ L} := fun c =>
    ⟨Classical.choose (hex c), (Classical.choose_spec (hex c)).2⟩
  have hf : Function.Injective f := by
    intro c c' he
    apply Subtype.ext
    by_contra hne
    have hd := hF (mem_filter.mp c.property).1 (mem_filter.mp c'.property).1 hne
    have hval := congrArg Subtype.val he
    change Classical.choose (hex c) = Classical.choose (hex c') at hval
    have hmem := (Classical.choose_spec (hex c')).1
    rw [← hval] at hmem
    exact disjoint_left.mp hd (Classical.choose_spec (hex c)).1 hmem
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- The loss bound holds on every subfamily, in particular each cycle coordinate. -/
theorem card_copies_lost [Fact m.Prime] (hm : 8 < m)
    (S : Finset (J × ZMod m × ZMod m)) (L : Finset (Sym2 V)) :
    #S ≤ #(S ∩ goodCopies P L) + #L := by
  have hb := card_rejected_le S (copyLeave P) L
    (fun _ _ _ _ hne => copyLeave_disjoint P hm (Set.mem_univ _) (Set.mem_univ _) hne)
  have he : S ∩ goodCopies P L = S.filter fun c => Disjoint (copyLeave P c) L := by
    ext c; simp [goodCopies]
  rw [he]
  have hc := card_filter_add_card_filter_not (s := S) (p := fun c => Disjoint (copyLeave P c) L)
  omega

/-- The loss estimate applies separately to every coordinate. -/
theorem good_coordinate_capacity [Fact m.Prime] (hm : 8 < m)
    (L : Finset (Sym2 V)) (j : J) :
    m ^ 2 ≤ #((goodCopies P L).filter fun c => c.1 = j) + #L := by
  let F : Finset (J × ZMod m × ZMod m) := univ.filter fun c => c.1 = j
  have hF : F = ({j} : Finset J) ×ˢ (univ : Finset (ZMod m × ZMod m)) := by
    ext ⟨a,b,c⟩; simp [F, Prod.mk.injEq, eq_comm]
  have hcard : #F = m ^ 2 := by
    rw [hF, card_product]; simp [Fintype.card_prod, ZMod.card, sq]
  have hi : F ∩ goodCopies P L = (goodCopies P L).filter fun c => c.1 = j := by
    ext c; simp [F, and_comm]
  have h := card_copies_lost P hm F L
  rw [hcard, hi] at h
  exact h

/-- Each coordinate starts with exactly `m²` copies. -/
theorem selected_coordinate_le (S : Finset (J × ZMod m × ZMod m)) (j : J) :
    #(S.filter fun c => c.1 = j) ≤ m ^ 2 := by
  have hF : (univ.filter fun c : J × ZMod m × ZMod m => c.1 = j) =
      ({j} : Finset J) ×ˢ (univ : Finset (ZMod m × ZMod m)) := by
    ext ⟨a,b,c⟩; simp [Prod.mk.injEq, eq_comm]
  have h := card_le_card (filter_subset_filter (fun c => c.1 = j) (subset_univ S))
  rw [hF, card_product] at h
  simpa [Fintype.card_prod, ZMod.card, sq] using h

/-- A coarse bound suffices; it does not require symmetry or exclusion of loops. -/
theorem card_edges_le_degree_sum (L : Finset (Sym2 V)) {Δ : ℕ}
    (hdeg : ∀ p, degL L p ≤ Δ) : #L ≤ Fintype.card V * Δ := by
  have hsub : L ⊆ univ.biUnion fun v : V => (nbL L v).image fun w => s(w, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ w v =>
      exact mem_biUnion.mpr ⟨v, mem_univ _, mem_image.mpr
        ⟨w, mem_filter.mpr ⟨mem_univ _, he⟩, rfl⟩⟩
  calc #L ≤ #(univ.biUnion fun v : V => (nbL L v).image fun w => s(w, v)) := card_le_card hsub
    _ ≤ ∑ v : V, #((nbL L v).image fun w => s(w, v)) := card_biUnion_le
    _ ≤ ∑ v : V, Δ := sum_le_sum fun v _ => card_image_le.trans (hdeg v)
    _ = Fintype.card V * Δ := by simp

/-- Any packing has at most as many blocks as occupied edges. -/
theorem card_packing_le_edges (Q : Finset (Finset V))
    (hQ : ∀ T ∈ Q, (triEdges T).Nonempty)
    (hdisj : (Q : Set (Finset V)).PairwiseDisjoint triEdges) :
    #Q ≤ #(Q.biUnion triEdges) := by
  have h := card_rejected_le Q triEdges (Q.biUnion triEdges) hdisj
  have hf : Q.filter (fun T => ¬ Disjoint (triEdges T) (Q.biUnion triEdges)) = Q := by
    apply filter_true_of_mem
    intro T hT
    obtain ⟨e, he⟩ := hQ T hT
    exact not_disjoint_iff.mpr ⟨e, he, mem_biUnion.mpr ⟨T, hT, he⟩⟩
  rw [hf] at h
  exact h

/-- Block-disjointness follows from disjoint occupied edge sets. -/
theorem packing_block_disjoint {Q R : Finset (Finset V)}
    (hQ : ∀ T ∈ Q, (triEdges T).Nonempty)
    (h : Disjoint (Q.biUnion triEdges) (R.biUnion triEdges)) : Disjoint Q R := by
  rw [Finset.disjoint_left]
  intro T hT hT'
  obtain ⟨e, he⟩ := hQ T hT
  exact disjoint_left.mp h (mem_biUnion.mpr ⟨T, hT, he⟩)
    (mem_biUnion.mpr ⟨T, hT', he⟩)

theorem degL_union_le (L L' : Finset (Sym2 V)) (v : V) :
    degL (L ∪ L') v ≤ degL L v + degL L' v := by
  have h : nbL (L ∪ L') v = nbL L v ∪ nbL L' v := by
    ext w; simp [nbL]
  simp only [degL, h]
  exact card_union_le _ _

end CDRBicolour.KBicolor
