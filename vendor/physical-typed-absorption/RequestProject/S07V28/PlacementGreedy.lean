/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V28.AbsorberPlacement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Greedy simultaneous placement with a saturation counter (V28)

Counters for a family `P : ι → Finset (Sym2 V)` of pieces and a family `A` of absorbers:

* `rootInc P v` — number of NONEMPTY pieces whose support contains `v` (local incidence);
* `auxCount P A v` — number of indices `i` with `v` used by `A i` OUTSIDE the support of `P i`
  (auxiliary use; occurrences of indices, roots are not counted).

`greedy_placement`: pieces are processed one at a time; the forbidden edge window for the
current piece is `B ∪ ⋃ P ∪ ⋃ (earlier absorbers)`, the forbidden vertex window is the set of
saturated vertices (`auxCount ≥ q`). The total number of auxiliary positions is
`≤ 2 s · #{nonempty pieces} ≤ 2 s n r` (local incidence, not the number of pieces), hence the
saturated set has size `≤ σ` as soon as `2 s n r < q (σ + 1)`.
-/

open Finset

noncomputable section
open Classical

namespace S07V28

open TypedTriangle.SparseEdge

variable {V I ι : Type*} [Fintype V] [Fintype ι]

/-- Local incidence: number of nonempty pieces whose support contains `v`. -/
def rootInc (P : ι → Finset (Sym2 V)) (v : V) : ℕ :=
  (univ.filter (fun i => P i ≠ ∅ ∧ v ∈ support (P i))).card

/-- Auxiliary-use counter. -/
def auxCount (P A : ι → Finset (Sym2 V)) (v : V) : ℕ :=
  (univ.filter (fun i => v ∈ support (A i) ∧ v ∉ support (P i))).card

/-- The number of nonempty pieces is at most `n r`. -/
lemma card_nonempty_le (P : ι → Finset (Sym2 V)) (r : ℕ) (hr : ∀ v, rootInc P v ≤ r) :
    (univ.filter (fun i => P i ≠ ∅)).card ≤ Fintype.card V * r := by
  calc (univ.filter (fun i => P i ≠ ∅)).card
      = ∑ i ∈ univ.filter (fun i => P i ≠ ∅), 1 := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => P i ≠ ∅), (support (P i)).card := by
        refine sum_le_sum (fun i hi => ?_)
        exact (support_nonempty (mem_filter.1 hi).2).card_pos
    _ = ∑ v : V, rootInc P v := by
        unfold rootInc
        simp only [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        refine sum_congr rfl (fun i _ => ?_)
        split_ifs with h
        · simp only [support, Finset.sum_filter]
          refine sum_congr rfl (fun v _ => ?_)
          simp only [ne_eq] at h
          simp [h]
        · simp [h]
    _ ≤ ∑ _v : V, r := sum_le_sum (fun v _ => hr v)
    _ = Fintype.card V * r := by simp

lemma sum_auxCount_le (P A : ι → Finset (Sym2 V)) :
    ∑ v : V, auxCount P A v ≤ ∑ i, (support (A i)).card := by
  unfold auxCount
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_le_sum (fun i _ => ?_)
  rw [← sum_filter]
  refine sum_le_sum_of_subset (fun v hv => ?_)
  simp only [mem_filter, mem_univ, true_and] at hv
  exact hv.1

/-- The total degree of the absorbers at `v` is controlled by local incidence plus auxiliary
use, not by the number of pieces. -/
lemma degIn_biUnion_absorbers_le (P A : ι → Finset (Sym2 V)) (s : ℕ)
    (hs : ∀ i, (A i).card ≤ s) (v : V) :
    degIn (univ.biUnion A) v ≤ s * (rootInc P v + auxCount P A v) := by
  refine (degIn_biUnion_le _ _ v).trans ?_
  have hsplit : ∑ i, degIn (A i) v =
      ∑ i ∈ univ.filter (fun i => v ∈ support (A i)), degIn (A i) v := by
    rw [sum_filter]
    refine sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rfl
    · exact degIn_eq_zero_of_not_mem h
  rw [hsplit]
  refine (sum_le_sum (fun i _ => (degIn_le_card (A i) v).trans (hs i))).trans ?_
  rw [sum_const, smul_eq_mul, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  unfold rootInc auxCount
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro i hi
  simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  by_cases hP : v ∈ support (P i)
  · exact Or.inl ⟨ne_empty_of_mem_support hP, hP⟩
  · exact Or.inr ⟨hi, hP⟩

/-- The input union has degree `≤ k · rootInc`. -/
lemma degIn_biUnion_pieces_le (P : ι → Finset (Sym2 V)) (k : ℕ)
    (hk : ∀ i, (support (P i)).card ≤ k) (v : V) :
    degIn (univ.biUnion P) v ≤ k * rootInc P v := by
  refine (degIn_biUnion_le _ _ v).trans ?_
  have hsplit : ∑ i, degIn (P i) v =
      ∑ i ∈ univ.filter (fun i => P i ≠ ∅ ∧ v ∈ support (P i)), degIn (P i) v := by
    rw [sum_filter]
    refine sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rfl
    · by_cases hv : v ∈ support (P i)
      · exact absurd ⟨ne_empty_of_mem_support hv, hv⟩ h
      · exact degIn_eq_zero_of_not_mem hv
  rw [hsplit]
  refine (sum_le_sum (fun i _ => (degIn_le_card_support (P i) v).trans (hk i))).trans ?_
  rw [sum_const, smul_eq_mul, mul_comm]
  rfl

/-- Invariant of the greedy schedule after processing the indices in `T`. -/
def PlaceInv (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (P : ι → Finset (Sym2 V)) (B : Finset (Sym2 V)) (s q : ℕ) (T : Finset ι)
    (A : ι → Finset (Sym2 V)) : Prop :=
  (∀ i, i ∉ T → A i = ∅) ∧ (∀ i, P i = ∅ → A i = ∅) ∧
    (∀ i ∈ T, IsAbsorber G lab F (P i) (A i)) ∧
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i, Disjoint (A i) (B ∪ univ.biUnion P)) ∧
    (∀ i, (A i).card ≤ s) ∧ (∀ v, auxCount P A v ≤ q)

lemma placeInv_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (P : ι → Finset (Sym2 V)) (B : Finset (Sym2 V)) (s q : ℕ) :
    PlaceInv G lab F P B s q ∅ (fun _ => ∅) := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, by simp, fun _ _ _ => by simp, fun _ => by simp,
    fun _ => by simp, fun v => ?_⟩
  simp [auxCount, support]

/-- Size of the saturated set. -/
lemma card_sat_le (P A : ι → Finset (Sym2 V)) (r s σ q : ℕ) (hr : ∀ v, rootInc P v ≤ r)
    (hs : ∀ i, (A i).card ≤ s) (hPA : ∀ i, P i = ∅ → A i = ∅)
    (hσ : 2 * s * (Fintype.card V * r) < q * (σ + 1)) :
    (univ.filter (fun v => q ≤ auxCount P A v)).card ≤ σ := by
  set Sat := univ.filter (fun v => q ≤ auxCount P A v)
  have h1 : Sat.card * q ≤ ∑ v : V, auxCount P A v := by
    calc Sat.card * q = ∑ _v ∈ Sat, q := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ Sat, auxCount P A v := sum_le_sum (fun v hv => (mem_filter.1 hv).2)
      _ ≤ ∑ v : V, auxCount P A v := sum_le_sum_of_subset (subset_univ _)
  have h2 : ∑ i, (support (A i)).card ≤ 2 * s * (Fintype.card V * r) := by
    have : ∑ i, (support (A i)).card ≤
        ∑ i ∈ univ.filter (fun i => P i ≠ ∅), 2 * s := by
      rw [sum_filter]
      refine sum_le_sum (fun i _ => ?_)
      split_ifs with h
      · exact (card_support_le _).trans (Nat.mul_le_mul_left _ (hs i))
      · rw [hPA i (not_not.1 h)]; simp [support]
    refine this.trans ?_
    rw [sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ (card_nonempty_le P r hr)
  have h3 : Sat.card * q < (σ + 1) * q := by
    have := (h1.trans (sum_auxCount_le P A)).trans h2
    linarith
  have := Nat.lt_of_mul_lt_mul_right h3
  omega

/-- One step of the greedy schedule. -/
lemma placeInv_insert {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {P : ι → Finset (Sym2 V)} {B : Finset (Sym2 V)} {k r b s D σ q : ℕ}
    (hk : ∀ i, (support (P i)).card ≤ k) (hr : ∀ v, rootInc P v ≤ r)
    (hb : ∀ v, degIn B v ≤ b)
    (hsup : ∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s D σ)
    (hD : b + k * r + s * (r + q) ≤ D) (hσ : 2 * s * (Fintype.card V * r) < q * (σ + 1))
    {T : Finset ι} {j : ι} (hj : j ∉ T) {A : ι → Finset (Sym2 V)}
    (hA : PlaceInv G lab F P B s q T A) :
    ∃ A', PlaceInv G lab F P B s q (insert j T) A' := by
  obtain ⟨hout, hPA, habs, hdisj, hBU, hcard, haux⟩ := hA
  by_cases hPj : P j = ∅
  · refine ⟨A, fun i hi => hout i (fun h => hi (mem_insert_of_mem h)), hPA, ?_, hdisj, hBU,
      hcard, haux⟩
    intro i hi
    rcases mem_insert.1 hi with rfl | hi
    · rw [hPA i hPj, hPj]; exact isAbsorber_empty G lab F
    · exact habs i hi
  -- forbidden windows
  set Fb := B ∪ univ.biUnion P ∪ univ.biUnion A with hFb
  set Sat := univ.filter (fun v => q ≤ auxCount P A v) with hSat
  have hFbdeg : ∀ v, degIn Fb v ≤ D := by
    intro v
    show degIn (B ∪ univ.biUnion P ∪ univ.biUnion A) v ≤ D
    have e1 := degIn_union_le (B ∪ univ.biUnion P) (univ.biUnion A) v
    have e2 := degIn_union_le B (univ.biUnion P) v
    have e3 := degIn_biUnion_pieces_le P k hk v
    have e4 := degIn_biUnion_absorbers_le P A s hcard v
    have e5 : k * rootInc P v ≤ k * r := Nat.mul_le_mul_left _ (hr v)
    have e6 : s * (rootInc P v + auxCount P A v) ≤ s * (r + q) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (hr v) (haux v))
    have := hb v
    omega
  have hSatcard : Sat.card ≤ σ := card_sat_le P A r s σ q hr hcard hPA hσ
  obtain ⟨A0, hA0abs, hA0Fb, hA0card, hA0S⟩ := hsup j hPj Fb hFbdeg Sat hSatcard
  refine ⟨Function.update A j A0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hij : i ≠ j := fun h => hi (h ▸ mem_insert_self _ _)
    rw [Function.update_of_ne hij]
    exact hout i (fun h => hi (mem_insert_of_mem h))
  · intro i hi
    have hij : i ≠ j := fun h => hPj (h ▸ hi)
    rw [Function.update_of_ne hij]; exact hPA i hi
  · intro i hi
    by_cases hij : i = j
    · subst hij; rw [Function.update_self]; exact hA0abs
    · rw [Function.update_of_ne hij]; exact habs i ((mem_insert.1 hi).resolve_left hij)
  · have hA0 : ∀ i, Disjoint A0 (A i) := fun i =>
      Disjoint.mono_right (subset_biUnion_of_mem A (mem_univ i))
        (Disjoint.mono_right subset_union_right hA0Fb)
    intro i i' hii'
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, Function.update_of_ne (Ne.symm hii')]; exact hA0 i'
    · by_cases hi' : i' = j
      · subst hi'
        rw [Function.update_self, Function.update_of_ne hi]; exact (hA0 i).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hi']; exact hdisj i i' hii'
  · intro i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]
      exact Disjoint.mono_right subset_union_left hA0Fb
    · rw [Function.update_of_ne hi]; exact hBU i
  · intro i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact hA0card
    · rw [Function.update_of_ne hi]; exact hcard i
  · intro v
    have hAj : A j = ∅ := hout j hj
    have hsub : univ.filter (fun i => v ∈ support (Function.update A j A0 i) ∧
        v ∉ support (P i)) ⊆
        insert j (univ.filter (fun i => v ∈ support (A i) ∧ v ∉ support (P i))) := by
      intro i hi
      by_cases hij : i = j
      · subst hij; exact mem_insert_self _ _
      · rw [mem_insert]; right
        simpa [Function.update_of_ne hij] using hi
    by_cases hnew : v ∈ support A0 ∧ v ∉ support (P j)
    · have hvS : v ∉ Sat := fun h => hnew.2 (hA0S v hnew.1 h)
      have hlt : auxCount P A v < q := by
        by_contra hc
        exact hvS (mem_filter.2 ⟨mem_univ _, not_lt.1 hc⟩)
      unfold auxCount at hlt ⊢
      exact ((card_le_card hsub).trans (card_insert_le _ _)).trans hlt
    · have hsub' : univ.filter (fun i => v ∈ support (Function.update A j A0 i) ∧
          v ∉ support (P i)) ⊆
          univ.filter (fun i => v ∈ support (A i) ∧ v ∉ support (P i)) := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          simp only [mem_filter, mem_univ, true_and, Function.update_self] at hi
          exact absurd hi hnew
        · simp only [mem_filter, mem_univ, true_and, Function.update_of_ne hij] at hi ⊢
          exact hi
      exact (card_le_card hsub').trans (haux v)

/-- **Greedy simultaneous placement.** Under the robust single-piece supply for every nonempty
piece, absorbers for all pieces exist simultaneously: pairwise edge-disjoint, disjoint from `B`
and from every piece, empty for empty pieces, each of `≤ s` edges, auxiliary use `≤ q` at every
vertex, and global degree `≤ s (r + q)`. -/
theorem greedy_placement (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (P : ι → Finset (Sym2 V)) (B : Finset (Sym2 V)) (k r b s D σ q : ℕ)
    (hk : ∀ i, (support (P i)).card ≤ k) (hr : ∀ v, rootInc P v ≤ r)
    (hb : ∀ v, degIn B v ≤ b)
    (hsup : ∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s D σ)
    (hD : b + k * r + s * (r + q) ≤ D) (hσ : 2 * s * (Fintype.card V * r) < q * (σ + 1)) :
    ∃ A : ι → Finset (Sym2 V),
      (∀ i, P i = ∅ → A i = ∅) ∧
      (∀ i, IsAbsorber G lab F (P i) (A i)) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ i, Disjoint (A i) B) ∧
      (∀ i j, Disjoint (A i) (P j)) ∧
      (∀ i, (A i).card ≤ s) ∧
      (∀ v, auxCount P A v ≤ q) ∧
      (∀ v, degIn (univ.biUnion A) v ≤ s * (r + q)) := by
  have key : ∀ T : Finset ι, ∃ A, PlaceInv G lab F P B s q T A := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨_, placeInv_empty G lab F P B s q⟩
    | insert j T hj ih =>
      obtain ⟨A, hA⟩ := ih
      exact placeInv_insert hk hr hb hsup hD hσ hj hA
  obtain ⟨A, -, hPA, habs, hdisj, hBU, hcard, haux⟩ := key univ
  refine ⟨A, hPA, fun i => habs i (mem_univ i), hdisj, fun i => ?_, fun i j => ?_, hcard, haux,
    fun v => ?_⟩
  · exact Disjoint.mono_right subset_union_left (hBU i)
  · exact Disjoint.mono_right ((subset_biUnion_of_mem P (mem_univ j)).trans subset_union_right)
      (hBU i)
  · exact (degIn_biUnion_absorbers_le P A s hcard v).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add (hr v) (haux v)))

end S07V28
