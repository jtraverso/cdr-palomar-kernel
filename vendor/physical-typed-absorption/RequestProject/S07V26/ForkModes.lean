/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V26.ForkGreedy

@[expose] public section

/-!
# V26 — positive modes of a prebuilt fork system for every later choice

Fix a `ForkSystem G lab F W X P fk` (built BEFORE any subset is chosen). Write
`XZ = XZ X W`, `R = forkUnion XZ fk` (all fork edges) and, for `I' ⊆ XZ`,
`Q(I') = ⋃_{e ∈ I'} Q_e`.

* `fork_modes`: for EVERY `I' ⊆ XZ`, the set `(R ∖ Q(I')) ∪ I'` has the permitted
  decomposition `modeDec I'` (active triangle `uvw` for `e ∈ I'`, the two basal triangles
  `uwa`, `vwb` for `e ∉ I'`), and `Q(I') ⊆ R` is disjoint from it (left available).
* `fork_L`: for every `L ⊆ X`, with `I' = L ∩ XZ`, `L1 = (L ∖ I') ∪ Q(I')` and
  `X1 = (X ∖ XZ) ∪ Q(XZ)`:
  `L ∪ R = L1 ⊔ ((R ∖ Q(I')) ∪ I')` (disjoint), every decomposition of `L1` extends to one of
  `L ∪ R`, `1_L - 1_{L1} ∈ lattice`, `L1 ⊆ X1`, every edge of `X1` meets `W` (`X1[Z] = ∅`),
  and `degIn X1 ≤ degIn X + degIn R`. `X1` is allowed to overlap `R`.
* `fork_L_ports`: for `e ∈ I'`, `Q_e ⊆ L1`, `e ∉ L1`, and the port replacements at `u`, `v`
  (even paths) and the new balanced pair at `w` (odd path).
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V25

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

/-! ### Generic decomposition calculus -/

omit [Fintype V] in
/-- a decomposed set has its indicator in the lattice -/
lemma ind_mem_lattice_of_dec {J : Finset (Sym2 V)} {D : Finset (Finset V)}
    (h : IsDecomposition G lab F J D) : ind J ∈ lattice G lab F := by
  rw [← h.2.2, ind_biUnion h.2.1]
  exact Submodule.sum_mem _ fun T hT => ind_mem_lattice (h.1 T hT)

omit [Fintype V] in
lemma triEdges_subset_of_dec {J : Finset (Sym2 V)} {D : Finset (Finset V)}
    (h : IsDecomposition G lab F J D) {T : Finset V} (hT : T ∈ D) : triEdges T ⊆ J := by
  rw [← h.2.2]; exact subset_biUnion_of_mem _ hT

omit [Fintype V] in
/-- decompositions of pairwise disjoint pieces combine -/
lemma isDecomposition_biUnion {ι : Type*} {S : Finset ι} {J : ι → Finset (Sym2 V)}
    {D : ι → Finset (Finset V)} (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (J i) (J j))
    (hD : ∀ i ∈ S, IsDecomposition G lab F (J i) (D i)) :
    IsDecomposition G lab F (S.biUnion J) (S.biUnion D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, hi, hT⟩ := mem_biUnion.1 hT
    exact (hD i hi).1 T hT
  · intro T hT T' hT' hne
    obtain ⟨i, hi, hT⟩ := mem_biUnion.1 (mem_coe.1 hT)
    obtain ⟨j, hj, hT'⟩ := mem_biUnion.1 (mem_coe.1 hT')
    by_cases hij : i = j
    · subst hij; exact (hD i hi).2.1 (mem_coe.2 hT) (mem_coe.2 hT') hne
    · exact (hdisj i hi j hj hij).mono (triEdges_subset_of_dec (hD i hi) hT)
        (triEdges_subset_of_dec (hD j hj) hT')
  · rw [biUnion_biUnion]
    exact biUnion_congr rfl fun i hi => (hD i hi).2.2

omit [Fintype V] in
/-- decompositions of two disjoint sets combine -/
lemma isDecomposition_union {J1 J2 : Finset (Sym2 V)} {D1 D2 : Finset (Finset V)}
    (h : Disjoint J1 J2) (h1 : IsDecomposition G lab F J1 D1)
    (h2 : IsDecomposition G lab F J2 D2) : IsDecomposition G lab F (J1 ∪ J2) (D1 ∪ D2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases mem_union.1 hT with hT | hT
    · exact h1.1 T hT
    · exact h2.1 T hT
  · intro T hT T' hT' hne
    rcases mem_union.1 (mem_coe.1 hT) with hT | hT <;>
      rcases mem_union.1 (mem_coe.1 hT') with hT' | hT'
    · exact h1.2.1 (mem_coe.2 hT) (mem_coe.2 hT') hne
    · exact h.mono (triEdges_subset_of_dec h1 hT) (triEdges_subset_of_dec h2 hT')
    · exact h.symm.mono (triEdges_subset_of_dec h2 hT) (triEdges_subset_of_dec h1 hT')
    · exact h2.2.1 (mem_coe.2 hT) (mem_coe.2 hT') hne
  · rw [union_biUnion, h1.2.2, h2.2.2]

/-! ### Mode pieces of a fork system -/

/-- the free halves `Q(I') = ⋃_{e ∈ I'} Q_e` -/
def QU (fk : Sym2 V → Fork V) (I' : Finset (Sym2 V)) : Finset (Sym2 V) :=
  I'.biUnion fun e => (fk e).Q

/-- the mode piece of `e`: active `{e} ∪ B_e` if `e ∈ I'`, basal `E_e` otherwise -/
def piece (fk : Sym2 V → Fork V) (I' : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  if e ∈ I' then insert e (fk e).B else (fk e).E

/-- the decomposition chosen by the modes -/
def modeDec (fk : Sym2 V → Fork V) (Xz I' : Finset (Sym2 V)) : Finset (Finset V) :=
  Xz.biUnion fun e => if e ∈ I' then {(fk e).T0} else {(fk e).T1, (fk e).T2}

omit [Fintype V] in
lemma piece_subset {I' : Finset (Sym2 V)} {e : Sym2 V} :
    piece fk I' e ⊆ insert e (fk e).E := by
  unfold piece
  split_ifs
  · exact insert_subset_insert _ subset_union_left
  · exact subset_insert _ _

section system

variable {X P : Finset (Sym2 V)} {fk : Sym2 V → Fork V} (hFS : ForkSystem G lab F W X P fk)
include hFS

lemma ForkSystem.E_disj_X {e : Sym2 V} (he : e ∈ XZ X W) : Disjoint (fk e).E X :=
  (hFS.2.2 e he).mono_right subset_union_left

lemma ForkSystem.R_disj_X : Disjoint (forkUnion (XZ X W) fk) X := by
  rw [forkUnion, disjoint_biUnion_left]
  exact fun e he => hFS.E_disj_X he

lemma ForkSystem.insert_disj {e e' : Sym2 V} (he : e ∈ XZ X W) (he' : e' ∈ XZ X W)
    (hne : e ≠ e') : Disjoint (insert e (fk e).E) (insert e' (fk e').E) := by
  have heX : e ∈ X := XZ_subset X W he
  have he'X : e' ∈ X := XZ_subset X W he'
  rw [disjoint_insert_left, disjoint_insert_right]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_insert]
    rintro (h | h)
    · exact hne h
    · exact disjoint_left.1 (hFS.E_disj_X he') h heX
  · intro h; exact disjoint_left.1 (hFS.E_disj_X he) h he'X
  · exact hFS.2.1 e he e' he' hne

lemma ForkSystem.piece_dec {I' : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ XZ X W) :
    IsDecomposition G lab F (piece fk I' e)
      (if e ∈ I' then {(fk e).T0} else {(fk e).T1, (fk e).T2}) := by
  obtain ⟨hroot, hv⟩ := hFS.1 e he
  unfold piece
  split_ifs
  · have := hv.active_mode.2.2.2; rwa [hroot] at this
  · exact hv.basal_mode.2.2

/-- the union of the mode pieces is `(R ∖ Q(I')) ∪ I'` -/
lemma ForkSystem.biUnion_piece {I' : Finset (Sym2 V)} (hI : I' ⊆ XZ X W) :
    (XZ X W).biUnion (piece fk I') = (forkUnion (XZ X W) fk \ QU fk I') ∪ I' := by
  have hBQ : ∀ e ∈ XZ X W, Disjoint (fk e).B (fk e).Q := fun e he =>
    ((hFS.1 e he).2.active_mode).2.2.1
  ext x
  simp only [mem_biUnion, mem_union, mem_sdiff, forkUnion, QU, piece, not_exists, not_and]
  constructor
  · rintro ⟨e, he, hx⟩
    split_ifs at hx with heI
    · rcases mem_insert.1 hx with rfl | hx
      · exact Or.inr heI
      · refine Or.inl ⟨⟨e, he, mem_union_left _ hx⟩, fun e' he'I hxe' => ?_⟩
        by_cases hee : e' = e
        · subst hee; exact disjoint_left.1 (hBQ e' he) hx hxe'
        · exact disjoint_left.1 (hFS.2.1 e he e' (hI he'I) (Ne.symm hee))
            (mem_union_left _ hx) (mem_union_right _ hxe')
    · refine Or.inl ⟨⟨e, he, hx⟩, fun e' he'I hxe' => ?_⟩
      have hee : e ≠ e' := fun h => heI (h ▸ he'I)
      exact disjoint_left.1 (hFS.2.1 e he e' (hI he'I) hee) hx (mem_union_right _ hxe')
  · rintro (⟨⟨e, he, hx⟩, hnot⟩ | hxI)
    · refine ⟨e, he, ?_⟩
      split_ifs with heI
      · refine mem_insert_of_mem ?_
        rcases mem_union.1 hx with hx | hx
        · exact hx
        · exact absurd hx (hnot e heI)
      · exact hx
    · exact ⟨x, hI hxI, by rw [if_pos hxI]; exact mem_insert_self _ _⟩

/-- **positive modes for every `I' ⊆ XZ`** -/
theorem ForkSystem.fork_modes {I' : Finset (Sym2 V)} (hI : I' ⊆ XZ X W) :
    IsDecomposition G lab F ((forkUnion (XZ X W) fk \ QU fk I') ∪ I') (modeDec fk (XZ X W) I') ∧
      QU fk I' ⊆ forkUnion (XZ X W) fk ∧
      Disjoint (QU fk I') ((forkUnion (XZ X W) fk \ QU fk I') ∪ I') := by
  have hQR : QU fk I' ⊆ forkUnion (XZ X W) fk := by
    intro x hx
    obtain ⟨e, he, hx⟩ := mem_biUnion.1 hx
    exact mem_biUnion.2 ⟨e, hI he, mem_union_right _ hx⟩
  refine ⟨?_, hQR, ?_⟩
  · rw [← hFS.biUnion_piece hI, modeDec]
    refine isDecomposition_biUnion (fun e he e' he' hne => ?_) (fun e he => hFS.piece_dec he)
    exact (hFS.insert_disj he he' hne).mono piece_subset piece_subset
  · rw [disjoint_union_right]
    refine ⟨disjoint_sdiff, ?_⟩
    exact (hFS.R_disj_X.mono hQR (hI.trans (XZ_subset X W)))

/-! ### The later choice `L ⊆ X` -/

/-- **the reduction of an arbitrary `L ⊆ X`** through the prebuilt forks -/
theorem ForkSystem.fork_L {L : Finset (Sym2 V)} (hL : L ⊆ X) :
    let I' := L ∩ XZ X W
    let R := forkUnion (XZ X W) fk
    let L1 := (L \ I') ∪ QU fk I'
    let X1 := (X \ XZ X W) ∪ QU fk (XZ X W)
    L ∪ R = L1 ∪ ((R \ QU fk I') ∪ I') ∧ Disjoint L1 ((R \ QU fk I') ∪ I') ∧
      (∀ D1, IsDecomposition G lab F L1 D1 →
        IsDecomposition G lab F (L ∪ R) (D1 ∪ modeDec fk (XZ X W) I')) ∧
      ind L - ind L1 ∈ lattice G lab F ∧
      L1 ⊆ X1 ∧ (∀ e ∈ X1, ∃ x ∈ e, x ∈ W) ∧
      (∀ x, degIn X1 x ≤ degIn X x + degIn R x) := by
  intro I' R L1 X1
  have hI : I' ⊆ XZ X W := inter_subset_right
  obtain ⟨hdec, hQR, hQdisj⟩ := hFS.fork_modes hI
  have hRX := hFS.R_disj_X
  have hRL : Disjoint R L := hRX.mono_right hL
  have hIL : I' ⊆ L := inter_subset_left
  -- the set identity
  have hset : L ∪ R = L1 ∪ ((R \ QU fk I') ∪ I') := by
    ext x
    simp only [L1, mem_union, mem_sdiff]
    constructor
    · rintro (hx | hx)
      · by_cases hxI : x ∈ I'
        · exact Or.inr (Or.inr hxI)
        · exact Or.inl (Or.inl ⟨hx, hxI⟩)
      · by_cases hxQ : x ∈ QU fk I'
        · exact Or.inl (Or.inr hxQ)
        · exact Or.inr (Or.inl ⟨hx, hxQ⟩)
    · rintro ((⟨hx, -⟩ | hx) | (⟨hx, -⟩ | hx))
      · exact Or.inl hx
      · exact Or.inr (hQR hx)
      · exact Or.inr hx
      · exact Or.inl (hIL hx)
  have hdisj : Disjoint L1 ((R \ QU fk I') ∪ I') := by
    rw [disjoint_union_left]
    refine ⟨?_, hQdisj⟩
    rw [disjoint_union_right]
    refine ⟨(hRL.symm.mono_left sdiff_subset).mono_right sdiff_subset, ?_⟩
    exact sdiff_disjoint
  refine ⟨hset, hdisj, fun D1 hD1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hset]; exact isDecomposition_union hdisj hD1 hdec
  · -- `1_L + 1_R = 1_{L1} + 1_{dec}`, and `1_R` is itself decomposed (all basal)
    have h1 : ind L + ind R = ind L1 + ind ((R \ QU fk I') ∪ I') := by
      rw [← ind_union_of_disjoint hRL.symm, hset, ind_union_of_disjoint hdisj]
    have hR : ind R ∈ lattice G lab F := by
      have := (hFS.fork_modes (I' := ∅) (empty_subset _)).1
      simp only [QU, biUnion_empty, sdiff_empty, union_empty] at this
      exact ind_mem_lattice_of_dec this
    have hD := ind_mem_lattice_of_dec hdec
    have : ind L - ind L1 = ind ((R \ QU fk I') ∪ I') - ind R := by
      rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
    rw [this]; exact Submodule.sub_mem _ hD hR
  · intro x hx
    simp only [L1, X1, mem_union, mem_sdiff] at hx ⊢
    rcases hx with ⟨hxL, hxI⟩ | hx
    · exact Or.inl ⟨hL hxL, fun h => hxI (mem_inter.2 ⟨hxL, h⟩)⟩
    · obtain ⟨e, he, hx⟩ := mem_biUnion.1 hx
      exact Or.inr (mem_biUnion.2 ⟨e, hI he, hx⟩)
  · intro e he
    rcases mem_union.1 he with he | he
    · obtain ⟨heX, heZ⟩ := mem_sdiff.1 he
      by_contra hc
      push_neg at hc
      exact heZ (mem_XZ.2 ⟨heX, hc⟩)
    · obtain ⟨e', he', he⟩ := mem_biUnion.1 he
      exact (hFS.1 e' he').2.Q_meets_W e he
  · intro x
    have hX1 : X1 ⊆ X ∪ R := by
      intro e he
      rcases mem_union.1 he with he | he
      · exact mem_union_left _ (mem_sdiff.1 he).1
      · obtain ⟨e', he', he⟩ := mem_biUnion.1 he
        exact mem_union_right _ (mem_biUnion.2 ⟨e', he', mem_union_right _ he⟩)
    exact (degIn_mono hX1 x).trans (degIn_union_le X R x)

/-- **local admissibility of `L1` via the two even paths** (and the odd path at `w`) -/
theorem ForkSystem.fork_L_ports {L : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ L ∩ XZ X W) :
    (fk e).Q ⊆ (L \ (L ∩ XZ X W)) ∪ QU fk (L ∩ XZ X W) ∧
      e ∉ (L \ (L ∩ XZ X W)) ∪ QU fk (L ∩ XZ X W) ∧
      (fk e).root = e ∧
      (comp G lab F (fk e).u (fk e).a = comp G lab F (fk e).u (fk e).v ∧
        (IsBip G lab F ((fk e).u, comp G lab F (fk e).u (fk e).v) →
          colG G lab F (fk e).u (fk e).a = colG G lab F (fk e).u (fk e).v)) ∧
      (comp G lab F (fk e).v (fk e).b = comp G lab F (fk e).v (fk e).u ∧
        (IsBip G lab F ((fk e).v, comp G lab F (fk e).v (fk e).u) →
          colG G lab F (fk e).v (fk e).b = colG G lab F (fk e).v (fk e).u)) ∧
      (comp G lab F (fk e).w (fk e).b = comp G lab F (fk e).w (fk e).a ∧
        (IsBip G lab F ((fk e).w, comp G lab F (fk e).w (fk e).a) →
          colG G lab F (fk e).w (fk e).b ≠ colG G lab F (fk e).w (fk e).a)) := by
  have heZ : e ∈ XZ X W := (mem_inter.1 he).2
  obtain ⟨hroot, hv⟩ := hFS.1 e heZ
  refine ⟨fun x hx => mem_union_right _ (mem_biUnion.2 ⟨e, he, hx⟩), ?_, hroot, hv.port_u,
    hv.port_v, hv.port_w⟩
  rintro hx
  rcases mem_union.1 hx with hx | hx
  · exact (mem_sdiff.1 hx).2 he
  · obtain ⟨e', he', hx⟩ := mem_biUnion.1 hx
    have hR : e ∈ (fk e').E := mem_union_right _ hx
    exact disjoint_left.1 (hFS.E_disj_X (mem_inter.1 he').2) hR
      (XZ_subset X W heZ)

end system

end S07V26

end
