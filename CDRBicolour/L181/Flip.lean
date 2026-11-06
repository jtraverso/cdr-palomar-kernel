/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Counting
public import CDRBicolour.L181.DegTwo

/-!
# L181: flipping a closed set of rows

Fix two colours `p ≠ x` and the transposition `τ = (p x)`.  For a set `Z` of rows, `flipCol`
applies `τ` to the colour of every edge meeting `Z`, and `flipM` applies `τ` to the pairs of
the rows of `Z`.

* If `Z` is closed under `p`/`x` edges (`KempeClosed`), the new colouring is proper, the
  missing set of a row of `Z` is the image under `τ` of the old one, and the other rows are
  unchanged (`miss_flip`).  This is the BBC part of the port operator: `Z` is a union of
  `p`/`x` Kempe components.
* If moreover `Z` is closed under links (`LinkClosed`: old pairs `pz`, `xz` in different rows),
  the new pairs are still pairwise disjoint (`pairDisjoint_flip`).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

/-! ### Partial pairings -/

/-- `M` is a partial pairing of `S`: non-degenerate pairs inside `S`, pairwise disjoint. -/
def IsPartialPairing (M : Finset (Sym2 Cl)) (S : Finset Cl) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ S) ∧
    (∀ e ∈ M, ∀ f ∈ M, ∀ v, v ∈ e → v ∈ f → e = f)

theorem isPartialPairing_of_perfect {M : Finset (Sym2 Cl)} {S : Finset Cl}
    (h : IsPerfectPairing M S) : IsPartialPairing M S :=
  ⟨h.1, h.2.1, fun e he f hf v hve hvf => by
    obtain ⟨g, _, hg⟩ := h.2.2 v (h.2.1 e he v hve)
    exact (hg e ⟨he, hve⟩).trans (hg f ⟨hf, hvf⟩).symm⟩

/-- Points covered by a set of pairs. -/
def cover (M : Finset (Sym2 Cl)) : Finset Cl := M.biUnion Sym2.toFinset

theorem mem_cover {M : Finset (Sym2 Cl)} {v : Cl} : v ∈ cover M ↔ ∃ e ∈ M, v ∈ e := by
  simp [cover, Sym2.mem_toFinset]

/-! ### The transposition -/

section Swap

variable (p x : Cl)

theorem mem_image_swap {s : Finset Cl} {v : Cl} :
    v ∈ s.image (Equiv.swap p x) ↔ Equiv.swap p x v ∈ s := by
  constructor
  · intro h; obtain ⟨u, hu, rfl⟩ := mem_image.1 h; simpa using hu
  · intro h; exact mem_image.2 ⟨_, h, by simp⟩

theorem map_swap_map_swap (e : Sym2 Cl) :
    Sym2.map (Equiv.swap p x) (Sym2.map (Equiv.swap p x) e) = e := by
  refine Sym2.ind (fun a b => ?_) e
  simp [Sym2.map_mk]

theorem mem_map_swap {e : Sym2 Cl} {v : Cl} :
    v ∈ Sym2.map (Equiv.swap p x) e ↔ Equiv.swap p x v ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨_, h, by simp⟩

theorem mem_image_map_swap {M : Finset (Sym2 Cl)} {e : Sym2 Cl} :
    e ∈ M.image (Sym2.map (Equiv.swap p x)) ↔ Sym2.map (Equiv.swap p x) e ∈ M := by
  constructor
  · intro h; obtain ⟨f, hf, rfl⟩ := mem_image.1 h; rwa [map_swap_map_swap]
  · intro h; exact mem_image.2 ⟨_, h, map_swap_map_swap p x e⟩

theorem map_swap_of_not_mem {e : Sym2 Cl} (hp : p ∉ e) (hx : x ∉ e) :
    Sym2.map (Equiv.swap p x) e = e := by
  revert hp hx
  refine Sym2.ind (fun a b => ?_) e
  intro hp hx
  simp only [Sym2.mem_iff, not_or] at hp hx
  rw [Sym2.map_mk, Equiv.swap_apply_of_ne_of_ne (Ne.symm hp.1) (Ne.symm hx.1),
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hp.2) (Ne.symm hx.2)]

theorem not_isDiag_map_swap {e : Sym2 Cl} (h : ¬ e.IsDiag) :
    ¬ (Sym2.map (Equiv.swap p x) e).IsDiag := by
  revert h
  refine Sym2.ind (fun a b => ?_) e
  intro h
  rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
  rw [Sym2.mk_isDiag_iff] at h
  intro h'; exact h ((Equiv.swap p x).injective h')

/-- A non-degenerate pair is fixed by `τ`, or it is `pz`/`xz` with `z ∉ {p,x}`. -/
theorem map_swap_cases (hpx : p ≠ x) {a b : Cl} (hab : a ≠ b) :
    Sym2.map (Equiv.swap p x) s(a, b) = s(a, b) ∨
      ∃ z, z ≠ p ∧ z ≠ x ∧
        ((s(a, b) = s(p, z) ∧ Sym2.map (Equiv.swap p x) s(a, b) = s(x, z)) ∨
          (s(a, b) = s(x, z) ∧ Sym2.map (Equiv.swap p x) s(a, b) = s(p, z))) := by
  rw [Sym2.map_mk]
  by_cases ha : a = p
  · subst ha
    by_cases hb : b = x
    · subst hb; left; simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Sym2.eq_swap]
    · right
      refine ⟨b, Ne.symm hab, hb, Or.inl ⟨rfl, ?_⟩⟩
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hb]
  · by_cases ha' : a = x
    · subst ha'
      by_cases hb : b = p
      · subst hb; left; simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Sym2.eq_swap]
      · right
        refine ⟨b, hb, Ne.symm hab, Or.inr ⟨rfl, ?_⟩⟩
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hb (Ne.symm hab)]
    · by_cases hb : b = p
      · subst hb
        right
        refine ⟨a, ha, ha', Or.inl ⟨Sym2.eq_swap, ?_⟩⟩
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne ha ha', Sym2.eq_swap]
      · by_cases hb' : b = x
        · subst hb'
          right
          refine ⟨a, ha, ha', Or.inr ⟨Sym2.eq_swap, ?_⟩⟩
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne ha ha', Sym2.eq_swap]
        · left
          rw [Equiv.swap_apply_of_ne_of_ne ha ha', Equiv.swap_apply_of_ne_of_ne hb hb']

theorem isPartialPairing_image_swap {M : Finset (Sym2 Cl)} {S : Finset Cl}
    (h : IsPartialPairing M S) :
    IsPartialPairing (M.image (Sym2.map (Equiv.swap p x))) (S.image (Equiv.swap p x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.1 he
    exact not_isDiag_map_swap p x (h.1 f hf)
  · intro e he v hv
    rw [mem_image_map_swap] at he
    rw [mem_image_swap]
    exact h.2.1 _ he _ ((mem_map_swap p x).1 (by rwa [map_swap_map_swap]))
  · intro e he f hf v hve hvf
    rw [mem_image_map_swap] at he hf
    have h1 : Equiv.swap p x v ∈ Sym2.map (Equiv.swap p x) e := by
      rw [mem_map_swap]; simpa using hve
    have h2 : Equiv.swap p x v ∈ Sym2.map (Equiv.swap p x) f := by
      rw [mem_map_swap]; simpa using hvf
    have := h.2.2 _ he _ hf _ h1 h2
    have := congrArg (Sym2.map (Equiv.swap p x)) this
    rwa [map_swap_map_swap, map_swap_map_swap] at this

theorem isPerfectPairing_image_swap {M : Finset (Sym2 Cl)} {S : Finset Cl}
    (h : IsPerfectPairing M S) :
    IsPerfectPairing (M.image (Sym2.map (Equiv.swap p x))) (S.image (Equiv.swap p x)) := by
  have hp := isPartialPairing_image_swap p x (isPartialPairing_of_perfect h)
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro v hv
  rw [mem_image_swap] at hv
  obtain ⟨f, ⟨hf, hvf⟩, _⟩ := h.2.2 _ hv
  refine ⟨Sym2.map (Equiv.swap p x) f, ⟨mem_image.2 ⟨f, hf, rfl⟩, ?_⟩, ?_⟩
  · rw [mem_map_swap]; exact hvf
  · rintro e ⟨he, hve⟩
    exact hp.2.2 e he _ (mem_image.2 ⟨f, hf, rfl⟩) v hve (by rw [mem_map_swap]; exact hvf)

theorem cover_image_swap (M : Finset (Sym2 Cl)) :
    cover (M.image (Sym2.map (Equiv.swap p x))) = (cover M).image (Equiv.swap p x) := by
  ext v
  rw [mem_image_swap, mem_cover, mem_cover]
  constructor
  · rintro ⟨e, he, hve⟩
    rw [mem_image_map_swap] at he
    exact ⟨_, he, by rw [mem_map_swap]; simpa using hve⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨Sym2.map (Equiv.swap p x) e, mem_image.2 ⟨e, he, rfl⟩, by rw [mem_map_swap]; exact hve⟩

end Swap

/-! ### Flipping a set of rows -/

section Flip

variable (G : SimpleGraph Rw) [DecidableRel G.Adj] (p x : Cl) (Z : Finset Rw)

/-- Apply `τ` to the colour of every edge meeting `Z`. -/
def flipCol (χ : Sym2 Rw → Cl) (e : Sym2 Rw) : Cl :=
  if ∃ j ∈ Z, j ∈ e then Equiv.swap p x (χ e) else χ e

/-- Apply `τ` to the pairs of the rows of `Z`. -/
def flipM (M : Rw → Finset (Sym2 Cl)) (j : Rw) : Finset (Sym2 Cl) :=
  if j ∈ Z then (M j).image (Sym2.map (Equiv.swap p x)) else M j

/-- `Z` is closed under the edges coloured `p` or `x`. -/
def KempeClosed (χ : Sym2 Rw → Cl) : Prop :=
  ∀ j j', G.Adj j j' → (χ s(j, j') = p ∨ χ s(j, j') = x) → j ∈ Z → j' ∈ Z

/-- `Z` is closed under links: old pairs `pz` and `xz` owned by different rows. -/
def LinkClosed (M : Rw → Finset (Sym2 Cl)) : Prop :=
  ∀ j j' z, j ≠ j' → s(p, z) ∈ M j → s(x, z) ∈ M j' → (j ∈ Z ↔ j' ∈ Z)

variable {G p x Z}

theorem flipCol_adj {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) {j j' : Rw}
    (h : G.Adj j j') :
    flipCol p x Z χ s(j, j') =
      if j ∈ Z then Equiv.swap p x (χ s(j, j')) else χ s(j, j') := by
  unfold flipCol
  by_cases hj : j ∈ Z
  · rw [if_pos ⟨j, hj, Sym2.mem_mk_left _ _⟩, if_pos hj]
  · rw [if_neg hj]
    split_ifs with hex
    · obtain ⟨i, hi, hie⟩ := hex
      have hij : i = j' := by
        rcases Sym2.mem_iff.1 hie with h1 | h1
        · exact absurd (h1 ▸ hi) hj
        · exact h1
      subst hij
      have hc : ¬ (χ s(j, i) = p ∨ χ s(j, i) = x) := by
        intro hc
        apply hj
        exact hZ i j h.symm (by rw [Sym2.eq_swap]; exact hc) hi
      push_neg at hc
      exact Equiv.swap_apply_of_ne_of_ne hc.1 hc.2
    · rfl

theorem flipCol_incident {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) {j : Rw}
    {e : Sym2 Rw} (he : e ∈ G.incidenceFinset j) :
    flipCol p x Z χ e = if j ∈ Z then Equiv.swap p x (χ e) else χ e := by
  rw [SimpleGraph.mem_incidenceFinset] at he
  obtain ⟨heE, hje⟩ := he
  obtain ⟨j', rfl⟩ := Sym2.mem_iff_exists.1 hje
  exact flipCol_adj hZ ((SimpleGraph.mem_edgeSet G).1 heE)

theorem present_flip {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) (j : Rw) :
    present G (flipCol p x Z χ) j =
      if j ∈ Z then (present G χ j).image (Equiv.swap p x) else present G χ j := by
  unfold present
  rw [Finset.image_congr (g := fun e => if j ∈ Z then Equiv.swap p x (χ e) else χ e)
    (fun e he => flipCol_incident hZ he)]
  split_ifs with hj
  · rw [image_image]; rfl
  · rfl

theorem miss_flip {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) (j : Rw) :
    miss G (flipCol p x Z χ) j =
      if j ∈ Z then (miss G χ j).image (Equiv.swap p x) else miss G χ j := by
  unfold miss
  rw [present_flip hZ]
  split_ifs with hj
  · ext v
    rw [mem_image_swap]
    simp only [mem_sdiff, mem_univ, true_and]
    rw [mem_image_swap]
  · rfl

theorem mem_miss_flip {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) (j : Rw) (v : Cl) :
    v ∈ miss G (flipCol p x Z χ) j ↔
      (j ∈ Z ∧ Equiv.swap p x v ∈ miss G χ j) ∨ (j ∉ Z ∧ v ∈ miss G χ j) := by
  rw [miss_flip hZ]
  split_ifs with hj
  · rw [mem_image_swap]; simp [hj]
  · simp [hj]

theorem properOn_flip {χ : Sym2 Rw → Cl} (hχ : ProperOn G.edgeFinset χ)
    (hZ : KempeClosed G p x Z χ) : ProperOn G.edgeFinset (flipCol p x Z χ) := by
  intro e he f hf hne hsame
  by_contra hdis
  rw [Finset.not_disjoint_iff] at hdis
  obtain ⟨j, hje, hjf⟩ := hdis
  rw [Sym2.mem_toFinset] at hje hjf
  have hei : e ∈ G.incidenceFinset j :=
    SimpleGraph.mem_incidenceFinset.2 ⟨SimpleGraph.mem_edgeFinset.1 he, hje⟩
  have hfi : f ∈ G.incidenceFinset j :=
    SimpleGraph.mem_incidenceFinset.2 ⟨SimpleGraph.mem_edgeFinset.1 hf, hjf⟩
  rw [flipCol_incident hZ hei, flipCol_incident hZ hfi] at hsame
  have hs : χ e = χ f := by
    split_ifs at hsame
    · exact (Equiv.swap p x).injective hsame
    · exact hsame
  have := hχ e he f hf hne hs
  exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 hje) (Sym2.mem_toFinset.2 hjf)

theorem avoid_flip {χ : Sym2 Rw → Cl} {W : Finset Cl} (hp : p ∉ W) (hx : x ∉ W)
    (hav : ∀ e ∈ G.edgeFinset, χ e ∉ W) : ∀ e ∈ G.edgeFinset, flipCol p x Z χ e ∉ W := by
  intro e he
  unfold flipCol
  split_ifs
  · by_cases h1 : χ e = p
    · rw [h1, Equiv.swap_apply_left]; exact hx
    · by_cases h2 : χ e = x
      · rw [h2, Equiv.swap_apply_right]; exact hp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hav e he
  · exact hav e he

/-- Multiplicities after the flip: `mult' v + #{Z ∋ v} = mult v + #{Z ∋ τ v}`. -/
theorem mult_flip {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) (v : Cl) :
    mult G (flipCol p x Z χ) v + (Z.filter fun j => v ∈ miss G χ j).card =
      mult G χ v + (Z.filter fun j => Equiv.swap p x v ∈ miss G χ j).card := by
  unfold mult
  have hsplit : ∀ P : Rw → Prop, [DecidablePred P] →
      (univ.filter P).card = (Z.filter P).card + (univ.filter fun j => j ∉ Z ∧ P j).card := by
    intro P _
    have h := card_filter_add_card_filter_not (s := univ.filter P) (fun j => j ∈ Z)
    rw [filter_filter, filter_filter] at h
    rw [← h]
    congr 1
    · congr 1; ext j; simp [and_comm]
    · congr 1; ext j; simp [and_comm]
  rw [hsplit (fun j => v ∈ miss G (flipCol p x Z χ) j), hsplit (fun j => v ∈ miss G χ j)]
  have h1 : (Z.filter fun j => v ∈ miss G (flipCol p x Z χ) j) =
      Z.filter fun j => Equiv.swap p x v ∈ miss G χ j := by
    ext j; simp only [mem_filter, mem_miss_flip hZ]
    constructor
    · rintro ⟨hj, (⟨_, h⟩ | ⟨h, _⟩)⟩
      · exact ⟨hj, h⟩
      · exact absurd hj h
    · rintro ⟨hj, h⟩; exact ⟨hj, Or.inl ⟨hj, h⟩⟩
  have h2 : (univ.filter fun j => j ∉ Z ∧ v ∈ miss G (flipCol p x Z χ) j) =
      univ.filter fun j => j ∉ Z ∧ v ∈ miss G χ j := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_miss_flip hZ]
    constructor
    · rintro ⟨hj, (⟨h, _⟩ | ⟨_, h⟩)⟩
      · exact absurd h hj
      · exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, Or.inr ⟨hj, h⟩⟩
  rw [h1, h2]
  omega

theorem mult_flip_of_ne {χ : Sym2 Rw → Cl} (hZ : KempeClosed G p x Z χ) {v : Cl} (hp : v ≠ p)
    (hx : v ≠ x) : mult G (flipCol p x Z χ) v = mult G χ v := by
  have := mult_flip hZ v
  rw [Equiv.swap_apply_of_ne_of_ne hp hx] at this
  omega

theorem flipM_of_not_mem {M : Rw → Finset (Sym2 Cl)} {j : Rw} (hj : j ∉ Z) :
    flipM p x Z M j = M j := if_neg hj

theorem flipM_of_mem {M : Rw → Finset (Sym2 Cl)} {j : Rw} (hj : j ∈ Z) :
    flipM p x Z M j = (M j).image (Sym2.map (Equiv.swap p x)) := if_pos hj

theorem isPartialPairing_flip {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hZ : KempeClosed G p x Z χ) {j : Rw} (h : IsPartialPairing (M j) (miss G χ j)) :
    IsPartialPairing (flipM p x Z M j) (miss G (flipCol p x Z χ) j) := by
  rw [miss_flip hZ]
  unfold flipM
  split_ifs
  · exact isPartialPairing_image_swap p x h
  · exact h

theorem isPerfectPairing_flip {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hZ : KempeClosed G p x Z χ) {j : Rw} (h : IsPerfectPairing (M j) (miss G χ j)) :
    IsPerfectPairing (flipM p x Z M j) (miss G (flipCol p x Z χ) j) := by
  rw [miss_flip hZ]
  unfold flipM
  split_ifs
  · exact isPerfectPairing_image_swap p x h
  · exact h

theorem pairDisjoint_flip (hpx : p ≠ x) {M : Rw → Finset (Sym2 Cl)}
    (hnd : ∀ j, ∀ e ∈ M j, ¬ e.IsDiag) (hd : PairDisjoint M) (hL : LinkClosed p x Z M) :
    PairDisjoint (flipM p x Z M) := by
  -- a pair moved out of `Z` cannot meet a row outside `Z`
  have key : ∀ j j', j ∈ Z → j' ∉ Z → j ≠ j' → ∀ e ∈ M j,
      Sym2.map (Equiv.swap p x) e ∉ M j' := by
    intro j j' hj hj' hne e he
    have hnd' := hnd j e he
    revert he hnd'
    refine Sym2.ind (fun a b => ?_) e
    intro he hnd' hmem
    rw [Sym2.mk_isDiag_iff] at hnd'
    rcases map_swap_cases p x hpx hnd' with h | ⟨z, -, -, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · rw [h] at hmem
      exact Finset.disjoint_left.1 (hd j j' hne) he hmem
    · rw [h2] at hmem; rw [h1] at he
      exact hj' ((hL j j' z hne he hmem).1 hj)
    · rw [h2] at hmem; rw [h1] at he
      exact hj' ((hL j' j z (Ne.symm hne) hmem he).2 hj)
  intro j j' hne
  rw [Finset.disjoint_left]
  intro e hej hej'
  by_cases hj : j ∈ Z <;> by_cases hj' : j' ∈ Z
  · rw [flipM_of_mem hj, mem_image_map_swap] at hej
    rw [flipM_of_mem hj', mem_image_map_swap] at hej'
    exact Finset.disjoint_left.1 (hd j j' hne) hej hej'
  · rw [flipM_of_mem hj, mem_image_map_swap] at hej
    rw [flipM_of_not_mem hj'] at hej'
    exact key j j' hj hj' hne _ hej (by rwa [map_swap_map_swap])
  · rw [flipM_of_not_mem hj] at hej
    rw [flipM_of_mem hj', mem_image_map_swap] at hej'
    exact key j' j hj' hj (Ne.symm hne) _ hej' (by rwa [map_swap_map_swap])
  · rw [flipM_of_not_mem hj] at hej
    rw [flipM_of_not_mem hj'] at hej'
    exact Finset.disjoint_left.1 (hd j j' hne) hej hej'

/-- Pairs avoiding `p` and `x` keep their owners. -/
theorem mem_flipM_of_not_mem {M : Rw → Finset (Sym2 Cl)} {e : Sym2 Cl} (hp : p ∉ e)
    (hx : x ∉ e) (j : Rw) : e ∈ flipM p x Z M j ↔ e ∈ M j := by
  unfold flipM
  split_ifs
  · rw [mem_image_map_swap, map_swap_of_not_mem p x hp hx]
  · rfl

/-- The `x`-pairs after the flip. -/
theorem mem_flipM_x {M : Rw → Finset (Sym2 Cl)} {r : Cl} (hrp : r ≠ p) (hrx : r ≠ x)
    (j : Rw) : s(x, r) ∈ flipM p x Z M j ↔
      (j ∈ Z ∧ s(p, r) ∈ M j) ∨ (j ∉ Z ∧ s(x, r) ∈ M j) := by
  unfold flipM
  split_ifs with hj
  · rw [mem_image_map_swap, Sym2.map_mk, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hrp hrx]
    simp [hj]
  · simp [hj]

end Flip

end CDRBicolour.L181
