/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Catalog
public import RequestProject.S07V42.Polarize
public import RequestProject.S07V31.TerminalAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §8 — native cell supply for the fixed catalog (step 5)

`native_cell_supply`: constants `t, Ecell, ε, n0` are fixed from
`(β, h, d, c, E, d', c', E', s, β₁)` BEFORE the host. For every host whose TRUE core subtype has
H3(β)/H4(β, h), every admissible `Z` (`|Z| ≤ coreDelta β h · |W|`), every active catalog entry,
either sign, and every forbidden `B` of maximum degree `≤ b ≤ ε |W|`, there are ACTUAL finite edge
sets `A, Y` with

* `A ∩ Y = ∅`, `(A ∪ Y) ∩ B = ∅`, no edge of `A ∪ Y` meets `Z`;
* every edge of `Y` is an edge of `H[W \ Z]` (so `Y` lies inside the fixed core `W`);
* `A` and `A ∪ Y` have allowed triangle decompositions in `H − Z` (hence in the original `H`,
  `isDecomposition_of_delG`);
* `|A ∪ Y| ≤ Ecell`;
* `[1_Y] = ± gCat v` in `Q` (edge-additive charge `chargeQ`).

Proof: `native_reroute` (step 4) gives `x`; `polarize` (integer polarization inside `W \ Z`) gives
`Y` with `1_Y − x ∈ Λ(H[W \ Z])`; then V31 `universal_terminal_absorber` (G2) is applied IN the
deleted host `H − Z` on the vertex set `support Y` with forbidden set `B`.

**Named inputs** (not constructed in this tree): the compression data `CoreCompression`,
`DelCompression` (G1-Z export shape) and the terminal supply `S07V31.TerminalSupply` of
`H − Z` on small vertex sets of `W \ Z` (the hypothesis of V31 `universal_terminal_absorber`).
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.Dispersal

variable {V I : Type*}

/-- a decomposition in `H − Z` is a decomposition in `H` -/
lemma isDecomposition_of_delG {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {Z : Finset V} {X : Finset (Sym2 V)} {D : Finset (Finset V)}
    (h : IsDecomposition (S07V39.delG H Z) lab F X D) : IsDecomposition H lab F X D :=
  ⟨fun T hT => S07V37.isAllowed_mono (S07V39.delG_le H Z) (h.1 T hT), h.2.1, h.2.2⟩

/-- edges of a set decomposable in `H − Z` avoid `Z` -/
lemma avoid_of_delG {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {Z : Finset V} {X : Finset (Sym2 V)} {D : Finset (Finset V)}
    (h : IsDecomposition (S07V39.delG H Z) lab F X D) : ∀ e ∈ X, ∀ z ∈ Z, z ∉ e := by
  intro e he z hz hze
  rw [← h.2.2, Finset.mem_biUnion] at he
  obtain ⟨T, hT, heT⟩ := he
  exact (S07V39.allowed_delG_iff.1 (h.1 T hT)).2 z (mem_of_mem_triEdges heT hze) hz

lemma l1E_neg [Fintype V] (x : Sym2 V → ℤ) : l1E (-x) = l1E x := by
  unfold l1E; simp

universe u v

/-- **Native cell supply for the fixed catalog.** -/
theorem native_cell_supply {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' s : ℕ) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) :
    ∃ (t Ecell : ℕ) (ε : ℝ), 0 < ε ∧ ∃ n0 : ℕ,
      ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
        {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → n0 ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ {Z : Finset V}, (Z.card : ℝ) ≤ coreDelta β h * W.card →
      DelCompression H lab F Z d' c' E' →
      (∀ U : Finset V, U ⊆ W \ Z → U.card ≤ t →
        S07V31.TerminalSupply (S07V39.delG H Z) lab F U s ⌊β₁ * Fintype.card V⌋₊
          ⌊β₁ * Fintype.card V⌋₊) →
      ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ x, degIn B x ≤ b) → (b : ℝ) ≤ ε * W.card →
      ∀ v : Cat d (catR β d c E d' c' E'),
        gCat C0 (catR β d c E d' c' E') v ∈ KZ H lab F W Z → ∀ σ : Bool,
      ∃ A Y : Finset (Sym2 V), Disjoint A Y ∧ Disjoint (A ∪ Y) B ∧
        (∀ e ∈ A ∪ Y, ∀ z ∈ Z, z ∉ e) ∧ (∀ e ∈ Y, e ∈ edges (indG H (W \ Z))) ∧
        (∃ D, IsDecomposition (S07V39.delG H Z) lab F A D) ∧
        (∃ D, IsDecomposition (S07V39.delG H Z) lab F (A ∪ Y) D) ∧
        (A ∪ Y).card ≤ Ecell ∧
        chargeQ H lab F W Y =
          (if σ then gCat C0 (catR β d c E d' c' E') v else -gCat C0 (catR β d c E d' c' E') v) := by
  obtain ⟨U, hU⟩ := native_reroute.{u, v} h hβ d c E d' c' E'
  set t := 8 * U with ht
  obtain ⟨εa, hεa, na, habs⟩ := S07V31.universal_terminal_absorber.{u, v} t s hβ₁
  refine ⟨t, s * 2 ^ (t * t) + 4 * U, min (β / 8) εa, lt_min (by positivity) hεa,
    na + ⌈40 * (U : ℝ) / β⌉₊ + 1, ?_⟩
  intro V _ I H lab F W hH3 hH4 hWc hWn C0 Z hZ CZ hsup B b hB hb v hv σ
  obtain ⟨x, hxM, hxL, hxU, hxc⟩ := hU hH3 hH4 hWc C0 hZ CZ v hv
  -- the signed vector
  set xs : Sym2 V → ℤ := if σ then x else -x with hxs
  have hxsM : xs ∈ MZ H lab F W Z := by
    rw [hxs]; split_ifs
    · exact hxM
    · exact neg_mem hxM
  have hxsL : xs ∈ LamDel H lab F Z := by
    rw [hxs]; split_ifs
    · exact hxL
    · exact neg_mem hxL
  have hxsU : l1E xs ≤ U := by
    rw [hxs]; split_ifs
    · exact hxU
    · rw [l1E_neg]; exact hxU
  have hxsc : clsQ H lab F W xs =
      (if σ then gCat C0 (catR β d c E d' c' E') v else -gCat C0 (catR β d c E d' c' E') v) := by
    rw [hxs]; split_ifs
    · exact hxc
    · rw [← hxc]; rfl
  -- room for polarization
  have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hZ' : (Z.card : ℝ) ≤ β / 2 * W.card :=
    hZ.trans (mul_le_mul_of_nonneg_right (coreDelta_le hβ h) hW0)
  have hb' : (b : ℝ) ≤ β / 8 * W.card :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)
  have hWbig : 40 * (U : ℝ) / β < W.card := by
    have h1 := Nat.le_ceil (40 * (U : ℝ) / β)
    have h2 : ((na + ⌈40 * (U : ℝ) / β⌉₊ + 1 : ℕ) : ℝ) ≤ W.card := by exact_mod_cast hWn
    push_cast at h2
    have : (0 : ℝ) ≤ na := Nat.cast_nonneg _
    linarith
  have hroom : 5 * (U : ℝ) + Z.card + 2 * b < β * W.card := by
    have : 40 * (U : ℝ) < β * W.card := by
      rw [div_lt_iff₀ hβ] at hWbig; linarith
    linarith
  obtain ⟨Y, hYL, hYB, hYE, hYc⟩ := polarize hH3 Z hB hxsM hxsU hroom
  -- physicality of `Y` in `H − Z`
  have hlatWD : lattice (indG H (W \ Z)) lab F ≤ LamDel H lab F Z :=
    S07V37.lattice_mono (indG_le_delG H Finset.sdiff_disjoint) lab F
  have hlatWC : lattice (indG H (W \ Z)) lab F ≤ LamCore H lab F W :=
    S07V37.lattice_mono (indG_mono H Finset.sdiff_subset) lab F
  have hYphys : ind Y ∈ lattice (S07V39.delG H Z) lab F := by
    have : ind Y = (ind Y - xs) + xs := by abel
    rw [this]; exact add_mem (hlatWD hYL) hxsL
  -- the terminal vertex set
  have hsuppW : support Y ⊆ W \ Z := by
    intro y hy
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨e, he, hye⟩ := hy
    have := hYE e he
    induction e using Sym2.ind with
    | h p q =>
      rw [mem_edges, SimpleGraph.mem_edgeSet] at this
      rw [Sym2.mem_iff] at hye
      rcases hye with rfl | rfl
      exacts [this.2.1, this.2.2]
  have hsuppc : (support Y).card ≤ t := by
    have := S07V28.card_support_le Y
    omega
  have hn0 : na ≤ Fintype.card V := by
    have : W.card ≤ Fintype.card V := Finset.card_le_univ W
    omega
  have hbV : (b : ℝ) ≤ εa * Fintype.card V := by
    have h1 : (W.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ W
    calc (b : ℝ) ≤ min (β / 8) εa * W.card := hb
      _ ≤ εa * W.card := mul_le_mul_of_nonneg_right (min_le_right _ _) hW0
      _ ≤ εa * Fintype.card V := mul_le_mul_of_nonneg_left h1 hεa.le
  obtain ⟨R, hRB, hRT, hRc, -, ⟨DR, hDR⟩, hRL⟩ := habs (S07V39.delG H Z) lab F (support Y) B b hn0
    hsuppc hB hbV (hsup _ hsuppW hsuppc)
  obtain ⟨DRY, hDRY⟩ := hRL Y hYphys subset_rfl
  have hYT : Y ⊆ triEdges (support Y) := S07V31.subset_triEdges_of_physical hYphys subset_rfl
  refine ⟨R, Y, hRT.mono_right hYT, Finset.disjoint_union_left.2 ⟨hRB, hYB⟩, ?_, hYE,
    ⟨DR, hDR⟩, ⟨DRY, hDRY⟩, ?_, ?_⟩
  · intro e he z hz
    rcases Finset.mem_union.1 he with h1 | h1
    · exact avoid_of_delG hDR e h1 z hz
    · intro hze
      have := hsuppW (mem_support_of_mem h1 hze)
      exact (Finset.mem_sdiff.1 this).2 hz
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hRc hYc)
  · rw [chargeQ_eq, ← hxsc]
    unfold clsQ
    exact (Submodule.Quotient.eq _).2 (hlatWC hYL)

end S07V42
