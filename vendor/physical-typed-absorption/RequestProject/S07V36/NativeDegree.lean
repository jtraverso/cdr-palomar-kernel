/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V36.NativeMatrix
@[expose] public section

/-!
# V36 — sizes, counts and degrees of the native matrix from the ORIGINAL H3

All statements assume only `CommonNbrCond G lab F α` (H3, unchanged), plus `0 < α` where a
division by `α` occurs.

* `side j c` — the colour class `c` of the chosen colouring inside the component of row `j`.
* `side_card_ge` — every side of every native row has `≥ α n` vertices (`n = card V`).
* `comp_card_ge` — every native row has `|K| ≥ 2 α n`.
* `card_rows_at_le` — at most `⌊1/(2α)⌋₊` native rows per root.
* `card_nrow_le` — at most `n ⌊1/(2α)⌋₊` native rows in total.
* `unanchored_partner` — for an unanchored row `(v, K)` and `u ∈ K`, the column `vu` has a
  second nonzero row, rooted at `u`.
* `card_comp_le_nbrs` — an unanchored row has at least `|K|` distinct neighbours in the V35
  `linkGraph` of the native matrix.
* `nbrs_ge_of_le` — any natural `m ≤ 2 α n` (in particular any `m ≤ α n`) is a valid degree
  bound for unanchored rows.
-/

open Finset Classical

noncomputable section

namespace S07V36

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
  TypedTriangle.ComponentCount

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- Colour class `c` inside the component of row `j`. -/
def side (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (j : Row V) (c : Bool) :
    Finset V :=
  j.2.filter (fun u => TypedTriangle.ComponentRows.col G lab F j u = c)

/-- **Both sides of a native row have at least `α n` vertices** (from H3). -/
theorem side_card_ge {α : ℝ} (hH3 : CommonNbrCond G lab F α) {j : Row V}
    (hj : IsNRow G lab F j) (c : Bool) : α * Fintype.card V ≤ (side G lab F j c).card := by
  -- a vertex `x ∈ K` with colour different from `c`
  obtain ⟨x, hxK, hxc⟩ : ∃ x ∈ j.2, TypedTriangle.ComponentRows.col G lab F j x ≠ c := by
    obtain ⟨a, ⟨w, haw⟩, ha⟩ := hj.1
    have haK : a ∈ j.2 := ha ▸ mem_comp_self G lab F _ a
    have hwK : w ∈ j.2 := by
      rw [← ha, mem_comp_iff]; exact haw.reachable
    have hne := col_proper hj.2 haK hwK haw
    by_cases h : TypedTriangle.ComponentRows.col G lab F j a = c
    · exact ⟨w, hwK, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨a, haK, h⟩
  have hdeg := S07V25.link_degree_ge hH3 j.1 x (linkActive_of_mem hj.1 hxK)
  have hsub : (link G lab F j.1).neighborFinset x ⊆ side G lab F j c := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyK : y ∈ j.2 := by
      rw [active_eq_comp hj.1 hxK, mem_comp_iff]; exact hy.reachable
    have hcol := col_proper hj.2 hxK hyK hy
    simp only [side, mem_filter]
    refine ⟨hyK, ?_⟩
    cases h1 : TypedTriangle.ComponentRows.col G lab F j y <;>
      cases h2 : TypedTriangle.ComponentRows.col G lab F j x <;> cases c <;> simp_all
  have := card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  exact hdeg.trans (by exact_mod_cast this)

omit [Fintype V] in
/-- The two sides partition the component. -/
lemma side_card_add (j : Row V) :
    (side G lab F j true).card + (side G lab F j false).card = j.2.card := by
  have := Finset.card_filter_add_card_filter_not
    (s := j.2) (fun u => TypedTriangle.ComponentRows.col G lab F j u = true)
  simpa [side] using this

/-- **Every native row has `|K| ≥ 2 α n`.** -/
theorem comp_card_ge {α : ℝ} (hH3 : CommonNbrCond G lab F α) {j : Row V}
    (hj : IsNRow G lab F j) : 2 * α * Fintype.card V ≤ j.2.card := by
  have h1 := side_card_ge hH3 hj true
  have h2 := side_card_ge hH3 hj false
  have h3 : ((side G lab F j true).card : ℝ) + (side G lab F j false).card = j.2.card := by
    exact_mod_cast side_card_add j
  linarith

/-- **At most `⌊1/(2α)⌋₊` native rows per root.** -/
theorem card_rows_at_le {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α) (v : V) :
    (univ.filter (fun j : NRow G lab F => j.1.1 = v)).card ≤ ⌊1 / (2 * α)⌋₊ := by
  set S := univ.filter (fun j : NRow G lab F => j.1.1 = v)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨v⟩
  -- the total size of the components of `S` is `≤ n`
  have hsum : ∑ j ∈ S, j.1.2.card ≤ Fintype.card V := by
    have hmap : ∑ j ∈ S, j.1.2.card = ∑ r ∈ S.map (Function.Embedding.subtype _), r.2.card := by
      rw [Finset.sum_map]; rfl
    rw [hmap]
    refine le_trans (Finset.sum_le_sum_of_subset ?_) (sum_card_activeRowsAt_le G lab F v)
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hr
    rw [mem_activeRowsAt]
    exact ⟨(mem_filter.1 hj).2, j.2.1⟩
  have hlow : (S.card : ℝ) * (2 * α * Fintype.card V) ≤ Fintype.card V := by
    have h1 : (S.card : ℝ) * (2 * α * Fintype.card V) ≤ ∑ j ∈ S, (j.1.2.card : ℝ) := by
      have := Finset.card_nsmul_le_sum S (fun j => (j.1.2.card : ℝ)) (2 * α * Fintype.card V)
        (fun j _ => comp_card_ge hH3 j.2)
      simpa [nsmul_eq_mul] using this
    have h2 : ∑ j ∈ S, (j.1.2.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hsum
    linarith
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)]
  have : (S.card : ℝ) * (2 * α) * Fintype.card V ≤ 1 * Fintype.card V := by linarith
  exact le_of_mul_le_mul_right this hn

/-- **At most `n ⌊1/(2α)⌋₊` native rows in total.** -/
theorem card_nrow_le {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α) :
    Fintype.card (NRow G lab F) ≤ Fintype.card V * ⌊1 / (2 * α)⌋₊ := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fun j : NRow G lab F => j.1.1)
    (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ v, (univ.filter (fun j : NRow G lab F => j.1.1 = v)).card
      ≤ ∑ _v : V, ⌊1 / (2 * α)⌋₊ := Finset.sum_le_sum fun v _ => card_rows_at_le hα hH3 v
    _ = Fintype.card V * ⌊1 / (2 * α)⌋₊ := by simp

/-! ### Degrees in the V35 link graph of the native matrix -/

/-- The column `vu` of a member `u` of a native row `(v, K)`. -/
lemma isNCol_root (j : NRow G lab F) {u : V} (hu : u ∈ j.1.2) : IsNCol G lab F s(j.1.1, u) := by
  obtain ⟨w, huw, hT⟩ := linkActive_of_mem j.2.1 hu
  exact ⟨{j.1.1, u, w}, hT, mem_triEdges.2 ⟨by simp, by simp, root_ne_of_mem j.2.1 hu⟩⟩

lemma natB_root_ne_zero (j : NRow G lab F) {u : V} (hu : u ∈ j.1.2) :
    natB G lab F j ⟨s(j.1.1, u), isNCol_root j hu⟩ ≠ 0 := by
  obtain ⟨⟨v, K⟩, hj⟩ := j
  show entry G lab F (v, K) s(v, u) ≠ 0
  rw [entry_root, if_pos hu]
  exact sgn_ne_zero _

/-- **Partner row.** For an unanchored native row `(v, K)` and `u ∈ K`, the column `vu`
carries a second nonzero row, and it is rooted at `u`. -/
theorem unanchored_partner (j : NRow G lab F) (hj : ¬ S07V35.Anchored (natB G lab F) j)
    {u : V} (hu : u ∈ j.1.2) :
    ∃ k : NRow G lab F, k ≠ j ∧ k.1.1 = u ∧
      natB G lab F k ⟨s(j.1.1, u), isNCol_root j hu⟩ ≠ 0 := by
  set e : NCol G lab F := ⟨s(j.1.1, u), isNCol_root j hu⟩
  have hje : natB G lab F j e ≠ 0 := natB_root_ne_zero j hu
  have : ∃ k, k ≠ j ∧ natB G lab F k e ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hj
    refine ⟨e, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun k hk => ?_⟩⟩
    · simp [S07V35.supp, hje]
    · by_contra hkj
      exact (mem_filter.1 hk).2 (hcon k hkj)
  obtain ⟨k, hkj, hk⟩ := this
  refine ⟨k, hkj, ?_, hk⟩
  have hmem := root_mem_of_natB hk
  change k.1.1 ∈ s(j.1.1, u) at hmem
  rw [Sym2.mem_iff] at hmem
  rcases hmem with h | h
  · exact absurd (eq_of_natB_root hk hje h) hkj
  · exact h

/-- **Degree from the component size.** An unanchored native row has at least `|K|` distinct
neighbours in the V35 link graph of the native matrix (distinct partner roots `u ∈ K`). -/
theorem card_comp_le_nbrs (j : NRow G lab F) (hj : ¬ S07V35.Anchored (natB G lab F) j) :
    j.1.2.card ≤ (S07V35.nbrs (S07V35.linkGraph (natB G lab F)) j).card := by
  let f : V → NRow G lab F := fun u =>
    if h : u ∈ j.1.2 then (unanchored_partner j hj h).choose else j
  have hf : ∀ u (hu : u ∈ j.1.2), f u ≠ j ∧ (f u).1.1 = u ∧
      natB G lab F (f u) ⟨s(j.1.1, u), isNCol_root j hu⟩ ≠ 0 := by
    intro u hu
    simp only [f, dif_pos hu]
    exact (unanchored_partner j hj hu).choose_spec
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro u hu
    obtain ⟨h1, -, h3⟩ := hf u hu
    simp only [S07V35.nbrs, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨h1.symm, _, natB_root_ne_zero j hu, h3⟩
  · intro u hu w hw h
    rw [← (hf u hu).2.1, ← (hf w hw).2.1, h]

/-- **Valid degree bound for the V35 gauge lemma**: every natural `m ≤ 2 α n` bounds the
number of distinct link-graph neighbours of every unanchored native row (from H3). -/
theorem nbrs_ge_of_le {α : ℝ} (hH3 : CommonNbrCond G lab F α) {m : ℕ}
    (hm : (m : ℝ) ≤ 2 * α * Fintype.card V) (j : NRow G lab F)
    (hj : ¬ S07V35.Anchored (natB G lab F) j) :
    m ≤ (S07V35.nbrs (S07V35.linkGraph (natB G lab F)) j).card := by
  have h1 : (m : ℝ) ≤ j.1.2.card := hm.trans (comp_card_ge hH3 j.2)
  exact (by exact_mod_cast h1 : m ≤ j.1.2.card).trans (card_comp_le_nbrs j hj)

/-- The requested form: any natural `m ≤ α n` is a valid degree bound (`0 ≤ α`). -/
theorem nbrs_ge_of_le_alpha {α : ℝ} (hα : 0 ≤ α) (hH3 : CommonNbrCond G lab F α) {m : ℕ}
    (hm : (m : ℝ) ≤ α * Fintype.card V) (j : NRow G lab F)
    (hj : ¬ S07V35.Anchored (natB G lab F) j) :
    m ≤ (S07V35.nbrs (S07V35.linkGraph (natB G lab F)) j).card := by
  refine nbrs_ge_of_le hH3 (hm.trans ?_) j hj
  have : (0 : ℝ) ≤ α * Fintype.card V := by positivity
  linarith

end S07V36
