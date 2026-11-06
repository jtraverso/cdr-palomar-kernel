/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.RobustAbstract

@[expose] public section

/-!
# V25 — robust connectivity ⇒ edge expansion

`expansion_of_conn`: if `K` stays connected after deleting any `≤ s` vertices and any edge set
of maximum degree `≤ d`, then every `T` with `2|T| ≤ |β|` has
`(d + 1) · min(|T|, s + 1) ≤ 2 · cutCount K T`.

Proof: let `D` be the vertices with more than `d` cut edges; `(d+1)|D| ≤ 2·cut`. If the bound
failed, `|D| ≤ s` and `|D| < |T| ≤ |β ∖ T|`; deleting `D` and the remaining cut edges (maximum
degree `≤ d`) would disconnect a survivor of `T` from a survivor of its complement.
-/

open Finset

namespace S07V25

open S07V24

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- number of cut edges at `x` -/
def cdeg (K : SimpleGraph β) [DecidableRel K.Adj] (T : Finset β) (x : β) : ℕ :=
  if x ∈ T then ((univ \ T).filter (K.Adj x)).card else (T.filter (K.Adj x)).card

lemma sum_cdeg_compl (K : SimpleGraph β) [DecidableRel K.Adj] (T : Finset β) :
    ∑ x ∈ univ \ T, (T.filter (K.Adj x)).card = cutCount K T := by
  unfold cutCount
  have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T) (t := univ \ T)
    (r := K.Adj)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
  rw [this]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ext y; simp [SimpleGraph.adj_comm]

/-- **robust connectivity ⇒ expansion** -/
theorem expansion_of_conn (K : SimpleGraph β) [DecidableRel K.Adj] (s d : ℕ)
    (hK : RobustConn K s d) (T : Finset β) (hT : 2 * T.card ≤ Fintype.card β) :
    (d + 1) * min T.card (s + 1) ≤ 2 * cutCount K T := by
  by_contra hlt
  push_neg at hlt
  set D := univ.filter (fun x => d < cdeg K T x) with hD
  have hDT : (d + 1) * (D.filter (· ∈ T)).card ≤ cutCount K T := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    calc ∑ _x ∈ D.filter (· ∈ T), (d + 1) ≤ ∑ x ∈ D.filter (· ∈ T), cdeg K T x := by
          refine Finset.sum_le_sum fun x hx => ?_
          simp only [hD, mem_filter, mem_univ, true_and] at hx; omega
      _ ≤ ∑ x ∈ T, cdeg K T x := by
          refine Finset.sum_le_sum_of_subset (fun x hx => ?_)
          simp only [mem_filter] at hx; exact hx.2
      _ = cutCount K T := by
          unfold cutCount; refine Finset.sum_congr rfl fun x hx => ?_
          simp [cdeg, hx]
  have hDTc : (d + 1) * (D.filter (· ∉ T)).card ≤ cutCount K T := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const, ← sum_cdeg_compl]
    calc ∑ _x ∈ D.filter (· ∉ T), (d + 1) ≤ ∑ x ∈ D.filter (· ∉ T), cdeg K T x := by
          refine Finset.sum_le_sum fun x hx => ?_
          simp only [hD, mem_filter, mem_univ, true_and] at hx; omega
      _ ≤ ∑ x ∈ univ \ T, cdeg K T x := by
          refine Finset.sum_le_sum_of_subset (fun x hx => ?_)
          simp only [mem_filter] at hx; simp [hx.2]
      _ = _ := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp only [mem_sdiff, mem_univ, true_and] at hx
          simp [cdeg, hx]
  have hDcard : (d + 1) * D.card ≤ 2 * cutCount K T := by
    have := Finset.card_filter_add_card_filter_not (s := D) (fun x => x ∈ T)
    nlinarith
  have hDlt : D.card < min T.card (s + 1) := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left (d + 1) h
    omega
  have hDs : D.card ≤ s := by have := min_le_right T.card (s + 1); omega
  have hDT' : D.card < T.card := lt_of_lt_of_le hDlt (min_le_left _ _)
  obtain ⟨x0, hx0⟩ : (T \ D).Nonempty := by
    rw [← Finset.card_pos]; have := Finset.le_card_sdiff D T; omega
  obtain ⟨y0, hy0⟩ : ((univ \ T) \ D).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff D (univ \ T)
    have h2 : (univ \ T).card = Fintype.card β - T.card := by
      rw [Finset.card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  rw [mem_sdiff] at hx0
  simp only [mem_sdiff, mem_univ, true_and] at hy0
  set B : Finset (Sym2 β) := ((T ×ˢ (univ \ T)).filter
    (fun p => K.Adj p.1 p.2 ∧ p.1 ∉ D ∧ p.2 ∉ D)).image (fun p => s(p.1, p.2)) with hBdef
  have hBdeg : ∀ x, degB B x ≤ d := by
    intro x
    unfold degB
    by_cases hxD : x ∈ D
    · have : B.filter (fun e => x ∈ e) = ∅ := by
        apply Finset.filter_false_of_mem
        intro e he hxe
        simp only [hBdef, mem_image, mem_filter, mem_product] at he
        obtain ⟨⟨p, q⟩, ⟨-, -, h3, h4⟩, rfl⟩ := he
        rcases Sym2.mem_iff.1 hxe with rfl | rfl
        exacts [h3 hxD, h4 hxD]
      rw [this]; simp
    · have hcd : cdeg K T x ≤ d := by
        simp only [hD, mem_filter, mem_univ, true_and, not_lt] at hxD; exact hxD
      by_cases hxT : x ∈ T
      · refine le_trans (Finset.card_le_card (t := ((univ \ T).filter (K.Adj x)).image
          (fun y => s(x, y))) ?_) (Finset.card_image_le.trans ?_)
        · intro e he
          simp only [hBdef, mem_filter, mem_image, mem_product] at he
          obtain ⟨⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq, -, -⟩, rfl⟩, hxe⟩ := he
          rcases Sym2.mem_iff.1 hxe with rfl | rfl
          · exact mem_image.2 ⟨q, mem_filter.2 ⟨hq, hpq⟩, rfl⟩
          · simp at hq; exact absurd hxT hq
        · simpa [cdeg, hxT] using hcd
      · refine le_trans (Finset.card_le_card (t := (T.filter (K.Adj x)).image
          (fun y => s(y, x))) ?_) (Finset.card_image_le.trans ?_)
        · intro e he
          simp only [hBdef, mem_filter, mem_image, mem_product] at he
          obtain ⟨⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq, -, -⟩, rfl⟩, hxe⟩ := he
          rcases Sym2.mem_iff.1 hxe with rfl | rfl
          · exact absurd hp hxT
          · exact mem_image.2 ⟨p, mem_filter.2 ⟨hp, hpq.symm⟩, rfl⟩
        · simpa [cdeg, hxT] using hcd
  obtain ⟨p, hpS, hpB⟩ := hK D hDs B hBdeg x0 y0 hx0.2 hy0.2
  obtain ⟨dt, hdt, h1, h2⟩ := p.exists_boundary_dart (T : Set β) (by simpa using hx0.1)
    (by simpa using hy0.1)
  have hfst := p.dart_fst_mem_support_of_mem_darts hdt
  have hsnd := p.dart_snd_mem_support_of_mem_darts hdt
  apply hpB dt.edge (List.mem_map_of_mem hdt)
  simp only [hBdef, mem_image, mem_filter, mem_product]
  refine ⟨dt.toProd, ⟨⟨h1, by simpa using h2⟩, dt.adj, fun h => hpS _ hfst h,
    fun h => hpS _ hsnd h⟩, rfl⟩

end S07V25
