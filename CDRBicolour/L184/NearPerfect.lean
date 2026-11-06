/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Equitable

/-!
# L184, part 1: colour classes of the final residual are near-perfect

Let `H` be a simple graph on a vertex set of ODD order `c`, properly edge-coloured with `k`
colours, with exactly `k(c-1)/2` edges.  Then

* every colour class has exactly `(c-1)/2` edges (`two_mul_card_class`), hence misses exactly
  one vertex `omitted i` (`compl_coveredBy`);
* a vertex `v` is omitted by exactly `k - deg_H v` colours (`card_omitted_fibre`).

These are the counting facts used in L184 ("each of the a colour classes has at most (c-1)/2
edges and their total equals a(c-1)/2, so every class is a near-perfect matching; its single
omitted point occurs a-s times at w, twice at each v in P, and never elsewhere").
-/

@[expose] public section

namespace CDRBicolour.L184

open Finset LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions
  LeanPool.Vizing.Equitable

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
  {k : ℕ} (colour : Sym2 W → Fin k)

/-- Vertices covered by the colour class `i`. -/
def coveredBy (i : Fin k) : Finset W :=
  (colourClass H.edgeFinset colour i).biUnion Sym2.toFinset

theorem card_coveredBy (hproper : ProperOn H.edgeFinset colour) (i : Fin k) :
    (coveredBy H colour i).card = 2 * (colourClass H.edgeFinset colour i).card := by
  unfold coveredBy
  rw [card_biUnion (colourClass_pairwiseDisjoint_toFinset hproper i)]
  calc ∑ e ∈ colourClass H.edgeFinset colour i, e.toFinset.card
      = ∑ _e ∈ colourClass H.edgeFinset colour i, 2 := by
        refine sum_congr rfl fun e he => ?_
        exact Sym2.card_toFinset_of_not_isDiag e
          (SimpleGraph.not_isDiag_of_mem_edgeFinset (colourClass_subset _ _ _ he))
    _ = 2 * (colourClass H.edgeFinset colour i).card := by
        rw [sum_const, smul_eq_mul, mul_comm]

variable {H colour}

/-- Every class has exactly `(c-1)/2` edges. -/
theorem two_mul_card_class (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (i : Fin k) :
    2 * (colourClass H.edgeFinset colour i).card = Fintype.card W - 1 := by
  have hle : ∀ j, 2 * (colourClass H.edgeFinset colour j).card ≤ Fintype.card W - 1 := by
    intro j
    have := two_mul_card_colourClass_le_vertices colour hproper j
    obtain ⟨m, hm⟩ := hodd
    omega
  by_contra hne
  have hlt : 2 * (colourClass H.edgeFinset colour i).card < Fintype.card W - 1 :=
    lt_of_le_of_ne (hle i) hne
  have hsum := sum_card_colourClass_univ H.edgeFinset colour
  have hstrict : ∑ j : Fin k, 2 * (colourClass H.edgeFinset colour j).card <
      ∑ _j : Fin k, (Fintype.card W - 1) :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ _, hlt⟩
  rw [← mul_sum, hsum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hstrict
  omega

/-- Every class misses exactly one vertex. -/
theorem card_compl_coveredBy (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (i : Fin k) :
    (coveredBy H colour i)ᶜ.card = 1 := by
  rw [card_compl, card_coveredBy H colour hproper, two_mul_card_class hproper hodd hE]
  obtain ⟨m, hm⟩ := hodd
  omega

/-- The vertex omitted by the colour class `i`. -/
noncomputable def omitted (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (i : Fin k) : W :=
  (card_eq_one.1 (card_compl_coveredBy hproper hodd hE i)).choose

theorem compl_coveredBy (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (i : Fin k) :
    (coveredBy H colour i)ᶜ = {omitted hproper hodd hE i} :=
  (card_eq_one.1 (card_compl_coveredBy hproper hodd hE i)).choose_spec

theorem mem_coveredBy_iff_ne_omitted (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (i : Fin k) (v : W) :
    v ∈ coveredBy H colour i ↔ v ≠ omitted hproper hodd hE i := by
  have h := compl_coveredBy hproper hodd hE i
  constructor
  · intro hv hvo
    have : v ∈ (coveredBy H colour i)ᶜ := by rw [h, hvo]; exact mem_singleton_self _
    exact (mem_compl.1 this) hv
  · intro hne
    by_contra hv
    have : v ∈ (coveredBy H colour i)ᶜ := mem_compl.2 hv
    rw [h, mem_singleton] at this
    exact hne this

theorem mem_coveredBy_iff (v : W) (i : Fin k) :
    v ∈ coveredBy H colour i ↔ ∃ e ∈ H.incidenceFinset v, colour e = i := by
  simp only [coveredBy, mem_biUnion, mem_colourClass, Sym2.mem_toFinset,
    SimpleGraph.incidenceFinset_eq_filter, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hc⟩, hv⟩; exact ⟨e, ⟨he, hv⟩, hc⟩
  · rintro ⟨e, ⟨he, hv⟩, hc⟩; exact ⟨e, ⟨he, hc⟩, hv⟩

/-- A vertex is covered by exactly `deg v` colours (properness). -/
theorem card_covering_colours (hproper : ProperOn H.edgeFinset colour) (v : W) :
    (univ.filter fun i : Fin k => v ∈ coveredBy H colour i).card = H.degree v := by
  have hset : (univ.filter fun i : Fin k => v ∈ coveredBy H colour i) =
      (H.incidenceFinset v).image colour := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_coveredBy_iff]
  rw [hset, card_image_of_injOn, SimpleGraph.card_incidenceFinset_eq_degree]
  intro e he f hf hef
  by_contra hne
  have he' := mem_coe.1 he
  have hf' := mem_coe.1 hf
  have hd := hproper e (SimpleGraph.incidenceFinset_subset H v he')
    f (SimpleGraph.incidenceFinset_subset H v hf') hne hef
  have hve : v ∈ e := (SimpleGraph.mem_incidenceFinset.1 he').2
  have hvf : v ∈ f := (SimpleGraph.mem_incidenceFinset.1 hf').2
  exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 hve) (Sym2.mem_toFinset.2 hvf)

/-- **Omission count.** Exactly `k - deg v` classes omit `v`. -/
theorem card_omitted_fibre (hproper : ProperOn H.edgeFinset colour)
    (hodd : Odd (Fintype.card W))
    (hE : 2 * H.edgeFinset.card = k * (Fintype.card W - 1)) (v : W) :
    (univ.filter fun i : Fin k => omitted hproper hodd hE i = v).card = k - H.degree v := by
  have hset : (univ.filter fun i : Fin k => omitted hproper hodd hE i = v) =
      univ.filter fun i : Fin k => ¬ v ∈ coveredBy H colour i := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_coveredBy_iff_ne_omitted hproper hodd hE,
      ne_eq, not_not]
    exact eq_comm
  rw [hset]
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
    (fun i : Fin k => v ∈ coveredBy H colour i)
  rw [card_covering_colours hproper v, card_univ, Fintype.card_fin] at hsplit
  omega

end CDRBicolour.L184
