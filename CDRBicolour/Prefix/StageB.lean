/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.HallStars

/-!
# L182, stage B: the BBC colouring, the stars, and BCC by L181 (star version)

P2 parameters as natural-number polynomials in `k` (`y = 6k+3`):
`a = 12k²+14k+4`, `b = a+2`, `c = 12k²+20k+9`, `N = c-1`, `K₀ = 6k²+4k+1`, `r = 3k+1`.

After stage A the BB graph `GB` has degrees `a-1` (4 vertices) and `a-3`, and
`e(GB) = N·K₀ - r`.  An equitable colouring with the `N` points of `C - w` has `r` classes of
size `K₀-1` and the others of size `K₀`; the multiplicities on `C - w` are `y+3` (`r` times) and
`y+1`, and `w` is missed by every row.  Hall gives distinct star partners, and L181 (star
version) completes every BCC row.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions
  CDRBicolour.L184

/-- P2 parameters. -/
abbrev pa (k : ℕ) : ℕ := 12 * k ^ 2 + 14 * k + 4
abbrev pb (k : ℕ) : ℕ := 12 * k ^ 2 + 14 * k + 6
abbrev pc (k : ℕ) : ℕ := 12 * k ^ 2 + 20 * k + 9
abbrev colP (k : ℕ) := col3 (pa k) (pb k) (pc k)

/-- Sum of a two-valued (`2`/`4`) function. -/
theorem sum_two_four {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (hf : ∀ x, f x = 2 ∨ f x = 4) :
    ∑ x, f x = 2 * Fintype.card ι + 2 * (univ.filter fun x => f x = 4).card := by
  have h : ∀ x, f x = 2 + 2 * (if f x = 4 then 1 else 0) := by
    intro x; rcases hf x with h | h <;> simp [h]
  rw [sum_congr rfl fun x _ => h x, sum_add_distrib, sum_const, card_univ, smul_eq_mul,
    ← mul_sum, sum_boole]
  simp [mul_comm]

/-- **Stage B.** -/
theorem stageB (hS : L181_Star.{0}) (k : ℕ) (hk : 4 ≤ k)
    (μ : AType (colP k) → AType (colP k)) (χA : Sym2 (AType (colP k)) → BType (colP k))
    (MA : AType (colP k) → Finset (Sym2 (BType (colP k))))
    (hMA : ∀ i, IsPerfectPairing (MA i) (miss (GA μ) χA i)) (hMAd : PairDisjoint MA)
    (htwo : ∀ v, mult (GA μ) χA v = 2 ∨ mult (GA μ) χA v = 4)
    (hcnt : (univ.filter fun v => mult (GA μ) χA v = 4).card = pa k - 2) :
    ∃ (w : CType (colP k)) (χB : Sym2 (BType (colP k)) → CType (colP k))
      (MB : BType (colP k) → Finset (Sym2 (CType (colP k)))),
      ProperOn (GB MA).edgeFinset χB ∧ (∀ e ∈ (GB MA).edgeFinset, χB e ≠ w) ∧
      (∀ j, IsPerfectPairing (MB j) (miss (GB MA) χB j)) ∧ PairDisjoint MB ∧
      (∀ v, v ≠ w → mult (GB MA) χB v = 6 * k + 4 ∨ mult (GB MA) χB v = 6 * k + 6) ∧
      (univ.filter fun v => v ≠ w ∧ mult (GB MA) χB v = 6 * k + 6).card = 3 * k + 1 := by
  classical
  have hcB : Fintype.card (BType (colP k)) = 12 * k ^ 2 + 14 * k + 6 := card_classB
  have hcC : Fintype.card (CType (colP k)) = (12 * k ^ 2 + 20 * k + 8) + 1 := card_classC
  have hcnt2 : (univ.filter fun v => mult (GA μ) χA v = 4).card = 12 * k ^ 2 + 14 * k + 2 := by
    rw [hcnt]; show 12 * k ^ 2 + 14 * k + 4 - 2 = _; omega
  have hk2 : 16 ≤ k ^ 2 := by nlinarith
  -- degrees of `GB`
  have hdegB : ∀ v, (GB MA).degree v + mult (GA μ) χA v = 12 * k ^ 2 + 14 * k + 5 := by
    intro v
    have := unused_degree_add_mult hMA hMAd v
    have h2 : (GB MA).degree v + mult (GA μ) χA v = Fintype.card (BType (colP k)) - 1 := by
      convert this using 2
    rw [h2, hcB]; omega
  have hΔ : (GB MA).maxDegree + 1 ≤ 12 * k ^ 2 + 20 * k + 8 := by
    have : ∀ v, (GB MA).degree v ≤ 12 * k ^ 2 + 14 * k + 3 := by
      intro v; have := hdegB v; rcases htwo v with h | h <;> omega
    have := SimpleGraph.maxDegree_le_of_forall_degree_le (GB MA) _ this
    omega
  -- `Σ mult_A = 4a` and `e(GB) + r = N·K₀`
  have hsumA : ∑ v, mult (GA μ) χA v = 4 * (12 * k ^ 2 + 14 * k + 4) := by
    rw [sum_two_four _ htwo, hcB, hcnt2]; ring
  have hE : (GB MA).edgeFinset.card + (3 * k + 1) =
      (12 * k ^ 2 + 20 * k + 8) * (6 * k ^ 2 + 4 * k + 1) := by
    have h1 := (GB MA).sum_degrees_eq_twice_card_edges
    have h2 : ∑ v, ((GB MA).degree v + mult (GA μ) χA v) =
        ∑ _v : BType (colP k), (12 * k ^ 2 + 14 * k + 5) :=
      sum_congr rfl fun v _ => hdegB v
    rw [sum_add_distrib, sum_const, card_univ, hcB, smul_eq_mul, h1, hsumA] at h2
    have h3 : 2 * ((GB MA).edgeFinset.card + (3 * k + 1)) =
        2 * ((12 * k ^ 2 + 20 * k + 8) * (6 * k ^ 2 + 4 * k + 1)) := by
      nlinarith [h2]
    omega
  -- equitable colouring of `GB` with the `N` points of `C - w`
  obtain ⟨colour, hprop, hequit, -⟩ :=
    exists_equitable_edge_colouring (GB MA) (12 * k ^ 2 + 20 * k + 8) hΔ
  let eC : CType (colP k) ≃ Fin ((12 * k ^ 2 + 20 * k + 8) + 1) := Fintype.equivFinOfCardEq hcC
  set w : CType (colP k) := eC.symm 0 with hw
  let ι : Fin (12 * k ^ 2 + 20 * k + 8) → CType (colP k) := fun i => eC.symm i.succ
  have hι : Function.Injective ι := fun i j h => Fin.succ_injective _ (eC.symm.injective h)
  have hιw : ∀ i, ι i ≠ w := fun i h => Fin.succ_ne_zero i (eC.symm.injective h)
  have hιsurj : ∀ v, v ≠ w → ∃ i, ι i = v := by
    intro v hv
    have h0 : eC v ≠ 0 := fun h => hv (by rw [hw, ← h]; simp)
    refine ⟨(eC v).pred h0, ?_⟩
    simp [ι]
  set χB : Sym2 (BType (colP k)) → CType (colP k) := ι ∘ colour with hχB
  have hpropB : ProperOn (GB MA).edgeFinset χB := properOn_comp hprop hι
  have havoid : ∀ e ∈ (GB MA).edgeFinset, χB e ≠ w := fun e _ => hιw _
  have hclassι : ∀ i, (colourClass (GB MA).edgeFinset χB (ι i)).card =
      (colourClass (GB MA).edgeFinset colour i).card := by
    intro i; congr 1; ext x
    simp only [mem_colourClass, hχB, Function.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hι h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
  have hclassw : (colourClass (GB MA).edgeFinset χB w).card = 0 := by
    rw [card_eq_zero]; ext x
    simp only [mem_colourClass, notMem_empty, iff_false, not_and]
    intro hx; exact havoid x hx
  -- class sizes `K₀` / `K₀ - 1`
  have hsizes := equitable_sizes (fun i => (colourClass (GB MA).edgeFinset colour i).card)
    (fun x y => hequit x y) (6 * k ^ 2 + 4 * k + 1) (3 * k + 1) (by omega)
    (by rw [Fintype.card_fin]; nlinarith) (by nlinarith)
    (by rw [sum_card_colourClass_univ, Fintype.card_fin]; exact hE)
  have hmultB : ∀ v, mult (GB MA) χB v + 2 * (colourClass (GB MA).edgeFinset χB v).card =
      12 * k ^ 2 + 14 * k + 6 := by
    intro v; rw [mult_add_two_mul_class hpropB, hcB]
  have hmultι : ∀ i, mult (GB MA) χB (ι i) = 6 * k + 4 ∨ mult (GB MA) χB (ι i) = 6 * k + 6 := by
    intro i
    have h1 := hmultB (ι i)
    rw [hclassι] at h1
    rcases hsizes.1 i with h | h
    · left; rw [h] at h1; omega
    · right; omega
  -- missing sets
  have hmissB : ∀ j, (miss (GB MA) χB j).card = 6 * k + 4 + mult (GA μ) χA j := by
    intro j; rw [card_miss hpropB, hcC]; have := hdegB j; rcases htwo j with h | h <;> omega
  have hwmiss : ∀ j, w ∈ miss (GB MA) χB j := by
    intro j; rw [mem_miss]; intro e he
    exact havoid e (SimpleGraph.incidenceFinset_subset _ _ he)
  -- Hall: distinct star partners
  set X := univ.filter fun j => mult (GA μ) χA j = 2 with hX
  have hXcard : X.card ≤ 4 := by
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (BType (colP k))))
      (fun j => mult (GA μ) χA j = 4)
    rw [hcnt2, card_univ, hcB] at hsplit
    have : X ⊆ univ.filter fun j => ¬ mult (GA μ) χA j = 4 := by
      intro j hj; simp only [hX, mem_filter, mem_univ, true_and] at hj ⊢; omega
    have := card_le_card this
    omega
  obtain ⟨t, htinj, ht⟩ := hall_stars (fun j => (miss (GB MA) χB j).erase w) X (6 * k + 7)
    (6 * k + 6) hXcard
    (by
      intro j
      rw [card_erase_of_mem (hwmiss j), hmissB j]
      by_cases hj : j ∈ X
      · simp only [hj, if_true]; simp only [hX, mem_filter, mem_univ, true_and] at hj; omega
      · simp only [hj, if_false]
        simp only [hX, mem_filter, mem_univ, true_and] at hj
        rcases htwo j with h | h <;> omega)
    (by
      intro v
      by_cases hv : v = w
      · subst hv
        simp only [mem_erase, ne_eq, not_true_eq_false, false_and, filter_false, card_empty]
        omega
      · obtain ⟨i, rfl⟩ := hιsurj v hv
        have hle : (univ.filter fun j => ι i ∈ (miss (GB MA) χB j).erase w).card ≤
            mult (GB MA) χB (ι i) := by
          apply card_le_card; intro j hj
          simp only [mem_filter, mem_univ, true_and, mem_erase] at hj ⊢; exact hj.2
        rcases hmultι i with h | h <;> omega)
    (by omega) (by omega)
  have htmiss : ∀ j, t j ∈ miss (GB MA) χB j ∧ t j ≠ w := by
    intro j; have := ht j; rw [mem_erase] at this; exact ⟨this.2, this.1⟩
  -- L181, star version, with `m = 6k+4`
  obtain ⟨χB2, hprop2, havoid2, htwo2, hcount2, MB, hMB, hMBd⟩ :=
    hS (BType (colP k)) (CType (colP k)) (GB MA) χB (6 * k + 4) w t hpropB havoid htinj htmiss
      (fun j => by
        rw [hmissB j]
        rcases htwo j with h | h <;> rw [h]
        · exact ⟨⟨3 * k + 3, by ring⟩, by omega⟩
        · exact ⟨⟨3 * k + 4, by ring⟩, by omega⟩)
      (fun v hv => by obtain ⟨i, rfl⟩ := hιsurj v hv; exact hmultι i)
      (by rw [hcC, Nat.add_sub_cancel]; nlinarith)
  refine ⟨w, χB2, MB, hprop2, havoid2, hMB, hMBd, htwo2, ?_⟩
  rw [hcount2]
  -- count of high labels: `r = 3k+1`
  have hset : (univ.filter fun v => v ≠ w ∧ mult (GB MA) χB v = 6 * k + 6) =
      (univ.filter fun i : Fin (12 * k ^ 2 + 20 * k + 8) =>
        (colourClass (GB MA).edgeFinset colour i).card + 1 = 6 * k ^ 2 + 4 * k + 1).map
        ⟨ι, hι⟩ := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hv, hm⟩
      obtain ⟨i, rfl⟩ := hιsurj v hv
      refine ⟨i, ?_, rfl⟩
      have h1 := hmultB (ι i); rw [hclassι] at h1
      rcases hsizes.1 i with h | h
      · rw [h] at h1; omega
      · exact h
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hιw i, ?_⟩
      have h1 := hmultB (ι i); rw [hclassι] at h1
      omega
  rw [hset, card_map, hsizes.2]

end CDRBicolour.Prefix
