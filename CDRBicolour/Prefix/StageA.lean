/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.P2Types
public import LeanPool.Vizing.Corollaries

/-!
# L182, stage A: `M_A`, the AAB colouring, and ABB by L181 (no anchor)

`M_A` is any perfect matching of `A` (|A| = a even).  `K_A − M_A` is `(a-2)`-regular; an
equitable colouring with the `b = a+2` points of `B` (Vizing + balancing, Lean Pool) has class
sizes `(a-2)/2` and `(a-4)/2`, so every `A`-row misses exactly `4` colours and every `B`-label is
missed by `2` or `4` rows, the value `4` occurring `a-2` times.  L181 (no anchor) then completes
all ABB rows, keeping the two-level multiset.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions
  CDRBicolour.L184

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3}

theorem GA_adj_iff' {μ : AType col → AType col} (hμ : ∀ u, μ (μ u) = u) {x y : AType col} :
    (GA μ).Adj x y ↔ x ≠ y ∧ y ≠ μ x := by
  simp only [GA, SimpleGraph.fromRel_adj, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact h2
    · intro h; apply h2; rw [h, hμ]
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩

theorem GA_degree {μ : AType col → AType col} (hμ : ∀ u, μ (μ u) = u) (hμ' : ∀ u, μ u ≠ u)
    (x : AType col) : (GA μ).degree x = Fintype.card (AType col) - 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hset : (GA μ).neighborFinset x = (univ.erase x).erase (μ x) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, GA_adj_iff' hμ, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 h.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 h.symm, h1⟩
  rw [hset, card_erase_of_mem (mem_erase.2 ⟨hμ' x, mem_univ _⟩), card_erase_of_mem (mem_univ _),
    card_univ]
  omega

/-- Post-composition with an injection keeps properness. -/
theorem properOn_comp {W Cl Cl' : Type*} [DecidableEq W] {E : Finset (Sym2 W)}
    {colour : Sym2 W → Cl} (h : ProperOn E colour) {f : Cl → Cl'} (hf : Function.Injective f) :
    ProperOn E (f ∘ colour) :=
  fun e he g hg hne hsame => h e he g hg hne (hf hsame)

/-- **Stage A.** -/
theorem stageA (hL : L181_NoAnchor.{0}) (a b c : ℕ) (hb : b = a + 2) (ha : 22 ≤ a)
    (haeven : Even a) :
    ∃ μ : AType (col3 a b c) → AType (col3 a b c), (∀ u, μ (μ u) = u) ∧ (∀ u, μ u ≠ u) ∧
      ∃ (χA : Sym2 (AType (col3 a b c)) → BType (col3 a b c))
        (MA : AType (col3 a b c) → Finset (Sym2 (BType (col3 a b c)))),
        ProperOn (GA μ).edgeFinset χA ∧ (∀ i, IsPerfectPairing (MA i) (miss (GA μ) χA i)) ∧
        PairDisjoint MA ∧ (∀ v, mult (GA μ) χA v = 2 ∨ mult (GA μ) χA v = 4) ∧
        (univ.filter fun v => mult (GA μ) χA v = 4).card = a - 2 := by
  classical
  have hcA : Fintype.card (AType (col3 a b c)) = a := card_classA
  have hcB : Fintype.card (BType (col3 a b c)) = b := card_classB
  -- the reserved matching
  obtain ⟨μ, hμ, hμ', -⟩ := exists_pairing_of_even_fibres (fun _ : AType (col3 a b c) => ())
    (fun _ => by
      have : (univ.filter fun _ : AType (col3 a b c) => () = ()) = univ := filter_true_of_mem
        (fun _ _ => rfl)
      rw [this, card_univ, hcA]; exact haeven)
  refine ⟨μ, hμ, hμ', ?_⟩
  -- equitable colouring of `K_A − M_A` with the `b` labels of `B`
  have hdeg : ∀ x, (GA μ).degree x = a - 2 := fun x => by rw [GA_degree hμ hμ', hcA]
  have hΔ : (GA μ).maxDegree + 1 ≤ b := by
    have := SimpleGraph.maxDegree_le_of_forall_degree_le (GA μ) (a - 2) fun x => (hdeg x).le
    omega
  obtain ⟨colour, hprop, hequit, -⟩ := exists_equitable_edge_colouring (GA μ) b hΔ
  let e : BType (col3 a b c) ≃ Fin b := Fintype.equivFinOfCardEq hcB
  set χA : Sym2 (AType (col3 a b c)) → BType (col3 a b c) := e.symm ∘ colour with hχA
  have hpropA : ProperOn (GA μ).edgeFinset χA := properOn_comp hprop e.symm.injective
  have hclass : ∀ v, (colourClass (GA μ).edgeFinset χA v).card =
      (colourClass (GA μ).edgeFinset colour (e v)).card := by
    intro v
    congr 1
    ext x
    simp only [mem_colourClass, hχA, Function.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2]; simp⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩
  -- edge count `a(a-2)/2`
  obtain ⟨t, ht⟩ := haeven
  have hE : (GA μ).edgeFinset.card = t * (a - 2) := by
    have h := (GA μ).sum_degrees_eq_twice_card_edges
    simp only [hdeg, sum_const, card_univ, hcA, smul_eq_mul] at h
    have h2 : a * (a - 2) = 2 * (t * (a - 2)) := by
      have : a = t + t := ht
      calc a * (a - 2) = (t + t) * (a - 2) := by rw [← this]
        _ = 2 * (t * (a - 2)) := by ring
    omega
  -- class sizes: `t-1` (`a-2` labels) and `t-2`
  have hsizes := equitable_sizes (fun v => (colourClass (GA μ).edgeFinset χA v).card)
    (fun x y => by rw [hclass, hclass]; exact hequit (e x) (e y)) (t - 1) (a - 2)
    (by omega) (by rw [hcB]; omega) (by omega) (by
      rw [sum_card_colourClass_univ, hE, hcB, hb, ht]
      zify [show 2 ≤ t + t by omega, show 1 ≤ t by omega]
      ring)
  have hmult : ∀ v, mult (GA μ) χA v + 2 * (colourClass (GA μ).edgeFinset χA v).card = a := by
    intro v; rw [mult_add_two_mul_class hpropA, hcA]
  have hmiss : ∀ i, (miss (GA μ) χA i).card = 4 := by
    intro i; rw [card_miss hpropA, hcB, hdeg]; omega
  -- apply L181 (no anchor) with `m = 2`
  obtain ⟨χA', hprop', htwo, hcount, MA, hMA, hMAd⟩ :=
    hL (AType (col3 a b c)) (BType (col3 a b c)) (GA μ) χA 2 hpropA
      (fun i => by rw [hmiss i]; exact ⟨⟨2, rfl⟩, le_rfl⟩)
      (fun v => by
        have := hmult v
        rcases hsizes.1 v with h | h
        · left; rw [h] at this; omega
        · right; omega)
      (by rw [hcB]; omega)
  refine ⟨χA', MA, hprop', hMA, hMAd, htwo, ?_⟩
  rw [hcount]
  have hset : (univ.filter fun v => mult (GA μ) χA v = 4) =
      univ.filter fun v => (colourClass (GA μ).edgeFinset χA v).card + 1 = t - 1 := by
    ext v
    simp only [mem_filter, mem_univ, true_and]
    have := hmult v
    rcases hsizes.1 v with h | h <;> constructor <;> intro h' <;> omega
  rw [hset, hsizes.2]

end CDRBicolour.Prefix
