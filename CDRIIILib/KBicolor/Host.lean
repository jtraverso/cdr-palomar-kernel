/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Host

/-!
# k-bicolourings: the host, H3 (common neighbours) and H1 (diffuse seed)

The host of a labelling `lab : V → Fin k` is the complete graph on `V`; the allowed types are the
**bicoloured** label multisets (`bicF k`: three labels, exactly two distinct). An allowed
decomposition of all edges is a Steiner triple system all of whose blocks meet exactly two
classes, i.e. a `k`-bicolouring with the classes of `lab`.

* `kH3`: if every class has at least `δ n` points (`δ n ≥ 4`), H3 holds with `α = δ / 2`.
* `kH1`: **type-uniform seed.** Give the triangle of type `XXY` the weight `a X Y / (c X - 1)`,
  where `a X Y + a Y X = 1` and `∑_{Y ≠ X} c Y · a X Y = c X - 1`. The edge sums are `1`
  exactly: a monochromatic edge in `X` sees `c Y` triangles `XXY` for each `Y ≠ X`; a
  bichromatic edge `XY` sees `c X - 1` triangles `XXY` and `c Y - 1` triangles `XYY`. If
  `a ≥ η` and every class has at least `δ n ≥ 2` points, the weights lie in
  `[1/(Cn), C/n]` with `C = 1/η + 2/δ`. (Such `a` exist iff a circulation problem on the
  complete graph on the classes is feasible; for instance `a X Y = 1/2 + 3 (c X - c Y)/(2n)`
  works when all class sizes differ by less than `n/3`, by the divisibility identity.)
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

variable {k : ℕ}

/-- Allowed types: three labels, exactly two distinct. -/
def bicF (k : ℕ) : Set (Multiset (Fin k)) := {m | Multiset.card m = 3 ∧ m.toFinset.card = 2}

/-- The complete host labelled by `lab`. -/
abbrev kHost {V : Type*} (lab : V → Fin k) : Host V (Fin k) := ⟨⊤, lab⟩

/-- Size of a class. -/
def ksz {V : Type*} [Fintype V] (lab : V → Fin k) (X : Fin k) : ℕ :=
  (univ.filter fun v => lab v = X).card

/-! ### Bicoloured multisets -/

theorem triple_toFinset (p q r : Fin k) :
    ({p, q, r} : Multiset (Fin k)).toFinset = ({p, q, r} : Finset (Fin k)) := by
  ext x; simp

theorem mem_bicF {p q r : Fin k} :
    ({p, q, r} : Multiset (Fin k)) ∈ bicF k ↔
      (p = q ∧ q ≠ r) ∨ (p = r ∧ p ≠ q) ∨ (q = r ∧ p ≠ q) := by
  simp only [bicF, Set.mem_ofPred_eq, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton]
  rw [show (p ::ₘ q ::ₘ {r} : Multiset (Fin k)) = {p, q, r} from rfl, triple_toFinset]
  by_cases hpq : p = q <;> by_cases hqr : q = r <;> by_cases hpr : p = r
  all_goals first
    | (subst_vars; simp_all)
    | (simp_all [card_insert_of_notMem, card_pair])

theorem perm_aba (a b : Fin k) : ({a, b, a} : Multiset (Fin k)) = {a, a, b} := by
  show a ::ₘ b ::ₘ a ::ₘ 0 = a ::ₘ a ::ₘ b ::ₘ 0
  rw [Multiset.cons_swap b a]

theorem perm_abb (a b : Fin k) : ({a, b, b} : Multiset (Fin k)) = {b, b, a} := by
  show a ::ₘ b ::ₘ b ::ₘ 0 = b ::ₘ b ::ₘ a ::ₘ 0
  rw [Multiset.cons_swap a b, Multiset.cons_swap a b]

theorem bicF_cases {m : Multiset (Fin k)} (hm : m ∈ bicF k) :
    ∃ X Y, X ≠ Y ∧ m = {X, X, Y} := by
  obtain ⟨p, q, r, rfl⟩ := Multiset.card_eq_three.1 hm.1
  rcases mem_bicF.1 hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨p, r, h, rfl⟩
  · exact ⟨p, q, h, perm_aba p q⟩
  · exact ⟨q, p, Ne.symm h, perm_abb p q⟩

theorem xxy_inj {X Y X' Y' : Fin k} (h : X ≠ Y) (h' : X' ≠ Y')
    (e : ({X, X, Y} : Multiset (Fin k)) = {X', X', Y'}) : X = X' ∧ Y = Y' := by
  have c1 := congrArg (Multiset.count X') e
  have c2 := congrArg (Multiset.count Y) e
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at c1 c2
  by_cases hX : X' = X
  · subst hX
    refine ⟨rfl, ?_⟩
    by_cases hY : Y = Y'
    · exact hY
    · simp [h.symm, hY] at c2
  · by_cases hY : X' = Y <;> simp_all

/-! ### H3 -/

theorem class_card_sub_two {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k)
    {u v : V} (X : Fin k) :
    ksz lab X ≤ (commonNbrs (kHost lab) X u v).card + 2 := by
  set S := univ.filter fun w : V => lab w = X with hS
  have hsub : (S.erase u).erase v ⊆ commonNbrs (kHost lab) X u v := by
    intro w hw
    simp only [mem_erase, hS, mem_filter, mem_univ, true_and] at hw
    simp only [commonNbrs, mem_filter, mem_univ, true_and, kHost, SimpleGraph.top_adj]
    exact ⟨Ne.symm hw.2.1, Ne.symm hw.1, hw.2.2⟩
  have h1 := card_le_card hsub
  have h2 := pred_card_le_card_erase (s := S.erase u) (a := v)
  have h3 := pred_card_le_card_erase (s := S) (a := u)
  have h0 : ksz lab X = S.card := rfl
  omega

/-- **H3**: classes of size at least `δ n`, `δ n ≥ 4`, give `α = δ / 2`. -/
theorem kH3 {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k) {δ : ℝ}
    (hcls : ∀ X, δ * Fintype.card V ≤ ksz lab X) (h4 : 4 ≤ δ * Fintype.card V) :
    CommonNbrCond (kHost lab) (bicF k) (δ / 2) := by
  intro u v _ X _
  have h := class_card_sub_two lab (u := u) (v := v) X
  have hR : (ksz lab X : ℝ) ≤ (commonNbrs (kHost lab) X u v).card + 2 := by exact_mod_cast h
  have := hcls X
  linarith

/-! ### H1 -/

/-- Seed data for class sizes `c`: `a X Y + a Y X = 1`, `a ≥ η`, and the row identities. -/
def SeedData (c : Fin k → ℕ) (η : ℝ) (a : Fin k → Fin k → ℝ) : Prop :=
  (∀ X Y, X ≠ Y → a X Y + a Y X = 1) ∧ (∀ X Y, X ≠ Y → η ≤ a X Y) ∧
    ∀ X, ∑ Y ∈ univ.filter (fun Y => Y ≠ X), (c Y : ℝ) * a X Y = (c X : ℝ) - 1

/-- The type-uniform seed weight: `a X Y / (c X - 1)` on type `XXY`. -/
def seedW (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) (m : Multiset (Fin k)) : ℝ :=
  ∑ X, ∑ Y, if X ≠ Y ∧ m = {X, X, Y} then a X Y / ((c X : ℝ) - 1) else 0

theorem seedW_xxy (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {X Y : Fin k} (h : X ≠ Y) :
    seedW c a {X, X, Y} = a X Y / ((c X : ℝ) - 1) := by
  unfold seedW
  rw [Fintype.sum_eq_single X, Fintype.sum_eq_single Y]
  · rw [if_pos ⟨h, rfl⟩]
  · intro Y' hY'
    rw [if_neg]
    rintro ⟨h', e⟩
    exact hY' ((xxy_inj h h' e).2).symm
  · intro X' hX'
    refine Fintype.sum_eq_zero _ fun Y' => ?_
    rw [if_neg]
    rintro ⟨h', e⟩
    exact hX' ((xxy_inj h h' e).1).symm

/-- **H1**: the type-uniform seed is a diffuse seed with `C = 1/η + 2/δ`. -/
theorem kH1 {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k) {η δ : ℝ}
    {a : Fin k → Fin k → ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hseed : SeedData (ksz lab) η a)
    (hcls : ∀ X, δ * Fintype.card V ≤ ksz lab X) (h2 : 2 ≤ δ * Fintype.card V) :
    IsDiffuseSeed (kHost lab) (bicF k) (1 / η + 2 / δ)
      (fun T => seedW (ksz lab) a (T.val.map lab)) := by
  classical
  obtain ⟨hsum, hlow, hrow⟩ := hseed
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := by
    have : 0 < δ * n := by linarith
    exact pos_of_mul_pos_right this hδ.le
  have hle : ∀ X, (ksz lab X : ℝ) ≤ n := fun X => by
    have : ksz lab X ≤ Fintype.card V := by
      unfold ksz; exact card_le_univ _
    rw [hn]; exact_mod_cast this
  have hup : ∀ X Y, X ≠ Y → a X Y ≤ 1 := fun X Y h => by
    have := hsum X Y h; have := hlow Y X (Ne.symm h); linarith
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · -- bounds
    obtain ⟨X, Y, hXY, hm⟩ := bicF_cases hT.2.2
    have hm' : T.val.map lab = {X, X, Y} := hm
    show 1 / ((1 / η + 2 / δ) * n) ≤ seedW (ksz lab) a (T.val.map lab) ∧
      seedW (ksz lab) a (T.val.map lab) ≤ (1 / η + 2 / δ) / n
    rw [hm', seedW_xxy _ _ hXY]
    have hc := hcls X
    have hcX := hle X
    have hpos : 0 < (ksz lab X : ℝ) - 1 := by linarith
    have hA := hlow X Y hXY
    have hB := hup X Y hXY
    constructor
    · rw [div_le_div_iff₀ (by positivity) hpos]
      have hc1 : (ksz lab X : ℝ) - 1 ≤ n := by linarith
      have h1 : 1 / η * n * η = n := by field_simp
      have q1 : 1 / η * n ≤ (1 / η + 2 / δ) * n := by
        have : 0 ≤ 2 / δ * n := by positivity
        nlinarith
      have q2 : 1 / η * n * η ≤ (1 / η + 2 / δ) * n * η :=
        mul_le_mul_of_nonneg_right q1 hη.le
      have q3 : (1 / η + 2 / δ) * n * η ≤ (1 / η + 2 / δ) * n * a X Y :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      nlinarith
    · rw [div_le_div_iff₀ hpos hn0]
      have h3 : δ * n / 2 ≤ (ksz lab X : ℝ) - 1 := by linarith
      have h4 : 2 / δ * (δ * n / 2) = n := by field_simp
      have h5 : 0 ≤ 1 / η * ((ksz lab X : ℝ) - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 / δ)]
  · -- edge sums
    induction e using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := he
    rw [CDRBicolour.Absorption.edge_sum_top' lab (bicF k) (seedW (ksz lab) a) huv _ ?hS]
    case hS =>
      intro T
      convert (mem_filter (s := allowed (⟨⊤, lab⟩ : Host V (Fin k)) (bicF k))
        (p := fun T => s(u, v) ∈ triEdges T) (a := T))
    rw [CDRBicolour.Absorption.sum_by_label lab (fun X => ({lab u, lab v, X} :
      Multiset (Fin k)) ∈ bicF k) (fun X => seedW (ksz lab) a {lab u, lab v, X})]
    simp only [CDRBicolour.Absorption.card_third lab huv]
    have hcard : ∀ X, ((univ.filter fun z => lab z = X).card : ℝ) = (ksz lab X : ℝ) := fun _ => rfl
    simp only [hcard]
    generalize hi : lab u = i
    generalize hj : lab v = j
    by_cases hij : i = j
    · subst hij
      have hci : 0 < (ksz lab i : ℝ) - 1 := by have := hcls i; linarith
      calc _ = ∑ Y, if Y ≠ i then (ksz lab Y : ℝ) * a i Y / ((ksz lab i : ℝ) - 1) else 0 := by
              refine Fintype.sum_congr _ _ fun Y => ?_
              by_cases hY : Y = i
              · subst hY
                have hnot : ({Y, Y, Y} : Multiset (Fin k)) ∉ bicF k := by
                  intro hm; rcases mem_bicF.1 hm with h | h | h <;> exact h.2 rfl
                rw [if_neg hnot, if_neg (not_not.2 rfl)]
              · rw [if_pos (mem_bicF.2 (Or.inl ⟨rfl, Ne.symm hY⟩)), if_pos hY, if_neg (Ne.symm hY),
                  seedW_xxy _ _ (Ne.symm hY)]
                ring
        _ = (∑ Y ∈ univ.filter (fun Y => Y ≠ i), (ksz lab Y : ℝ) * a i Y) /
              ((ksz lab i : ℝ) - 1) := by
              rw [sum_div, sum_filter]
        _ = 1 := by rw [hrow i, div_self hci.ne']
    · have hci : 0 < (ksz lab i : ℝ) - 1 := by have := hcls i; linarith
      have hcj : 0 < (ksz lab j : ℝ) - 1 := by have := hcls j; linarith
      rw [Fintype.sum_eq_add i j hij]
      · rw [if_pos (mem_bicF.2 (Or.inr (Or.inl ⟨rfl, hij⟩))),
          if_pos (mem_bicF.2 (Or.inr (Or.inr ⟨rfl, hij⟩))), perm_aba, perm_abb,
          seedW_xxy _ _ hij, seedW_xxy _ _ (Ne.symm hij), if_pos rfl, if_neg (Ne.symm hij),
          if_neg hij, if_pos rfl]
        field_simp
        linear_combination (((ksz lab i : ℝ) - 1) * ((ksz lab j : ℝ) - 1)) * hsum i j hij
      · intro Z ⟨hZi, hZj⟩
        rw [if_neg]
        rw [mem_bicF]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hij h1
        · exact hZi h1.symm
        · exact hZj h1.symm

end CDRBicolour.KBicolor
