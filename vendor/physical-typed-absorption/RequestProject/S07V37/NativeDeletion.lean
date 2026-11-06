/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V25.CompH3H4
public import RequestProject.TypedTriangle.RoutingInputs
@[expose] public section

/-!
# V37 — the routing deletion hypotheses from the ORIGINAL H3/H4

The routing endpoint `RoutingInputs.routing_budget_of_lower` / `routing_budget_real` consumes
two geometric inputs: the active-component lower bound `hlow` and the local deletion theorem
`hdel : ∀ A, |A| ≤ δ n → DeletionHyp G lab F A`. Here both are derived from H3
(`CommonNbrCond G lab F α`) and H4 (`HingeCond G lab F α h`), unchanged.

* `hlow_of_H3` — every active row `(v, K)` has `α n ≤ |K|`.
* `delOf α h = rhoOf α h / 4` — the deletion rate, fixed from `(α, h)` before the host.
* `deletionHyp_H3H4` — for `n ≥ n1Of α` and every `A` with `|A| ≤ delOf α h · n`,
  `DeletionHyp G lab F A` holds: survivors of an active component stay connected in
  `linkA a A` (robust connectivity of `L_a[C]`, `conn_of_local`); a non-bipartite component
  stays non-bipartite (robust connectivity of the double cover); `fresh` and `nonempty` follow
  from the H3 link degrees.
-/

open Finset Classical

noncomputable section

namespace S07V37

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open S07V24 S07V25

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- the deletion rate, fixed from `(α, h)` before the host -/
def delOf (α : ℝ) (h : ℕ) : ℝ := rhoOf α h / 4

lemma delOf_pos {α : ℝ} (hα : 0 < α) (h : ℕ) : 0 < delOf α h := by
  have := rhoOf_pos hα h; unfold delOf; positivity

/-- neighbours of a vertex of a component lie in the component -/
lemma nbr_subset_comp (v x : V) :
    (link G lab F v).neighborFinset x ⊆ comp G lab F v x := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  exact mem_comp_iff.2 hy.reachable

/-- **`hlow` from H3**: every active row `(v, K)` has `α n ≤ |K|`. -/
theorem hlow_of_H3 {α : ℝ} (hH3 : CommonNbrCond G lab F α) :
    ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card := by
  rintro ⟨v, K⟩ ⟨u, hu, hK⟩
  simp only at hu hK ⊢
  subst hK
  have h1 := link_degree_ge hH3 v u hu
  have h2 : (link G lab F v).degree u ≤ (comp G lab F v u).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact card_le_card (nbr_subset_comp v u)
  exact h1.trans (by exact_mod_cast h2)

/-- numeric window: `2 |A| ≤ ⌊ρ n⌋`, `|A| < α n` and `⌊ρ n⌋ + 2 ≤` every link degree budget -/
lemma del_window {α : ℝ} (hα : 0 < α) (h : ℕ) {n a : ℕ} (hn : n1Of α ≤ n)
    (ha : (a : ℝ) ≤ delOf α h * n) :
    2 * a ≤ ⌊rhoOf α h * n⌋₊ ∧ (a : ℝ) < α * n ∧
      ((⌊rhoOf α h * n⌋₊ : ℝ) + 3 * ((2 * ⌊rhoOf α h * n⌋₊ : ℕ) : ℝ)) * 2 ^ (h.choose 2) <
        α * n ∧ (⌊rhoOf α h * n⌋₊ : ℝ) + 2 < α * n := by
  set ρ := rhoOf α h with hρdef
  set M : ℝ := 2 ^ (h.choose 2) with hM
  have hρ := rhoOf_pos hα h
  have hM1 : (1 : ℝ) ≤ M := one_le_pow₀ (by norm_num)
  have hρM : ρ * (8 * M) ≤ α := by
    have : ρ ≤ α / (8 * M) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  have hnR : (3 / α : ℝ) < n := by
    have h1 := Nat.le_ceil (3 / α)
    have h2 : ((⌈3 / α⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; linarith
  have hαn : 3 < α * n := by
    rw [div_lt_iff₀ hα] at hnR; linarith
  have hnpos : (0 : ℝ) < n := by
    by_contra hc; push_neg at hc; nlinarith
  set s := ⌊ρ * n⌋₊ with hsdef
  have hs1 : (s : ℝ) ≤ ρ * n := Nat.floor_le (by positivity)
  have hs2 : ρ * n < s + 1 := Nat.lt_floor_add_one _
  have hρα : ρ * 8 ≤ α := by nlinarith
  have ha' : (a : ℝ) ≤ ρ / 4 * n := ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    push_cast
    nlinarith
  · nlinarith
  · push_cast
    have : (s : ℝ) * M ≤ ρ * n * M := mul_le_mul_of_nonneg_right hs1 (by positivity)
    have h8 : ρ * n * M * 8 ≤ α * n := by nlinarith
    nlinarith
  · have : (s : ℝ) * M ≤ ρ * n * M := mul_le_mul_of_nonneg_right hs1 (by positivity)
    have h8 : ρ * n * M * 8 ≤ α * n := by nlinarith
    nlinarith

/-- robust connectivity of an active component and of its double cover (non-bipartite case),
from the ORIGINAL H3/H4 (the same route as `compInterface_H3H4`) -/
theorem comp_robust {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V) (v x0 : V)
    (hx0 : ∃ y, (link G lab F v).Adj x0 y) :
    S07V25.RobustConn ((link G lab F v).induce (comp G lab F v x0 : Set V))
        ⌊rhoOf α h * Fintype.card V⌋₊ (2 * ⌊rhoOf α h * Fintype.card V⌋₊) ∧
      (¬ IsBip G lab F (v, comp G lab F v x0) →
        S07V25.RobustConn (dcover ((link G lab F v).induce (comp G lab F v x0 : Set V)))
          ⌊rhoOf α h * Fintype.card V⌋₊ ⌊rhoOf α h * Fintype.card V⌋₊) := by
  set C := comp G lab F v x0 with hCdef
  set n := Fintype.card V with hndef
  set s := ⌊rhoOf α h * n⌋₊ with hsdef
  obtain ⟨-, -, hsd, hs2⟩ := del_window (a := 0) hα h hn (by
    have := delOf_pos hα h; simp only [Nat.cast_zero]; positivity)
  have hER : EvenRobustLocal (link G lab F v) s (2 * s) := link_evenRobust hH4 v s (2 * s) hsd
  have hCl : NbrClosed (link G lab F v) (C : Set V) := comp_closed v x0
  have hERK : EvenRobustLocal ((link G lab F v).induce (C : Set V)) s (2 * s) :=
    induce_evenRobust hCl hER
  have hpre : ((link G lab F v).induce (C : Set V)).Preconnected :=
    induce_preconnected hCl x0 (fun x hx => mem_comp_iff.1 hx)
  have hdeg2 : ∀ w : (C : Set V), s + 2 ≤ ((link G lab F v).induce (C : Set V)).degree w := by
    intro w
    have h1 : α * n ≤ (link G lab F v).degree w.1 := link_degree_ge hH3 v w.1 (comp_active hx0 w.2)
    have h2 := induce_degree_ge hCl w
    have : (s : ℝ) + 2 < ((link G lab F v).induce (C : Set V)).degree w := by
      have : ((link G lab F v).degree w.1 : ℝ) ≤ ((link G lab F v).induce (C : Set V)).degree w := by
        exact_mod_cast h2
      linarith
    exact_mod_cast this.le
  refine ⟨conn_of_local _ s (2 * s) hpre hERK.toLocal hdeg2, fun hnb => ?_⟩
  have hnocol : ¬ ∃ c : ↥(C : Set V) → Bool,
      ∀ x y, ((link G lab F v).induce (C : Set V)).Adj x y → c x ≠ c y := by
    rintro ⟨c, hc⟩
    apply hnb
    refine ⟨fun x => if hx : x ∈ C then c ⟨x, hx⟩ else false, fun x hx y hy hxy => ?_⟩
    simp only [dif_pos hx, dif_pos hy]
    exact hc ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hcp := cover_preconnected ((link G lab F v).induce (C : Set V)) hpre hnocol
  have hcl := cover_local ((link G lab F v).induce (C : Set V)) s s hERK
  have hdegc : ∀ w, s + 2 ≤ (dcover ((link G lab F v).induce (C : Set V))).degree w := by
    rintro ⟨w, b⟩; rw [dcover_degree]; exact hdeg2 w
  exact conn_of_local (dcover ((link G lab F v).induce (C : Set V))) s s hcp hcl hdegc

omit [Fintype V] in
/-- walks of `L[C]` avoiding `A` are walks of `linkA a A` -/
lemma reach_linkA_of_walk {a : V} {A : Finset V} {C : Set V}
    {x y : C} (p : ((link G lab F a).induce C).Walk x y) (hp : ∀ z ∈ p.support, z.1 ∉ A) :
    (linkA G lab F a A).Reachable x.1 y.1 := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj q ih =>
    rename_i u w z
    have hu : u.1 ∉ A := hp _ (SimpleGraph.Walk.start_mem_support _)
    have hw : w.1 ∉ A := hp _ (by simp)
    have h1 : (linkA G lab F a A).Adj u.1 w.1 := ⟨hadj, hu, hw⟩
    exact h1.reachable.trans (ih fun z hz => hp z (by simp [hz]))

omit [Fintype V] in
/-- along a walk of the double cover avoiding `A`, `col ⊕ sheet` is constant -/
lemma cover_walk_const {a : V} {A : Finset V} {C : Finset V} (col : V → Bool)
    (hcol : ∀ u ∈ C, ∀ w ∈ C, (linkA G lab F a A).Adj u w → col u ≠ col w)
    {x y : ↥(C : Set V) × Bool}
    (p : (dcover ((link G lab F a).induce (C : Set V))).Walk x y)
    (hp : ∀ z ∈ p.support, z.1.1 ∉ A) :
    xor (col x.1.1) x.2 = xor (col y.1.1) y.2 := by
  induction p with
  | nil => rfl
  | cons hadj q ih =>
    rename_i u w z
    have hu : u.1.1 ∉ A := hp _ (SimpleGraph.Walk.start_mem_support _)
    have hw : w.1.1 ∉ A := hp _ (by simp)
    have h1 : (linkA G lab F a A).Adj u.1.1 w.1.1 := ⟨hadj.1, hu, hw⟩
    have hne := hcol _ u.1.2 _ w.1.2 h1
    have hsheet := hadj.2
    rw [← ih fun z hz => hp z (by simp [hz])]
    revert hne hsheet
    cases col u.1.1 <;> cases col w.1.1 <;> cases u.2 <;> cases w.2 <;> simp

/-- **The routing deletion hypotheses from the ORIGINAL H3/H4.** For `n ≥ n1Of α` and every
`A` with `|A| ≤ delOf α h · n`, `DeletionHyp G lab F A`. -/
theorem deletionHyp_H3H4 {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V) (A : Finset V)
    (hA : (A.card : ℝ) ≤ delOf α h * Fintype.card V) : DeletionHyp G lab F A := by
  obtain ⟨h2A, hAα, -, -⟩ := del_window hα h hn hA
  set s := ⌊rhoOf α h * Fintype.card V⌋₊
  have hAs : A.card ≤ s := by omega
  -- nonempty survivors
  have hne : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∃ u ∈ K, u ∉ A := by
    intro a _ K hK
    by_contra hc
    push_neg at hc
    have h1 := hlow_of_H3 hH3 (a, K) hK
    have h2 : K.card ≤ A.card := card_le_card hc
    have : (K.card : ℝ) ≤ A.card := by exact_mod_cast h2
    simp only at h1
    linarith
  refine ⟨?_, ?_, ?_, hne⟩
  · -- conn
    rintro a - K ⟨x0, hx0, hK⟩ u hu w hw huA hwA
    simp only at hx0 hK
    subst hK
    obtain ⟨hconn, -⟩ := comp_robust hα hH3 hH4 hn a x0 hx0
    set C := comp G lab F a x0
    let S : Finset ↥(C : Set V) := univ.filter fun z => z.1 ∈ A
    have hS : S.card ≤ s := by
      refine le_trans ?_ hAs
      refine card_le_card_of_injOn (fun z => z.1) (fun z hz => by simpa [S] using hz) ?_
      intro z _ z' _ e; exact Subtype.ext e
    obtain ⟨p, hp, -⟩ := hconn S hS ∅ (fun x => by simp [degB]) ⟨u, hu⟩ ⟨w, hw⟩
      (by simpa [S] using huA) (by simpa [S] using hwA)
    exact reach_linkA_of_walk p fun z hz => by simpa [S] using hp z hz
  · -- bip
    rintro a ha K hK hnb ⟨col, hcol⟩
    obtain ⟨x0, hx0, hK⟩ := hK
    simp only at hx0 hK
    subst hK
    obtain ⟨-, hcov⟩ := comp_robust hα hH3 hH4 hn a x0 hx0
    have hconn := hcov hnb
    set C := comp G lab F a x0
    obtain ⟨u, hu, huA⟩ := hne a ha C ⟨x0, hx0, rfl⟩
    let S : Finset (↥(C : Set V) × Bool) := univ.filter fun z => z.1.1 ∈ A
    have hS : S.card ≤ s := by
      have : S ⊆ (univ.filter fun z : ↥(C : Set V) => z.1 ∈ A) ×ˢ univ := by
        intro z hz; simp only [S, mem_filter, mem_univ, true_and] at hz; simp [hz]
      refine (card_le_card this).trans ?_
      rw [card_product, card_univ, Fintype.card_bool]
      have : (univ.filter fun z : ↥(C : Set V) => z.1 ∈ A).card ≤ A.card :=
        card_le_card_of_injOn (fun z => z.1) (fun z hz => by simpa using hz)
          (fun z _ z' _ e => Subtype.ext e)
      omega
    obtain ⟨p, hp, -⟩ := hconn S hS ∅ (fun x => by simp [degB]) (⟨u, hu⟩, true) (⟨u, hu⟩, false)
      (by simpa [S] using huA) (by simpa [S] using huA)
    have := cover_walk_const col hcol p fun z hz => by simpa [S] using hp z hz
    revert this
    cases col u <;> simp
  · -- fresh
    intro a _ b _ hab
    by_contra hc
    push_neg at hc
    have h1 := link_degree_ge hH3 a b hab
    have h2 : (link G lab F a).neighborFinset b ⊆ A := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      by_contra hwA; exact hc w hwA hw
    have h3 := card_le_card h2
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h3
    have : ((link G lab F a).degree b : ℝ) ≤ A.card := by exact_mod_cast h3
    linarith

end S07V37
