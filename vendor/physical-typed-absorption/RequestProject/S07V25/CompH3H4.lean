/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.LinkRobust
public import RequestProject.S07V25.InduceTransfer
public import RequestProject.S07V25.RobustExpansion
public import RequestProject.S07V25.RobustCover
public import RequestProject.S07.Compose

@[expose] public section

/-!
# V25 — `S07V24.CompInterface` discharged from the ORIGINAL H3/H4, one component at a time

For a host `(G, lab, F)` satisfying `CommonNbrCond G lab F α` (H3) and `HingeCond G lab F α h`
(H4), both UNCHANGED, and for every ACTIVE component `C = comp G lab F v x₀` of the typed link
`L_v = ComponentRows.link G lab F v` (`x₀` non-isolated), `compInterface_H3H4` proves
`S07V24.CompInterface L_v α κ n C (IsBip G lab F (v, C)) (colG G lab F v)` with

* `κ = kappaOf α h = ρ² / 2`, `ρ = rhoOf α h = min 1 (α / (8 · 2^(h choose 2)))`,
* threshold `n ≥ n1Of α = ⌈3/α⌉₊ + 1`,

all fixed from `(α, h)` BEFORE the host. Route: H3 ⇒ link degrees `≥ αn` (`link_degree_ge`);
H4 ⇒ the link is locally robust with even paths (`link_evenRobust`, budgets `s = ⌊ρn⌋`,
`d = 2s`); restriction to the closed set `C` (`induce_evenRobust`); robust connectivity
(`conn_of_local`) and expansion (`expansion_of_conn`) of `L_v[C]`; in the non-bipartite case the
same on the double cover `S07V24.dcover L_v[C]` (`cover_local` pays the factor `2` in the degree
budget, `cover_preconnected` uses the absence of a proper colouring). The colouring of a
bipartite component is the existing `ComponentRows.col` of the row `(v, C)`.
-/

open Finset

namespace S07V25

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24

/-- the robustness rate -/
noncomputable def rhoOf (α : ℝ) (h : ℕ) : ℝ := min 1 (α / (8 * 2 ^ (h.choose 2)))

/-- the expansion constant (fixed from `α`, `h` before the host) -/
noncomputable def kappaOf (α : ℝ) (h : ℕ) : ℝ := rhoOf α h ^ 2 / 2

/-- the size threshold -/
noncomputable def n1Of (α : ℝ) : ℕ := ⌈3 / α⌉₊ + 1

lemma rhoOf_pos {α : ℝ} (hα : 0 < α) (h : ℕ) : 0 < rhoOf α h :=
  lt_min one_pos (by positivity)

lemma rhoOf_le_one (α : ℝ) (h : ℕ) : rhoOf α h ≤ 1 := min_le_left _ _

lemma kappaOf_pos {α : ℝ} (hα : 0 < α) (h : ℕ) : 0 < kappaOf α h := by
  have := rhoOf_pos hα h; unfold kappaOf; positivity

/-- the row colouring, one function per root -/
noncomputable def colG {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (v x : V) : Bool :=
  col G lab F (v, comp G lab F v x) x

/-- conversion of the natural-number expansion bound -/
lemma real_conv {ρ : ℝ} {n T s d cut : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hT : T ≤ n)
    (hd : ρ * n ≤ d + 1) (hs : ρ * n ≤ s + 1) (h : (d + 1) * min T (s + 1) ≤ 2 * cut) :
    ρ ^ 2 / 2 * n * T ≤ cut := by
  have hTR : (T : ℝ) ≤ n := by exact_mod_cast hT
  have hmin : ρ * T ≤ (min T (s + 1) : ℕ) := by
    rcases le_total T (s + 1) with h1 | h1
    · rw [min_eq_left h1]
      have : (0 : ℝ) ≤ T := by positivity
      nlinarith
    · rw [min_eq_right h1]; push_cast
      nlinarith
  have hR : ((d + 1 : ℕ) : ℝ) * (min T (s + 1) : ℕ) ≤ 2 * cut := by exact_mod_cast h
  have hd' : ρ * n ≤ ((d + 1 : ℕ) : ℝ) := by push_cast; exact hd
  have h0' : (0 : ℝ) ≤ ρ * T := by positivity
  have key := mul_le_mul hd' hmin h0' (by positivity)
  nlinarith

variable {V I : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma mem_comp_iff {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x y : V} :
    y ∈ comp G lab F v x ↔ (link G lab F v).Reachable x y := by
  simp [comp]

omit [DecidableEq V] in
lemma comp_eq_of_mem {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x y : V}
    (hy : y ∈ comp G lab F v x) : comp G lab F v y = comp G lab F v x := by
  rw [mem_comp_iff] at hy
  ext z; rw [mem_comp_iff, mem_comp_iff]
  exact ⟨fun h => hy.trans h, fun h => hy.symm.trans h⟩

omit [DecidableEq V] in
lemma comp_closed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} (v x : V) :
    NbrClosed (link G lab F v) (comp G lab F v x : Set V) := by
  intro y z hy hyz
  simp only [Finset.mem_coe, mem_comp_iff] at hy ⊢
  exact hy.trans hyz.reachable

omit [DecidableEq V] in
lemma comp_active {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x0 : V}
    (hx0 : ∃ y, (link G lab F v).Adj x0 y) {w : V} (hw : w ∈ comp G lab F v x0) :
    ∃ y, (link G lab F v).Adj w y := by
  rw [mem_comp_iff] at hw
  by_cases hwx : w = x0
  · subst hwx; exact hx0
  obtain ⟨p⟩ := hw.symm
  cases p with
  | nil => exact absurd rfl hwx
  | cons h _ => exact ⟨_, h⟩

/-- **the S03 §§4–6 interface of one active component, from the ORIGINAL H3/H4** -/
theorem compInterface_H3H4 {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ}
    {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (hn : n1Of α ≤ Fintype.card V) (v x0 : V) (hx0 : ∃ y, (link G lab F v).Adj x0 y)
    [DecidableRel (link G lab F v).Adj] :
    CompInterface (link G lab F v) α (kappaOf α h) (Fintype.card V) (comp G lab F v x0)
      (IsBip G lab F (v, comp G lab F v x0)) (colG G lab F v) := by
  set C := comp G lab F v x0 with hCdef
  set n := Fintype.card V with hndef
  set ρ := rhoOf α h with hρdef
  set M : ℝ := 2 ^ (h.choose 2) with hM
  have hρ := rhoOf_pos hα h
  have hρ1 := rhoOf_le_one α h
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
  -- H4 ⇒ even local robustness of the link
  have hsd : ((s : ℝ) + 3 * ((2 * s : ℕ) : ℝ)) * 2 ^ (h.choose 2) < α * n := by
    push_cast
    have : (s : ℝ) * M ≤ ρ * n * M := mul_le_mul_of_nonneg_right hs1 (by positivity)
    have h8 : ρ * n * M * 8 ≤ α * n := by nlinarith
    rw [← hM]; nlinarith
  have hER : EvenRobustLocal (link G lab F v) s (2 * s) := by
    convert link_evenRobust hH4 v s (2 * s) hsd
  have hCl : NbrClosed (link G lab F v) (C : Set V) := comp_closed v x0
  have hERK : EvenRobustLocal ((link G lab F v).induce (C : Set V)) s (2 * s) := induce_evenRobust hCl hER
  have hpre : ((link G lab F v).induce (C : Set V)).Preconnected :=
    induce_preconnected hCl x0 (fun x hx => mem_comp_iff.1 hx)
  -- H3 ⇒ degrees
  have hdegK : ∀ w : (C : Set V), α * n ≤ ((link G lab F v).induce (C : Set V)).degree w := by
    intro w
    have h1 : α * n ≤ (link G lab F v).degree w.1 := by
      convert link_degree_ge hH3 v w.1 (comp_active hx0 w.2)
    exact h1.trans (by exact_mod_cast induce_degree_ge hCl w)
  have hdeg2 : ∀ w : (C : Set V), s + 2 ≤ ((link G lab F v).induce (C : Set V)).degree w := by
    intro w
    have h1 := hdegK w
    have : (s : ℝ) + 2 < ((link G lab F v).induce (C : Set V)).degree w := by nlinarith
    exact_mod_cast this.le
  have hcardC : Fintype.card (C : Set V) ≤ n := by
    rw [hndef]; exact Fintype.card_subtype_le _
  refine ⟨fun w => hdegK w, fun w => ?_, fun hb => ?_, fun hnb => ?_⟩
  · have := SimpleGraph.degree_lt_card_verts (G := (link G lab F v).induce (C : Set V)) w
    exact_mod_cast (this.trans_le hcardC).le
  · -- bipartite component
    refine ⟨fun w w' hww' => ?_, fun T hT => ?_⟩
    · have e1 : colG G lab F v w.1 = col G lab F (v, C) w.1 := by
        unfold colG; rw [comp_eq_of_mem w.2]
      have e2 : colG G lab F v w'.1 = col G lab F (v, C) w'.1 := by
        unfold colG; rw [comp_eq_of_mem w'.2]
      rw [e1, e2]
      unfold col; rw [dif_pos hb]
      exact Classical.choose_spec hb w.1 w.2 w'.1 w'.2 hww'
    · have hconn := conn_of_local ((link G lab F v).induce (C : Set V)) s (2 * s) hpre hERK.toLocal hdeg2
      have hexp := expansion_of_conn ((link G lab F v).induce (C : Set V)) s (2 * s) hconn T hT
      have hTn : T.card ≤ n := (card_le_univ T).trans hcardC
      have := real_conv (cut := cutCount ((link G lab F v).induce (C : Set V)) T) hρ hρ1 hTn
        (by push_cast; linarith) hs2.le hexp
      simpa [kappaOf] using this
  · -- non-bipartite component: the double cover
    intro T hT
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
    have hconn := conn_of_local (dcover ((link G lab F v).induce (C : Set V))) s s hcp hcl hdegc
    have hexp := expansion_of_conn (dcover ((link G lab F v).induce (C : Set V))) s s hconn T hT
    have hTn : T.card ≤ n := by
      rw [Fintype.card_prod, Fintype.card_bool] at hT; omega
    have := real_conv (cut := cutCount (dcover ((link G lab F v).induce (C : Set V))) T) hρ hρ1 hTn
      hs2.le hs2.le hexp
    simpa [kappaOf] using this

end S07V25
