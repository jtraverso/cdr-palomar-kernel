/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.RobustPaths

@[expose] public section

/-!
# Bounded odd simple paths from robust components (S07 §2) — V20

Pure graph theory on an arbitrary graph `H` (to be instantiated with the typed link
`L_v(H, F)`), and a vertex set `K` (an active component).  The robustness inputs are explicit
hypotheses, i.e. obligations to be instantiated from H3–H4; they are NOT added to T.

* `RobustDiam H K M D` : for every deleted set `Y`, `|Y| ≤ M`, any two survivors `x, y ∈ K \ Y`
  are joined by a walk of length `≤ D` all of whose vertices lie in `K \ Y`.
  (`robustDiam_of_closed`: if `K` is closed under adjacency — e.g. a component — it suffices
  that the walk avoids `Y`.)
* `RobustNonBip H K M` : for every `Y`, `|Y| ≤ M`, the survivors `K \ Y` have no proper
  2-colouring (in particular they are nonempty).

Proved here:

1. `exists_loop_of_not_isPath` : a walk that is not a path contains a nontrivial closed
   subwalk (with exact length bookkeeping).
2. `exists_adj_evenPath_of_odd_loop` : an odd closed walk of length `L` yields an edge
   `c0 c1` and a simple path `c1 → c0` of even length `≤ L - 1` inside its support, i.e. a
   simple odd cycle of length `≤ L`.
3. `exists_short_odd_loop` : diameter `≤ D` plus non-2-colourability of a vertex set `W` give
   an odd closed walk of length `≤ 2D+1` inside `W` (parity of chosen root walks; no cycle is
   assumed).
4. `short_odd_cycle` : combination; a simple odd cycle of length `≤ 2D+1` in `W`.
5. `isPath_append_of` : concatenation of two paths meeting only at the junction is a path.
6. **`odd_path_nonbip`** : if `B + 3D + 1 ≤ M` (in particular for the S07 slack `B + 3D + 4`),
   `RobustDiam H K M D` and `RobustNonBip H K M`, then for every `Z`, `|Z| ≤ B`, and all distinct
   `a, b ∈ K \ Z` there is a SIMPLE path `a → b` of ODD length `≤ 4D + 1` inside `K \ Z`.
   Forbidden sets used: `Z ∪ {a,b}` (`≤ B+2`), `Z ∪ {b} ∪ (C \ {c0})` (`≤ B+2D+1`),
   `Z ∪ V(P) ∪ (C \ {c1})` (`≤ B+3D+1`).
7. **`odd_path_bip`** : if `K` is bipartite with side `X` and `RobustDiam H K M D`, `B ≤ M`,
   then two survivors on opposite sides are joined by a simple odd path of length `≤ D`.
8. **`robustOddPaths_nonbip`**, **`robustOddPaths_bip`** : `SelEmbed.RobustOddPaths` with
   `ℓ = 4D + 1` is a CONCLUSION (PAR: any two distinct vertices of `K`; BAL: opposite sides).
-/

namespace SelRoute

open Finset SimpleGraph SelEmbed

variable {V : Type*} {H : SimpleGraph V}

/-! ### Walk surgery -/

/-- A walk that is not a path contains a nontrivial closed subwalk. -/
theorem exists_loop_of_not_isPath [DecidableEq V] : ∀ {a b : V} (p : H.Walk a b), ¬ p.IsPath →
    ∃ x, ∃ (p1 : H.Walk a x) (c : H.Walk x x) (p2 : H.Walk x b),
      p1.length + c.length + p2.length = p.length ∧ 0 < c.length ∧
      p1.support ⊆ p.support ∧ c.support ⊆ p.support ∧ p2.support ⊆ p.support
  | _, _, .nil, hp => absurd Walk.IsPath.nil hp
  | a, b, .cons h q, hp => by
    by_cases ha : a ∈ q.support
    · refine ⟨a, .nil, .cons h (q.takeUntil a ha), q.dropUntil a ha, ?_, by simp, ?_, ?_, ?_⟩
      · have := congrArg Walk.length (q.take_spec ha)
        rw [Walk.length_append] at this
        simp [Walk.length_cons]; omega
      · simp
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (q.support_takeUntil_subset ha hx)
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr (q.support_dropUntil_subset ha hx)
    · have hq : ¬ q.IsPath := fun hq => hp ((Walk.cons_isPath_iff h q).mpr ⟨hq, ha⟩)
      obtain ⟨x, p1, c, p2, hl, hc, h1, h2, h3⟩ := exists_loop_of_not_isPath q hq
      refine ⟨x, .cons h p1, c, p2, by simp [Walk.length_cons]; omega, hc, ?_, ?_, ?_⟩
      · intro y hy
        simp only [Walk.support_cons, List.mem_cons] at hy ⊢
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (h1 hy)
      · intro y hy; simp only [Walk.support_cons, List.mem_cons]; exact Or.inr (h2 hy)
      · intro y hy; simp only [Walk.support_cons, List.mem_cons]; exact Or.inr (h3 hy)

/-- **Odd closed walk ⇒ simple odd cycle.**  An odd closed walk of length `≤ n` gives an edge
`c0 c1` and a simple path `R : c1 → c0` of even length, `|R| + 1 ≤ |w|`, inside the support of
`w`; `R` together with the edge is a simple odd cycle. -/
theorem exists_adj_evenPath_of_odd_loop [DecidableEq V] : ∀ (n : ℕ) {u : V} (w : H.Walk u u),
    w.length ≤ n → Odd w.length →
    ∃ c0 c1, H.Adj c0 c1 ∧ ∃ R : H.Walk c1 c0, R.IsPath ∧ Even R.length ∧
      R.length + 1 ≤ w.length ∧ R.support ⊆ w.support := by
  intro n
  induction n with
  | zero => intro u w hw ho; rw [Nat.le_zero.mp hw] at ho; exact absurd ho (by decide)
  | succ n ih =>
    intro u w hw ho
    cases w with
    | nil => exact absurd ho (by simp)
    | cons h w' =>
      rw [Walk.length_cons] at hw ho
      by_cases hp : w'.IsPath
      · refine ⟨_, _, h, w', hp, ?_, by simp [Walk.length_cons], ?_⟩
        · rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩
        · intro x hx; simp [hx]
      · obtain ⟨x, p1, c, p2, hl, hc, h1, h2, h3⟩ := exists_loop_of_not_isPath w' hp
        have hsub : w'.support ⊆ (Walk.cons h w').support := fun y hy => by simp [hy]
        rcases Nat.even_or_odd c.length with hce | hco
        · obtain ⟨c0, c1, hadj, R, hR, hRe, hRl, hRs⟩ :=
            ih (Walk.cons h (p1.append p2)) (by simp [Walk.length_cons]; omega)
              (by
                simp only [Walk.length_cons, Walk.length_append]
                rcases ho with ⟨k, hk⟩; rcases hce with ⟨m, hm⟩; exact ⟨k - m, by omega⟩)
          refine ⟨c0, c1, hadj, R, hR, hRe, ?_, ?_⟩
          · simp only [Walk.length_cons, Walk.length_append] at hRl ⊢; omega
          · intro y hy
            have := hRs hy
            simp only [Walk.support_cons, Walk.support_append, List.mem_cons,
              List.mem_append] at this ⊢
            rcases this with rfl | hy | hy
            · exact Or.inl rfl
            · exact Or.inr (h1 hy)
            · exact Or.inr (h3 (List.mem_of_mem_tail hy))
        · obtain ⟨c0, c1, hadj, R, hR, hRe, hRl, hRs⟩ := ih c (by omega) hco
          exact ⟨c0, c1, hadj, R, hR, hRe, by simp [Walk.length_cons]; omega,
            fun y hy => hsub (h2 (hRs hy))⟩

/-- **Short odd closed walk from diameter and non-bipartiteness.**  If any two vertices of `W`
are joined by walks of length `≤ D` inside `W`, and `W` has no proper 2-colouring, then `W`
contains an odd closed walk of length `≤ 2D+1`.  (Colour each vertex by the parity of a chosen
root walk; a monochromatic edge closes an odd walk.) -/
theorem exists_short_odd_loop (W : Set V) (D : ℕ)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, ∃ p : H.Walk x y, p.length ≤ D ∧ ∀ z ∈ p.support, z ∈ W)
    (hnb : ¬ ∃ col : V → Bool, ∀ x ∈ W, ∀ y ∈ W, H.Adj x y → col x ≠ col y) :
    ∃ u, ∃ w : H.Walk u u, Odd w.length ∧ w.length ≤ 2 * D + 1 ∧ ∀ z ∈ w.support, z ∈ W := by
  classical
  obtain ⟨r, hr⟩ : W.Nonempty := by
    by_contra hW
    rw [Set.not_nonempty_iff_eq_empty] at hW
    exact hnb ⟨fun _ => true, fun x hx => by simp [hW] at hx⟩
  by_contra hcon
  choose f hf using fun x (hx : x ∈ W) => hdiam r hr x hx
  apply hnb
  refine ⟨fun x => if hx : x ∈ W then decide (Even (f x hx).length) else true, ?_⟩
  intro x hx y hy hxy hcol
  simp only [hx, hy, dite_true, decide_eq_decide] at hcol
  apply hcon
  refine ⟨r, (f x hx).append (Walk.cons hxy (f y hy).reverse), ?_, ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]
    rcases Nat.even_or_odd (f x hx).length with h | h
    · have h' := hcol.mp h
      rcases h with ⟨a, ha⟩; rcases h' with ⟨b, hb⟩; exact ⟨a + b, by omega⟩
    · have h' : Odd (f y hy).length := by
        rw [← Nat.not_even_iff_odd] at h ⊢; rwa [← hcol]
      rcases h with ⟨a, ha⟩; rcases h' with ⟨b, hb⟩; exact ⟨a + b + 1, by omega⟩
  · simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]
    have := (hf x hx).1; have := (hf y hy).1; omega
  · intro z hz
    simp only [Walk.support_append, Walk.support_cons, Walk.support_reverse, List.mem_append,
      List.tail_cons, List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact (hf x hx).2 z hz
    · exact (hf y hy).2 z hz

/-- **Short simple odd cycle**: an edge `c0 c1` and a simple path `c1 → c0` of even length
`≤ 2D`, inside `W` (a simple odd cycle of length `≤ 2D+1`). -/
theorem short_odd_cycle (W : Set V) (D : ℕ)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, ∃ p : H.Walk x y, p.length ≤ D ∧ ∀ z ∈ p.support, z ∈ W)
    (hnb : ¬ ∃ col : V → Bool, ∀ x ∈ W, ∀ y ∈ W, H.Adj x y → col x ≠ col y) :
    ∃ c0 c1, H.Adj c0 c1 ∧ ∃ R : H.Walk c1 c0, R.IsPath ∧ Even R.length ∧
      R.length ≤ 2 * D ∧ ∀ z ∈ R.support, z ∈ W := by
  classical
  obtain ⟨u, w, ho, hl, hs⟩ := exists_short_odd_loop W D hdiam hnb
  obtain ⟨c0, c1, hadj, R, hR, hRe, hRl, hRs⟩ := exists_adj_evenPath_of_odd_loop _ w le_rfl ho
  exact ⟨c0, c1, hadj, R, hR, hRe, by omega, fun z hz => hs z (hRs hz)⟩

/-- Concatenation of two paths meeting only at the junction is a path. -/
theorem isPath_append_of {a b c : V} (p : H.Walk a b) (q : H.Walk b c) (hp : p.IsPath)
    (hq : q.IsPath) (h : ∀ x ∈ p.support, x ∈ q.support → x = b) : (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append]
  have hqs := hq.support_nodup
  rw [Walk.support_eq_cons q, List.nodup_cons] at hqs
  refine ⟨hp.support_nodup, hqs.2, ?_⟩
  intro x hx y hy hxy
  subst hxy
  have := h x hx (Walk.support_eq_cons q ▸ List.mem_cons_of_mem _ hy)
  subst this
  exact hqs.1 hy

/-! ### Robustness hypotheses (obligations from H3–H4) -/

/-- Robust connectivity with diameter: after deleting any `Y`, `|Y| ≤ M`, every two survivors
of `K` are joined by a walk of length `≤ D` through survivors of `K`. -/
def RobustDiam (H : SimpleGraph V) (K : Finset V) (M D : ℕ) : Prop :=
  ∀ Y : Finset V, Y.card ≤ M → ∀ x ∈ K, ∀ y ∈ K, x ∉ Y → y ∉ Y →
    ∃ p : H.Walk x y, p.length ≤ D ∧ ∀ z ∈ p.support, z ∈ K ∧ z ∉ Y

/-- Robust non-bipartiteness: after deleting any `Y`, `|Y| ≤ M`, the survivors of `K` have no
proper 2-colouring. -/
def RobustNonBip (H : SimpleGraph V) (K : Finset V) (M : ℕ) : Prop :=
  ∀ Y : Finset V, Y.card ≤ M →
    ¬ ∃ col : V → Bool, ∀ x ∈ K, ∀ y ∈ K, x ∉ Y → y ∉ Y → H.Adj x y → col x ≠ col y

/-- Walks starting in a vertex set closed under adjacency stay inside it. -/
theorem support_subset_of_closed (K : Finset V) (hK : ∀ x ∈ K, ∀ y, H.Adj x y → y ∈ K) :
    ∀ {x y : V} (p : H.Walk x y), x ∈ K → ∀ z ∈ p.support, z ∈ K
  | _, _, .nil, hx, z, hz => by simp at hz; exact hz ▸ hx
  | _, _, .cons h p, hx, z, hz => by
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact support_subset_of_closed K hK p (hK _ hx _ h) z hz

/-- **Adapter for components**: if `K` is closed under adjacency, walks that merely avoid `Y`
give `RobustDiam`. -/
theorem robustDiam_of_closed (K : Finset V) (M D : ℕ) (hK : ∀ x ∈ K, ∀ y, H.Adj x y → y ∈ K)
    (h : ∀ Y : Finset V, Y.card ≤ M → ∀ x ∈ K, ∀ y ∈ K, x ∉ Y → y ∉ Y →
      ∃ p : H.Walk x y, p.length ≤ D ∧ ∀ z ∈ p.support, z ∉ Y) :
    RobustDiam H K M D := by
  intro Y hY x hx y hy hxY hyY
  obtain ⟨p, hl, hs⟩ := h Y hY x hx y hy hxY hyY
  exact ⟨p, hl, fun z hz => ⟨support_subset_of_closed K hK p hx z hz, hs z hz⟩⟩

theorem RobustDiam.mono {K : Finset V} {M M' D : ℕ} (h : RobustDiam H K M D) (hM : M' ≤ M) :
    RobustDiam H K M' D := fun Y hY => h Y (hY.trans hM)

theorem RobustNonBip.mono {K : Finset V} {M M' : ℕ} (h : RobustNonBip H K M) (hM : M' ≤ M) :
    RobustNonBip H K M' := fun Y hY => h Y (hY.trans hM)

/-- A simple connecting path from `RobustDiam` (by bypassing the robust walk). -/
theorem robust_path [DecidableEq V] {K : Finset V} {M D : ℕ} (hd : RobustDiam H K M D)
    (Y : Finset V) (hY : Y.card ≤ M) {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxY : x ∉ Y)
    (hyY : y ∉ Y) :
    ∃ p : H.Walk x y, p.IsPath ∧ p.length ≤ D ∧ ∀ z ∈ p.support, z ∈ K ∧ z ∉ Y := by
  obtain ⟨p, hl, hs⟩ := hd Y hY x hx y hy hxY hyY
  exact ⟨p.bypass, p.bypass_isPath, (p.length_bypass_le).trans hl,
    fun z hz => hs z (p.support_bypass_subset hz)⟩

/-! ### Priority 1: the odd path in a non-bipartite robust component -/

/-- Assembling the odd path from the two connectors and an arc of the cycle. -/
theorem assemble [DecidableEq V] {a b c0 c1 : V} (C : Finset V) (P : H.Walk a c0)
    (arc : H.Walk c0 c1) (Q : H.Walk b c1) (hP : P.IsPath) (harc : arc.IsPath) (hQ : Q.IsPath)
    (harcC : ∀ z ∈ arc.support, z ∈ C)
    (hPC : ∀ z ∈ P.support, z ∈ C → z = c0)
    (hQPC : ∀ z ∈ Q.support, (z ∈ P.support ∨ z ∈ C) → z = c1) :
    ((P.append arc).append Q.reverse).IsPath := by
  refine isPath_append_of _ _ (isPath_append_of _ _ hP harc ?_) hQ.reverse ?_
  · intro z hz hz'; exact hPC z hz (harcC z hz')
  · intro z hz hz'
    rw [Walk.support_reverse, List.mem_reverse] at hz'
    rw [Walk.support_append, List.mem_append] at hz
    refine hQPC z hz' ?_
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (harcC z (List.mem_of_mem_tail hz))

/-- **Bounded odd simple paths in a robust non-bipartite component.**  With
`B + 3D + 1 ≤ M` (implied by the S07 slack `B + 3D + 4 ≤ M`), for every `Z` with `|Z| ≤ B`, any
two distinct `a, b ∈ K \ Z` are joined by a simple path `a → b` of odd length `≤ 4D + 1` inside
`K \ Z`. -/
theorem odd_path_nonbip [DecidableEq V] {K : Finset V} {B M D : ℕ} (hM : B + 3 * D + 1 ≤ M)
    (hd : RobustDiam H K M D) (hn : RobustNonBip H K M) (Z : Finset V) (hZ : Z.card ≤ B)
    {a b : V} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) (haZ : a ∉ Z) (hbZ : b ∉ Z) :
    ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ 4 * D + 1 ∧
      ∀ z ∈ w.support, z ∈ K ∧ z ∉ Z := by
  -- `D ≥ 1`, since `a ≠ b` are joined by a walk of length `≤ D`.
  have hD : 1 ≤ D := by
    obtain ⟨p, hl, -⟩ := hd ∅ (by simp) a ha b hb (by simp) (by simp)
    by_contra h0
    exact hab (p.eq_of_length_eq_zero (by omega))
  -- Step 1: a short odd cycle avoiding `Z ∪ {a, b}`.
  obtain ⟨Y1, hY1⟩ : ∃ Y : Finset V, Y = insert a (insert b Z) := ⟨_, rfl⟩
  have hY1c : Y1.card ≤ B + 2 := by
    rw [hY1]
    have := card_insert_le a (insert b Z); have := card_insert_le b Z; omega
  obtain ⟨c0, c1, hadj, R, hR, hRe, hRl, hRs⟩ := short_odd_cycle (H := H)
    {x | x ∈ K ∧ x ∉ Y1} D
    (fun x hx y hy => hd Y1 (by omega) x hx.1 y hy.1 hx.2 hy.2)
    (fun ⟨col, hcol⟩ => hn Y1 (by omega)
      ⟨col, fun x hx y hy hxY hyY hxy => hcol x ⟨hx, hxY⟩ y ⟨hy, hyY⟩ hxy⟩)
  obtain ⟨C, hC⟩ : ∃ C : Finset V, C = R.support.toFinset := ⟨_, rfl⟩
  have hCc : C.card ≤ 2 * D + 1 := by
    have := List.toFinset_card_le R.support; rw [Walk.length_support] at this; rw [hC]; omega
  have hCK : ∀ z ∈ C, z ∈ K ∧ z ∉ Y1 := fun z hz => hRs z (List.mem_toFinset.mp (hC ▸ hz))
  have hc0C : c0 ∈ C := hC ▸ List.mem_toFinset.mpr R.end_mem_support
  have hc1C : c1 ∈ C := hC ▸ List.mem_toFinset.mpr R.start_mem_support
  have hc01 : c0 ≠ c1 := H.ne_of_adj hadj
  have hnotY1 : ∀ z ∈ C, z ≠ a ∧ z ≠ b ∧ z ∉ Z := by
    intro z hz
    have := (hCK z hz).2
    simp only [hY1, mem_insert, not_or] at this
    exact this
  have hCerase : ∀ c ∈ C, (C.erase c).card ≤ 2 * D := fun c hc => by
    have := card_erase_lt_of_mem hc; omega
  -- Step 2: connect `a` to `c0` avoiding `Z`, `b` and the cycle except `c0`.
  obtain ⟨Y2, hY2⟩ : ∃ Y : Finset V, Y = insert b Z ∪ C.erase c0 := ⟨_, rfl⟩
  have hY2c : Y2.card ≤ B + 2 * D + 1 := by
    rw [hY2]
    have := card_union_le (insert b Z) (C.erase c0); have := card_insert_le b Z
    have := hCerase c0 hc0C; omega
  have haY2 : a ∉ Y2 := by
    simp only [hY2, mem_union, mem_insert, mem_erase, not_or]
    exact ⟨⟨hab, haZ⟩, fun ⟨_, h⟩ => (hnotY1 a h).1 rfl⟩
  have hc0Y2 : c0 ∉ Y2 := by
    simp only [hY2, mem_union, mem_insert, mem_erase, not_or]
    exact ⟨⟨(hnotY1 c0 hc0C).2.1, (hnotY1 c0 hc0C).2.2⟩, fun ⟨h, _⟩ => h rfl⟩
  obtain ⟨P, hP, hPl, hPs⟩ := robust_path hd Y2 (by omega) ha (hCK c0 hc0C).1 haY2 hc0Y2
  -- Step 3: connect `b` to `c1` avoiding `Z`, `V(P)` and the cycle except `c1`.
  obtain ⟨Y3, hY3⟩ : ∃ Y : Finset V, Y = Z ∪ P.support.toFinset ∪ C.erase c1 := ⟨_, rfl⟩
  have hY3c : Y3.card ≤ B + 3 * D + 1 := by
    rw [hY3]
    have h1 := card_union_le (Z ∪ P.support.toFinset) (C.erase c1)
    have h2 := card_union_le Z P.support.toFinset
    have h3 := List.toFinset_card_le P.support
    rw [Walk.length_support] at h3
    have := hCerase c1 hc1C; omega
  have hbY3 : b ∉ Y3 := by
    simp only [hY3, mem_union, List.mem_toFinset, mem_erase, not_or]
    refine ⟨⟨hbZ, fun h => (hPs b h).2 ?_⟩, fun ⟨_, h⟩ => (hnotY1 b h).2.1 rfl⟩
    simp [hY2]
  have hc1Y3 : c1 ∉ Y3 := by
    simp only [hY3, mem_union, List.mem_toFinset, mem_erase, not_or]
    refine ⟨⟨(hnotY1 c1 hc1C).2.2, fun h => (hPs c1 h).2 ?_⟩, fun ⟨h, _⟩ => h rfl⟩
    simp only [hY2, mem_union, mem_erase]
    exact Or.inr ⟨hc01.symm, hc1C⟩
  obtain ⟨Q, hQ, hQl, hQs⟩ := robust_path hd Y3 (by omega) hb (hCK c1 hc1C).1 hbY3 hc1Y3
  -- Step 4: disjointness facts and the choice of arc.
  have hPC : ∀ z ∈ P.support, z ∈ C → z = c0 := by
    intro z hz hzC
    by_contra hne
    exact (hPs z hz).2 (hY2 ▸ mem_union_right _ (mem_erase.mpr ⟨hne, hzC⟩))
  have hQPC : ∀ z ∈ Q.support, (z ∈ P.support ∨ z ∈ C) → z = c1 := by
    intro z hz hz'
    by_contra hne
    apply (hQs z hz).2
    rw [hY3]
    rcases hz' with h | h
    · exact mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr h))
    · exact mem_union_right _ (mem_erase.mpr ⟨hne, h⟩)
  have hgood : ∀ (arc : H.Walk c0 c1), arc.IsPath → (∀ z ∈ arc.support, z ∈ C) →
      Odd (P.length + arc.length + Q.length) → arc.length ≤ 2 * D →
      ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ 4 * D + 1 ∧
        ∀ z ∈ w.support, z ∈ K ∧ z ∉ Z := by
    intro arc harc harcC hodd hal
    refine ⟨(P.append arc).append Q.reverse, assemble C P arc Q hP harc hQ harcC hPC hQPC,
      ?_, ?_, ?_⟩
    · simpa [Walk.length_append, Walk.length_reverse] using hodd
    · simp only [Walk.length_append, Walk.length_reverse]; omega
    · intro z hz
      simp only [Walk.support_append, Walk.support_reverse, List.mem_append] at hz
      rcases hz with (hz | hz) | hz
      · exact ⟨(hPs z hz).1, fun h => (hPs z hz).2 (hY2 ▸ mem_union_left _ (mem_insert_of_mem h))⟩
      · have := harcC z (List.mem_of_mem_tail hz)
        exact ⟨(hCK z this).1, (hnotY1 z this).2.2⟩
      · have hz' := List.mem_reverse.mp (List.mem_of_mem_tail hz)
        exact ⟨(hQs z hz').1, fun h => (hQs z hz').2 (hY3 ▸ mem_union_left _ (mem_union_left _ h))⟩
  rcases Nat.even_or_odd (P.length + Q.length) with he | ho
  · -- use the single edge `c0 c1` (length 1)
    refine hgood (Walk.cons hadj Walk.nil) ?_ ?_ ?_ ?_
    · rw [Walk.cons_isPath_iff]; simp [hc01]
    · intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
    · simp only [Walk.length_cons, Walk.length_nil]
      rcases he with ⟨k, hk⟩; exact ⟨k, by omega⟩
    · simp only [Walk.length_cons, Walk.length_nil]
      omega
  · -- use the other arc of the cycle (even length)
    refine hgood R.reverse hR.reverse ?_ ?_ ?_
    · intro z hz; rw [Walk.support_reverse, List.mem_reverse] at hz
      exact hC ▸ List.mem_toFinset.mpr hz
    · rw [Walk.length_reverse]
      rcases ho with ⟨k, hk⟩; rcases hRe with ⟨m, hm⟩; exact ⟨k + m, by omega⟩
    · rw [Walk.length_reverse]; exact hRl

/-- Parity of walks inside a bipartite vertex set `K` with side `X`. -/
theorem walk_parity_in (K : Finset V) (X : Set V)
    (hbip : ∀ x ∈ K, ∀ y ∈ K, H.Adj x y → (x ∈ X ↔ y ∉ X)) :
    ∀ {a b : V} (p : H.Walk a b), (∀ z ∈ p.support, z ∈ K) →
      ((a ∈ X ↔ b ∈ X) ↔ Even p.length)
  | _, _, .nil, _ => by simp
  | _, _, .cons h p, hs => by
    rw [Walk.length_cons, Nat.even_add_one,
      ← walk_parity_in K X hbip p (fun z hz => hs z (by simp [hz]))]
    have := hbip _ (hs _ (by simp)) _ (hs _ (by simp [p.start_mem_support])) h
    tauto

/-- **Bipartite case.**  Survivors on opposite sides of a robust bipartite component are joined
by a simple odd path of length `≤ D` inside `K \ Z`. -/
theorem odd_path_bip [DecidableEq V] {K : Finset V} {B M D : ℕ} (hM : B ≤ M)
    (hd : RobustDiam H K M D) (X : Set V)
    (hbip : ∀ x ∈ K, ∀ y ∈ K, H.Adj x y → (x ∈ X ↔ y ∉ X)) (Z : Finset V) (hZ : Z.card ≤ B)
    {a b : V} (ha : a ∈ K) (hb : b ∈ K) (hs : ¬ (a ∈ X ↔ b ∈ X)) (haZ : a ∉ Z) (hbZ : b ∉ Z) :
    ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ D ∧
      ∀ z ∈ w.support, z ∈ K ∧ z ∉ Z := by
  obtain ⟨p, hp, hl, hps⟩ := robust_path hd Z (hZ.trans hM) ha hb haZ hbZ
  refine ⟨p, hp, ?_, hl, hps⟩
  rw [← Nat.not_even_iff_odd, ← walk_parity_in K X hbip p (fun z hz => (hps z hz).1)]
  exact hs

/-- **`RobustOddPaths` as a conclusion (PAR, non-bipartite component).** -/
theorem robustOddPaths_nonbip [DecidableEq V] {K : Finset V} {B M D : ℕ}
    (hM : B + 3 * D + 1 ≤ M) (hd : RobustDiam H K M D) (hn : RobustNonBip H K M) :
    RobustOddPaths H (ParAllowed K) (4 * D + 1) B := by
  intro Z hZ a b ⟨ha, hb, hab⟩ haZ hbZ
  obtain ⟨w, hw, ho, hl, hs⟩ := odd_path_nonbip hM hd hn Z hZ ha hb hab haZ hbZ
  exact ⟨w, hw, ho, hl, fun z hz => (hs z hz).2⟩

/-- **`RobustOddPaths` as a conclusion (BAL, bipartite component with sides `X ⊔ Y ⊆ K`).**
Odd paths are produced only between opposite sides. -/
theorem robustOddPaths_bip [DecidableEq V] {K X Y : Finset V} {B M D : ℕ} (hM : B ≤ M)
    (hd : RobustDiam H K M D) (hXK : X ⊆ K) (hYK : Y ⊆ K) (hXY : Disjoint X Y)
    (hbip : ∀ x ∈ K, ∀ y ∈ K, H.Adj x y → (x ∈ X ↔ y ∉ X)) :
    RobustOddPaths H (BalAllowed X Y) (4 * D + 1) B := by
  intro Z hZ a b hall haZ hbZ
  have key : ∀ a b, a ∈ X → b ∈ Y → a ∉ Z → b ∉ Z →
      ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ 4 * D + 1 ∧
        ∀ z ∈ w.support, z ∉ Z := by
    intro a b ha hb haZ hbZ
    have hbX : b ∉ X := fun h => disjoint_left.mp hXY h hb
    obtain ⟨w, hw, ho, hl, hs⟩ := odd_path_bip (B := B) hM hd (X : Set V) (by simpa using hbip)
      Z hZ (hXK ha) (hYK hb) (by simp [ha, hbX]) haZ hbZ
    exact ⟨w, hw, ho, by omega, fun z hz => (hs z hz).2⟩
  rcases hall with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact key a b ha hb haZ hbZ
  · obtain ⟨w, hw, ho, hl, hs⟩ := key b a hb ha hbZ haZ
    exact ⟨w.reverse, hw.reverse, by simpa using ho, by simpa using hl,
      fun z hz => hs z (by simpa using hz)⟩

end SelRoute
