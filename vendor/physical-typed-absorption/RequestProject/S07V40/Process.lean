/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V40.Basic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# Global finite macro-round bank, part 1: the placement process (V40)

* `pick S B Z l` chooses a good cell when one exists (the supply guarantees it does along the
  process).
* `placeRound S Z r B ls` places ONE cell for every label of `ls`, sequentially, each disjoint from
  all previously used edges; `Z` is held fixed during the round.
* `actSet S Z` = labels `(sign, c, color)` with `g c ∈ K Z`; `actList` is its list.
* `run S t` is the bank after `t` macro rounds: stop if `K (Z_t) = ⊥`, otherwise run one full
  round at `Z_t = satSet q (edges of run S t)`; saturation is updated only between rounds.

Main supply-dependent result: `run_inv` (degree, edge count, cell properties, pairwise disjoint
totals) for every `t ≤ N`, under the cap premise `2 * E * Bstar * N ≤ q * zmax`.
-/

@[expose] public section

namespace S07V40

open Finset Classical

noncomputable section

variable {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- Choice of a good cell (default: the empty cell if none exists). -/
def pick (S : MacroSetting V Q C) (B : Finset (Sym2 V)) (Z : Finset V) (l : Lab C S.P) :
    Cell V :=
  if h : ∃ c, GoodCell S B Z l c then h.choose else ⟨∅, ∅⟩

omit [Fintype V] [Fintype C] in
lemma pick_good {S : MacroSetting V Q C} {B : Finset (Sym2 V)} {Z : Finset V} {l : Lab C S.P}
    (h : ∃ c, GoodCell S B Z l c) : GoodCell S B Z l (pick S B Z l) := by
  unfold pick; rw [dif_pos h]; exact h.choose_spec

/-- A placed cell: round index, label (sign, catalog entry, color) and the actual cell. -/
structure Placed (V C : Type*) (P : ℕ) where
  /-- chronological round index -/
  round : ℕ
  /-- label -/
  lab : Lab C P
  /-- the edge data -/
  cell : Cell V

/-- Union of the total edge sets of a list of placed cells. -/
def edgesOf {P : ℕ} : List (Placed V C P) → Finset (Sym2 V)
  | [] => ∅
  | p :: L => p.cell.tot ∪ edgesOf L

section edges
variable {P : ℕ}

omit [Fintype V] [Fintype C] in
@[simp] lemma edgesOf_nil : edgesOf ([] : List (Placed V C P)) = ∅ := rfl

omit [Fintype V] [Fintype C] in
@[simp] lemma edgesOf_cons (p : Placed V C P) (L : List (Placed V C P)) :
    edgesOf (p :: L) = p.cell.tot ∪ edgesOf L := rfl

omit [Fintype V] [Fintype C] in
lemma edgesOf_append (L L' : List (Placed V C P)) :
    edgesOf (L ++ L') = edgesOf L ∪ edgesOf L' := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih, union_assoc]

omit [Fintype V] [Fintype C] in
lemma mem_edgesOf {L : List (Placed V C P)} {e : Sym2 V} :
    e ∈ edgesOf L ↔ ∃ p ∈ L, e ∈ p.cell.tot := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

omit [Fintype V] [Fintype C] in
lemma tot_subset_edgesOf {L : List (Placed V C P)} {p : Placed V C P} (h : p ∈ L) :
    p.cell.tot ⊆ edgesOf L := fun _ he => mem_edgesOf.2 ⟨p, h, he⟩

omit [Fintype V] [Fintype C] in
lemma disjoint_edgesOf {X : Finset (Sym2 V)} {L : List (Placed V C P)}
    (h : ∀ p ∈ L, Disjoint X p.cell.tot) : Disjoint X (edgesOf L) := by
  rw [Finset.disjoint_left]
  intro e heX heL
  obtain ⟨p, hp, he⟩ := mem_edgesOf.1 heL
  exact Finset.disjoint_left.1 (h p hp) heX he

omit [Fintype V] [Fintype C] in
/-- With pairwise disjoint totals the edge count is exactly the sum of the cell sizes. -/
lemma card_edgesOf_eq {L : List (Placed V C P)}
    (hpw : L.Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot)) :
    (edgesOf L).card = (L.map (fun p => p.cell.tot.card)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.pairwise_cons] at hpw
    simp only [edgesOf_cons, List.map_cons, List.sum_cons]
    rw [card_union_of_disjoint (disjoint_edgesOf hpw.1), ih hpw.2]

end edges

/-- One full macro round at fixed `Z`: one cell per label of `ls`, placed sequentially. -/
def placeRound (S : MacroSetting V Q C) (Z : Finset V) (r : ℕ) :
    Finset (Sym2 V) → List (Lab C S.P) → List (Placed V C S.P)
  | _, [] => []
  | B, l :: ls => ⟨r, l, pick S B Z l⟩ :: placeRound S Z r (B ∪ (pick S B Z l).tot) ls

/-- Active labels at `Z`. -/
def actSet (S : MacroSetting V Q C) (Z : Finset V) : Finset (Lab C S.P) :=
  univ.filter (fun l => S.g l.2.1 ∈ S.K Z)

/-- Active labels at `Z`, as a duplicate-free list. -/
def actList (S : MacroSetting V Q C) (Z : Finset V) : List (Lab C S.P) := (actSet S Z).toList

/-- Saturated set of a bank. -/
def Zof (S : MacroSetting V Q C) (L : List (Placed V C S.P)) : Finset V :=
  satSet S.q (edgesOf L)

/-- **The macro-round process.** `run S t` is the bank after `t` rounds. -/
def run (S : MacroSetting V Q C) : ℕ → List (Placed V C S.P)
  | 0 => []
  | t + 1 =>
    if S.K (Zof S (run S t)) = ⊥ then run S t
    else run S t ++ placeRound S (Zof S (run S t)) t (edgesOf (run S t))
      (actList S (Zof S (run S t)))

/-- Saturated set at the start of round `t`. -/
def Zr (S : MacroSetting V Q C) (t : ℕ) : Finset V := Zof S (run S t)

/-- Used edges after `t` rounds. -/
def Br (S : MacroSetting V Q C) (t : ℕ) : Finset (Sym2 V) := edgesOf (run S t)

/-- Round `t` is executed (not stopped). -/
def Active (S : MacroSetting V Q C) (t : ℕ) : Prop := S.K (Zr S t) ≠ ⊥

variable {S : MacroSetting V Q C}

omit [Fintype V] in
lemma card_actList_le (Z : Finset V) : (actList S Z).length ≤ S.Bstar := by
  unfold actList
  rw [Finset.length_toList]
  calc (actSet S Z).card ≤ (univ : Finset (Lab C S.P)).card := card_le_card (subset_univ _)
    _ = S.Bstar := by rw [card_univ, card_lab]; rfl

omit [Fintype V] in
lemma mem_actList {Z : Finset V} {l : Lab C S.P} : l ∈ actList S Z ↔ S.g l.2.1 ∈ S.K Z := by
  simp [actList, actSet]

lemma run_succ_of_not_active {t : ℕ} (h : ¬ Active S t) : run S (t + 1) = run S t := by
  unfold Active Zr at h
  rw [run, if_pos (not_not.1 h)]

lemma run_succ_of_active {t : ℕ} (h : Active S t) : run S (t + 1) =
    run S t ++ placeRound S (Zr S t) t (Br S t) (actList S (Zr S t)) := by
  unfold Active Zr at h
  rw [run, if_neg h]; rfl

lemma run_prefix (t : ℕ) : run S t <+: run S (t + 1) := by
  by_cases h : Active S t
  · rw [run_succ_of_active h]; exact List.prefix_append _ _
  · rw [run_succ_of_not_active h]

lemma Br_mono : Monotone (Br S) := by
  refine monotone_nat_of_le_succ (fun t => ?_)
  obtain ⟨L, hL⟩ := run_prefix (S := S) t
  unfold Br; rw [← hL, edgesOf_append]; exact subset_union_left

lemma Zr_mono : Monotone (Zr S) := fun _ _ h => satSet_mono _ (Br_mono h)

lemma not_active_succ {t : ℕ} (h : ¬ Active S t) : ¬ Active S (t + 1) := by
  have : Zr S (t + 1) = Zr S t := by unfold Zr; rw [run_succ_of_not_active h]
  unfold Active at *; rw [this]; exact h

lemma active_of_le {s t : ℕ} (hst : s ≤ t) (ht : Active S t) : Active S s := by
  by_contra hs
  induction t, hst using Nat.le_induction with
  | base => exact hs ht
  | succ t _ ih => exact ih (not_not.1 (fun h => (not_active_succ h) ht))

/-! ### Supply-free bookkeeping of rounds and labels -/

omit [Fintype V] [Fintype C] in
lemma placeRound_round {Z : Finset V} {r : ℕ} :
    ∀ (ls : List (Lab C S.P)) (B : Finset (Sym2 V)), ∀ p ∈ placeRound S Z r B ls, p.round = r
  | [], _ => by simp [placeRound]
  | l :: ls, B => by
    intro p hp
    simp only [placeRound, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact placeRound_round ls _ p hp

omit [Fintype V] [Fintype C] in
lemma placeRound_lab {Z : Finset V} {r : ℕ} :
    ∀ (ls : List (Lab C S.P)) (B : Finset (Sym2 V)),
      (placeRound S Z r B ls).map (fun p => p.lab) = ls
  | [], _ => by simp [placeRound]
  | l :: ls, B => by simp [placeRound, placeRound_lab ls]

omit [Fintype V] [Fintype C] in
lemma countP_placeRound {Z : Finset V} {r r' : ℕ} {l : Lab C S.P} :
    ∀ (ls : List (Lab C S.P)) (B : Finset (Sym2 V)),
      (placeRound S Z r B ls).countP (fun p => decide (p.round = r' ∧ p.lab = l)) =
        if r = r' then ls.count l else 0
  | [], _ => by simp [placeRound]
  | l' :: ls, B => by
    simp only [placeRound, List.countP_cons, countP_placeRound ls, List.count_cons]
    by_cases h : r = r' <;> by_cases h' : l' = l <;> simp [h, h']

lemma run_round_lt : ∀ (t : ℕ), ∀ p ∈ run S t, p.round < t
  | 0 => by simp [run]
  | t + 1 => by
    intro p hp
    by_cases h : Active S t
    · rw [run_succ_of_active h, List.mem_append] at hp
      rcases hp with hp | hp
      · exact Nat.lt_succ_of_lt (run_round_lt t p hp)
      · rw [placeRound_round _ _ p hp]; exact Nat.lt_succ_self t
    · rw [run_succ_of_not_active h] at hp
      exact Nat.lt_succ_of_lt (run_round_lt t p hp)

/-- **Exactly one cell per executed round and active label.** -/
theorem countP_run (r : ℕ) (l : Lab C S.P) : ∀ t : ℕ,
    (run S t).countP (fun p => decide (p.round = r ∧ p.lab = l)) =
      if r < t ∧ Active S r ∧ S.g l.2.1 ∈ S.K (Zr S r) then 1 else 0
  | 0 => by simp [run]
  | t + 1 => by
    by_cases h : Active S t
    · have hc : (actList S (Zr S t)).count l =
          if S.g l.2.1 ∈ S.K (Zr S t) then 1 else 0 := by
        have hnd : (actList S (Zr S t)).Nodup := Finset.nodup_toList _
        split_ifs with hg
        · exact List.count_eq_one_of_mem hnd (mem_actList.2 hg)
        · exact List.count_eq_zero_of_not_mem (fun hm => hg (mem_actList.1 hm))
      rw [run_succ_of_active h, List.countP_append, countP_run r l t, countP_placeRound, hc]
      by_cases hrt : r = t
      · subst hrt; simp [h]
      · have : r < t + 1 ↔ r < t := by omega
        simp [Ne.symm hrt, this]
    · rw [run_succ_of_not_active h, countP_run r l t]
      by_cases hrt : r = t
      · subst hrt; simp [h]
      · have : r < t + 1 ↔ r < t := by omega
        simp [this]

/-! ### The round lemma (uses the supply) -/

omit [Fintype V] in
/-- **Round lemma.** Placing the labels `ls` one at a time from used set `B`, with `Z` fixed. -/
theorem placeRound_spec (hS : CellSupply S) {Z : Finset V} (hZ : Z.card ≤ S.zmax) (r : ℕ) :
    ∀ (ls : List (Lab C S.P)) (B : Finset (Sym2 V)),
      (∀ l ∈ ls, S.g l.2.1 ∈ S.K Z) →
      (∀ v, v ∉ Z → deg B v + ls.length * S.E < S.q + S.Bstar * S.E) →
      (∀ v ∈ Z, deg B v < S.q + S.Bstar * S.E) →
      (∀ p ∈ placeRound S Z r B ls, p.round = r ∧ GoodCell S B Z p.lab p.cell) ∧
      (placeRound S Z r B ls).Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot) ∧
      (∀ v, v ∉ Z → deg (B ∪ edgesOf (placeRound S Z r B ls)) v ≤ deg B v + ls.length * S.E) ∧
      (∀ v ∈ Z, deg (B ∪ edgesOf (placeRound S Z r B ls)) v = deg B v) ∧
      (edgesOf (placeRound S Z r B ls)).card ≤ ls.length * S.E
  | [], B => by intros; simp [placeRound]
  | l :: ls, B => by
    intro hact hout hin
    have hmax : ∀ v, deg B v ≤ S.q + S.Bstar * S.E := by
      intro v
      by_cases hv : v ∈ Z
      · exact (hin v hv).le
      · have := hout v hv
        rw [List.length_cons, add_mul, one_mul] at this
        omega
    have hc := pick_good (hS B Z hmax hZ l (hact l (List.mem_cons_self ..)))
    set c := pick S B Z l with hcdef
    obtain ⟨hAY, hbA, hbT, hdisj, havoid, hcard, hch⟩ := hc
    set B' := B ∪ c.tot with hB'
    have hdeg' : ∀ v, deg B' v ≤ deg B v + S.E :=
      fun v => (deg_union_le B c.tot v).trans (Nat.add_le_add_left hcard _)
    have hZ' : ∀ v ∈ Z, deg B' v = deg B v := fun v hv => deg_union_of_avoids havoid hv
    obtain ⟨h1, h2, h4, h5, h6⟩ := placeRound_spec hS hZ r ls B'
      (fun l hl => hact l (List.mem_cons_of_mem _ hl))
      (fun v hv => by
        have := hout v hv
        have := hdeg' v
        rw [List.length_cons, add_mul, one_mul] at *
        omega)
      (fun v hv => by rw [hZ' v hv]; exact hin v hv)
    have hcons : placeRound S Z r B (l :: ls) = ⟨r, l, c⟩ :: placeRound S Z r B' ls := rfl
    rw [hcons]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨rfl, hAY, hbA, hbT, hdisj, havoid, hcard, hch⟩
      · exact ⟨(h1 p hp).1, (h1 p hp).2.mono subset_union_left⟩
    · refine List.Pairwise.cons (fun p hp => ?_) h2
      exact ((h1 p hp).2.2.2.2.1.mono_right subset_union_right).symm
    · intro v hv
      have e : B ∪ edgesOf (⟨r, l, c⟩ :: placeRound S Z r B' ls) =
          B' ∪ edgesOf (placeRound S Z r B' ls) := by
        simp [hB', Cell.tot, union_assoc]
      rw [e, List.length_cons, add_mul, one_mul]
      have := h4 v hv
      have := hdeg' v
      omega
    · intro v hv
      have e : B ∪ edgesOf (⟨r, l, c⟩ :: placeRound S Z r B' ls) =
          B' ∪ edgesOf (placeRound S Z r B' ls) := by
        simp [hB', Cell.tot, union_assoc]
      rw [e, h5 v hv, hZ' v hv]
    · rw [edgesOf_cons, List.length_cons, add_mul, one_mul]
      show (c.tot ∪ _).card ≤ _
      exact (card_union_le _ _).trans (by omega)

/-! ### The global invariant -/

/-- Properties of a placed cell, intrinsic to the cell. -/
def PlacedOK (S : MacroSetting V Q C) (p : Placed V C S.P) : Prop :=
  Disjoint p.cell.A p.cell.Y ∧ S.basal p.cell.A ∧ S.basal p.cell.tot ∧
    p.cell.tot.card ≤ S.E ∧ charge S.w p.cell.Y = sgnQ p.lab.1 (S.g p.lab.2.1)

/-- The invariant after `t` rounds. -/
def RunInv (S : MacroSetting V Q C) (t : ℕ) : Prop :=
  (∀ v, deg (Br S t) v < S.q + S.Bstar * S.E) ∧
  (Br S t).card ≤ S.E * S.Bstar * t ∧
  (∀ p ∈ run S t, PlacedOK S p ∧ p.round < t ∧ Active S p.round ∧
      S.g p.lab.2.1 ∈ S.K (Zr S p.round) ∧ Avoids (Zr S p.round) p.cell.tot) ∧
  (run S t).Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot)

/-- Smallness from the global count and the cap: `q * |Z_t| ≤ 2 * E * Bstar * t` and, for
`t ≤ N`, `|Z_t| ≤ zmax`. -/
lemma card_Zr_of_inv {t N : ℕ} (hq : 0 < S.q) (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax)
    (htN : t ≤ N) (hcard : (Br S t).card ≤ S.E * S.Bstar * t) :
    S.q * (Zr S t).card ≤ 2 * S.E * S.Bstar * t ∧ (Zr S t).card ≤ S.zmax := by
  have h1 : S.q * (Zr S t).card ≤ 2 * S.E * S.Bstar * t := by
    calc S.q * (Zr S t).card ≤ 2 * (Br S t).card := mul_card_satSet_le _ _
      _ ≤ 2 * (S.E * S.Bstar * t) := Nat.mul_le_mul_left _ hcard
      _ = 2 * S.E * S.Bstar * t := by ring
  refine ⟨h1, ?_⟩
  have : S.q * (Zr S t).card ≤ S.q * S.zmax :=
    h1.trans ((Nat.mul_le_mul_left _ htN).trans hcap)
  exact Nat.le_of_mul_le_mul_left this hq

/-- **Global invariant** of the process for every `t ≤ N`, from the finite supply. -/
theorem run_inv (hq : 0 < S.q) (hS : CellSupply S) {N : ℕ}
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) : ∀ t ≤ N, RunInv S t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun v => ?_, by simp [Br, run], by simp [run], by simp [run]⟩
    simp only [Br, run, edgesOf_nil, deg, filter_empty, card_empty]
    exact Nat.add_pos_left hq _
  | succ t ih =>
    intro htN
    obtain ⟨hdeg, hcard, hcells, hpw⟩ := ih (by omega)
    by_cases hact : Active S t
    · have hZ := (card_Zr_of_inv hq hcap (by omega) hcard).2
      have hlen := card_actList_le (S := S) (Zr S t)
      have hlenE : (actList S (Zr S t)).length * S.E ≤ S.Bstar * S.E :=
        Nat.mul_le_mul_right _ hlen
      obtain ⟨h1, h2, h4, h5, h6⟩ := placeRound_spec hS hZ t (actList S (Zr S t)) (Br S t)
        (fun l hl => mem_actList.1 hl)
        (fun v hv => by
          have : deg (Br S t) v < S.q := by
            have : ¬ S.q ≤ deg (Br S t) v := fun h => hv (mem_satSet.2 h)
            omega
          omega)
        (fun v _ => hdeg v)
      have hBr : Br S (t + 1) = Br S t ∪
          edgesOf (placeRound S (Zr S t) t (Br S t) (actList S (Zr S t))) := by
        unfold Br; rw [run_succ_of_active hact, edgesOf_append]; rfl
      refine ⟨fun v => ?_, ?_, ?_, ?_⟩
      · rw [hBr]
        by_cases hv : v ∈ Zr S t
        · rw [h5 v hv]; exact hdeg v
        · have := h4 v hv
          have : deg (Br S t) v < S.q := by
            have : ¬ S.q ≤ deg (Br S t) v := fun h => hv (mem_satSet.2 h)
            omega
          omega
      · rw [hBr]
        refine (card_union_le _ _).trans ?_
        have : S.E * S.Bstar * (t + 1) = S.E * S.Bstar * t + S.Bstar * S.E := by ring
        omega
      · intro p hp
        rw [run_succ_of_active hact, List.mem_append] at hp
        rcases hp with hp | hp
        · obtain ⟨a, b, c, d, e⟩ := hcells p hp
          exact ⟨a, by omega, c, d, e⟩
        · obtain ⟨hr, hAY, hbA, hbT, _, havoid, hcd, hch⟩ := h1 p hp
          have hlab : p.lab ∈ actList S (Zr S t) := by
            have := placeRound_lab (S := S) (Z := Zr S t) (r := t) (actList S (Zr S t)) (Br S t)
            rw [← this]
            exact List.mem_map_of_mem hp
          rw [hr]
          exact ⟨⟨hAY, hbA, hbT, hcd, hch⟩, Nat.lt_succ_self t, hact, mem_actList.1 hlab,
            havoid⟩
      · rw [run_succ_of_active hact, List.pairwise_append]
        refine ⟨hpw, h2, fun a ha b hb => ?_⟩
        exact ((h1 b hb).2.2.2.2.1.mono_right (tot_subset_edgesOf ha)).symm
    · have hrun := run_succ_of_not_active hact
      have hBr : Br S (t + 1) = Br S t := by unfold Br; rw [hrun]
      refine ⟨fun v => by rw [hBr]; exact hdeg v, ?_, ?_, by rw [hrun]; exact hpw⟩
      · rw [hBr]; refine hcard.trans (Nat.mul_le_mul_left _ (Nat.le_succ t))
      · intro p hp
        rw [hrun] at hp
        obtain ⟨a, b, c, d, e⟩ := hcells p hp
        exact ⟨a, by omega, c, d, e⟩

end

end S07V40
