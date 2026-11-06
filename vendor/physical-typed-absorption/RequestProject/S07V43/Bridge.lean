/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V43.Activation
public import RequestProject.S07V40.MacroBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V43 §3 — exact bridge from a stratum of the V40 bank (a LIST) to finite occurrence indices

For a V40 setting `S` and horizon `N`, the actual constructed bank is the list `run S N`.

* `StratOcc S N j = {k : Fin (run S N).length // sidx S ((run S N).get k).round = j}` : the
  occurrences of stratum `j` are POSITIONS in the list (two positions with equal, even empty,
  cells are different occurrences — no injectivity of edge sets is used).
* `stratBank S N j : Bank V (StratOcc S N j) C S.P` reads the tag and the cell at each position.
* `card_filter_get` : counting positions is `List.countP`.
* `stratBank_fiber_card` : `|fiber (s, c, p)| = if g c ∈ Kstrat j then m_j else 0`, from V40
  `countP_stratum` (unconditional).
* `stratBank_valid` (from `MacroBank`) : the stratum bank is a valid `Bank` (pairwise-disjoint
  totals from the list `Pairwise`, cell properties from `PlacedOK`).
* `stratBank_avoids` : the stratum bank avoids the initial saturated set `Zstrat j`;
  `stratBank_total_subset` / `stratBank_deg_lt` : it lies in the used edges of degree
  `< q + Bstar * E`.
* `stratBank_supplies` : a word supported on entries active for `Kstrat j`, with colour cost
  `≤ m_j`, is supplied.
-/

@[expose] public section

namespace S07V43

open Finset Classical S07V40

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- counting positions of a list is `countP` -/
lemma card_filter_get {α : Type*} (L : List α) (f : α → Bool) :
    (univ.filter (fun k : Fin L.length => f (L.get k) = true)).card = L.countP f := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [card_filter, List.countP_cons, ← ih, card_filter]
    change (∑ i : Fin (L.length + 1), _) = _
    rw [Fin.sum_univ_succ]
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero,
      Fin.val_succ, List.getElem_cons_succ]
    split_ifs <;> simp_all [add_comm]

/-- counting a filter over a subtype -/
lemma card_filter_subtype {α : Type*} [Fintype α] (r q : α → Prop) :
    (univ.filter (fun x : {a // r a} => q x.1)).card = (univ.filter (fun a => r a ∧ q a)).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨a, h1⟩, h2, rfl⟩

variable {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- occurrences of stratum `j`: positions in the list `run S N` -/
abbrev StratOcc (S : MacroSetting V Q C) (N j : ℕ) :=
  {k : Fin (run S N).length // sidx S ((run S N).get k).round = j}

/-- the bank of stratum `j` of the actual V40 bank -/
def stratBank (S : MacroSetting V Q C) (N j : ℕ) : Bank V (StratOcc S N j) C S.P where
  sgn k := ((run S N).get k.1).lab.1
  cat k := ((run S N).get k.1).lab.2.1
  col k := ((run S N).get k.1).lab.2.2
  A k := ((run S N).get k.1).cell.A
  Y k := ((run S N).get k.1).cell.Y

variable {S : MacroSetting V Q C} {N j : ℕ}

lemma stratBank_tot (k : StratOcc S N j) :
    (stratBank S N j).tot k = ((run S N).get k.1).cell.tot := rfl

lemma get_mem_run (k : StratOcc S N j) : (run S N).get k.1 ∈ run S N := List.get_mem _ _

/-- **fibre count of the stratum bank** (from V40 `countP_stratum`; no hypothesis) -/
theorem stratBank_fiber_card (s : Bool) (c : C) (p : Fin S.P) :
    ((stratBank S N j).fiber s c p).card =
      if S.g c ∈ Kstrat S N j then mStrat S N j else 0 := by
  rw [← countP_stratum N j (s, c, p), ← card_filter_get]
  unfold Bank.fiber
  refine Finset.card_bij (fun k _ => k.1) ?_ ?_ ?_
  · intro k hk
    have hp := (mem_filter.mp hk).2
    change ((run S N).get k.1).lab.1 = s ∧
      ((run S N).get k.1).lab.2.1 = c ∧ ((run S N).get k.1).lab.2.2 = p at hp
    exact mem_filter.mpr ⟨mem_univ _,by
      simp only [decide_eq_true_eq]
      exact ⟨k.2,Prod.ext hp.1 (Prod.ext hp.2.1 hp.2.2)⟩⟩
  · intro k _ k' _ hkk
    exact Subtype.ext hkk
  · intro k hk
    have hh := (mem_filter.mp hk).2
    simp only [decide_eq_true_eq] at hh
    refine ⟨⟨k,hh.1⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    change ((run S N).get k).lab.1 = s ∧
      ((run S N).get k).lab.2.1 = c ∧ ((run S N).get k).lab.2.2 = p
    rw [hh.2]
    exact ⟨rfl,rfl,rfl⟩

/-- **the stratum bank is valid** (from the V40 invariants) -/
theorem stratBank_valid {L : ℕ} (hM : MacroBank S L N) :
    (stratBank S N j).Valid S.basal S.w S.g := by
  have hok : ∀ k : StratOcc S N j, PlacedOK S ((run S N).get k.1) :=
    fun k => (hM.cells _ (get_mem_run k)).1
  refine ⟨fun k => (hok k).1, ?_, fun k => (hok k).2.1, fun k => (hok k).2.2.1,
    fun k => (hok k).2.2.2.2⟩
  intro k k' hkk
  have hne : k.1 ≠ k'.1 := fun h => hkk (Subtype.ext h)
  have hpw := List.pairwise_iff_get.1 hM.disjoint
  rcases lt_or_gt_of_ne hne with h | h
  · exact hpw _ _ h
  · exact (hpw _ _ h).symm

/-- the stratum bank lies inside the used edges of the whole bank -/
theorem stratBank_total_subset : (stratBank S N j).total ⊆ Br S N :=
  biUnion_subset.2 fun k _ => tot_subset_edgesOf (get_mem_run k)

/-- local degrees of the stratum bank are below `q + Bstar * E` -/
theorem stratBank_deg_lt {L : ℕ} (hM : MacroBank S L N) (v : V) :
    deg (stratBank S N j).total v < S.q + S.Bstar * S.E :=
  lt_of_le_of_lt (deg_mono stratBank_total_subset v) (hM.maxdeg v)

/-- **the stratum bank avoids the initial saturated set of the stratum** -/
theorem stratBank_avoids {L : ℕ} (hM : MacroBank S L N) :
    Avoids (Zstrat S N j) (stratBank S N j).total := by
  intro e he v hv
  simp only [Bank.total, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨k, hk⟩ := he
  obtain ⟨-, hlt, -, hav⟩ := hM.cells _ (get_mem_run k)
  have hpre : preStrat S N j ≤ ((run S N).get k.1).round :=
    ((hM.interval _ hlt j).1 k.2).1
  exact hav e hk v (Zr_mono hpre hv)

/-- **supply of a word by the stratum bank**: support on active entries, colour cost `≤ m_j` -/
theorem stratBank_supplies {z : Fin S.P → C → ℤ}
    (hact : ∀ p c, z p c ≠ 0 → S.g c ∈ Kstrat S N j)
    (hz : ∀ p, ∑ c, (z p c).natAbs ≤ mStrat S N j) : (stratBank S N j).Supplies z := by
  intro p c
  by_cases h0 : z p c = 0
  · rw [h0]; simp
  · rw [stratBank_fiber_card, if_pos (hact p c h0)]
    exact (single_le_sum (f := fun c => (z p c).natAbs) (fun _ _ => Nat.zero_le _)
      (mem_univ c)).trans (hz p)

end

end S07V43
