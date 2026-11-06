/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V40.Strata
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# Global finite macro-round bank, part 3: modes and the main constructor theorem (V40)

* `modeUnion σ L` = union over the cells of `L` of their chosen mode (`A` if `σ p = false`,
  `A ∪ Y` if `σ p = true`).  Both modes are subsets of the same total cell.
* `MacroBank S L N` collects every invariant of the bank `run S N`.
* `macro_bank` proves `MacroBank S L N` from: `0 < q`, the cell-supply interface, basal
  inheritance, the chain bound `L`, and the cap premise `2 * E * Bstar * N ≤ q * zmax`.
-/

@[expose] public section

namespace S07V40

open Finset Classical

noncomputable section

variable {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

section modes
variable {P : ℕ}

/-- The chosen mode of a placed cell. -/
def modeSet (σ : Placed V C P → Bool) (p : Placed V C P) : Finset (Sym2 V) :=
  if σ p then p.cell.tot else p.cell.A

/-- Union of the chosen modes. -/
def modeUnion (σ : Placed V C P → Bool) : List (Placed V C P) → Finset (Sym2 V)
  | [] => ∅
  | p :: L => modeSet σ p ∪ modeUnion σ L

omit [Fintype V] [Fintype C] in
lemma modeSet_subset (σ : Placed V C P → Bool) (p : Placed V C P) :
    modeSet σ p ⊆ p.cell.tot := by
  unfold modeSet; split_ifs
  · exact subset_rfl
  · exact subset_union_left

omit [Fintype V] [Fintype C] in
lemma modeUnion_subset (σ : Placed V C P → Bool) :
    ∀ L : List (Placed V C P), modeUnion σ L ⊆ edgesOf L
  | [] => by simp [modeUnion]
  | p :: L => union_subset_union (modeSet_subset σ p) (modeUnion_subset σ L)

omit [Fintype V] [Fintype C] in
lemma disjoint_modeUnion {σ : Placed V C P → Bool} {p : Placed V C P} {L : List (Placed V C P)}
    (h : ∀ p' ∈ L, Disjoint p.cell.tot p'.cell.tot) : Disjoint (modeSet σ p) (modeUnion σ L) :=
  ((disjoint_edgesOf h).mono_right (modeUnion_subset σ L)).mono_left (modeSet_subset σ p)

end modes

variable {S : MacroSetting V Q C}

omit [Fintype V] [Fintype C] in
/-- **Compatible modes**: any choice of modes on a pairwise-disjoint list of good cells is basal. -/
theorem modeUnion_basal (hB : BasalInherit S) (σ : Placed V C S.P → Bool) :
    ∀ L : List (Placed V C S.P), (∀ p ∈ L, PlacedOK S p) →
      L.Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot) → S.basal (modeUnion σ L)
  | [], _, _ => hB.1
  | p :: L, hok, hpw => by
    rw [List.pairwise_cons] at hpw
    refine hB.2 _ _ (disjoint_modeUnion hpw.1) ?_
      (modeUnion_basal hB σ L (fun p' hp' => hok p' (List.mem_cons_of_mem _ hp')) hpw.2)
    have := hok p (List.mem_cons_self ..)
    unfold modeSet; split_ifs
    · exact this.2.2.1
    · exact this.2.1

omit [Fintype V] [Fintype C] in
/-- Charge of a mode union: `charge A` for every cell plus `± g c` for every cell switched on. -/
theorem charge_modeUnion (σ : Placed V C S.P → Bool) :
    ∀ L : List (Placed V C S.P), (∀ p ∈ L, PlacedOK S p) →
      L.Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot) →
      charge S.w (modeUnion σ L) = (L.map (fun p => charge S.w p.cell.A +
        if σ p then sgnQ p.lab.1 (S.g p.lab.2.1) else 0)).sum
  | [], _, _ => by simp [modeUnion, charge]
  | p :: L, hok, hpw => by
    rw [List.pairwise_cons] at hpw
    have hp := hok p (List.mem_cons_self ..)
    simp only [modeUnion, List.map_cons, List.sum_cons]
    rw [charge, sum_union (disjoint_modeUnion hpw.1), ← charge, ← charge,
      charge_modeUnion σ L (fun p' hp' => hok p' (List.mem_cons_of_mem _ hp')) hpw.2]
    congr 1
    unfold modeSet
    split_ifs
    · rw [Cell.tot, charge, sum_union hp.1, ← charge, ← charge, hp.2.2.2.2]
    · simp

/-- **All invariants of the global finite macro-round bank** `run S N`. -/
structure MacroBank (S : MacroSetting V Q C) (L N : ℕ) : Prop where
  /-- placed cells have pairwise disjoint total edge sets -/
  disjoint : (run S N).Pairwise (fun p p' => Disjoint p.cell.tot p'.cell.tot)
  /-- every placed cell is good and was placed in an executed round, avoiding that round's `Z`,
  for an active label -/
  cells : ∀ p ∈ run S N, PlacedOK S p ∧ p.round < numRounds S N ∧
    S.g p.lab.2.1 ∈ S.K (Zr S p.round) ∧ Avoids (Zr S p.round) p.cell.tot
  /-- every choice of on/off modes is basal -/
  modes_basal : ∀ σ : Placed V C S.P → Bool, S.basal (modeUnion σ (run S N))
  /-- charge of every mode choice -/
  modes_charge : ∀ σ : Placed V C S.P → Bool, charge S.w (modeUnion σ (run S N)) =
    ((run S N).map (fun p => charge S.w p.cell.A +
      if σ p then sgnQ p.lab.1 (S.g p.lab.2.1) else 0)).sum
  /-- every mode choice lies inside the used edges -/
  modes_sub : ∀ σ : Placed V C S.P → Bool, modeUnion σ (run S N) ⊆ Br S N
  /-- maximum degree of the whole bank `< q + Bstar * E` -/
  maxdeg : ∀ v, deg (Br S N) v < S.q + S.Bstar * S.E
  /-- edge count after `t` rounds -/
  edges : ∀ t ≤ N, (Br S t).card ≤ S.E * S.Bstar * t
  /-- the edge count is the sum of the (disjoint) cell sizes; both modes are inside one cell -/
  edges_exact : (Br S N).card = ((run S N).map (fun p => p.cell.tot.card)).sum
  /-- saturated sets after `t` rounds -/
  sat : ∀ t ≤ N, S.q * (Zr S t).card ≤ 2 * S.E * S.Bstar * t
  /-- smallness, derived from the global count and the cap -/
  small : ∀ t ≤ N, (Zr S t).card ≤ S.zmax
  /-- `Z` starts empty -/
  zero : Zr S 0 = ∅
  /-- `Z` only grows -/
  mono : Monotone (Zr S)
  /-- executed rounds have `K ≠ 0` -/
  active : ∀ r < numRounds S N, S.K (Zr S r) ≠ ⊥
  /-- each executed round has EXACTLY one cell per active label, and no other round has cells -/
  round_exact : ∀ (r : ℕ) (l : Lab C S.P),
    (run S N).countP (fun p => decide (p.round = r ∧ p.lab = l)) =
      if r < numRounds S N ∧ S.g l.2.1 ∈ S.K (Zr S r) then 1 else 0
  /-- every executed round lies in one of the strata `0, …, L` -/
  strata_le : ∀ r < numRounds S N, sidx S r ≤ L
  /-- at most `L+1` nonempty strata -/
  numStrata_le : numStrata S N ≤ L + 1
  /-- nonempty strata are exactly `j < numStrata` -/
  m_pos_iff : ∀ j, 0 < mStrat S N j ↔ j < numStrata S N
  /-- strata beyond `L` are empty -/
  m_zero : ∀ j, L < j → mStrat S N j = 0
  /-- the strata cover all executed rounds -/
  m_sum : ∑ j ∈ range (L + 1), mStrat S N j = numRounds S N
  /-- stratum `j` is the chronological interval `[∑ i<j, m i, ∑ i≤j, m i)` -/
  interval : ∀ r < numRounds S N, ∀ j, sidx S r = j ↔
    ∑ i ∈ range j, mStrat S N i ≤ r ∧ r < ∑ i ∈ range (j + 1), mStrat S N i
  /-- `K` is constant on each stratum -/
  K_const : ∀ r < numRounds S N, S.K (Zr S r) = Kstrat S N (sidx S r)
  /-- EXACTLY `m_j` cells per active label in stratum `j` -/
  stratum_exact : ∀ (j : ℕ) (l : Lab C S.P),
    (run S N).countP (fun p => decide (sidx S p.round = j ∧ p.lab = l)) =
      if S.g l.2.1 ∈ Kstrat S N j then mStrat S N j else 0
  /-- prefix bound for the initial saturated set of each stratum -/
  prefix_bound : ∀ j, S.q * (Zstrat S N j).card ≤
    2 * S.E * S.Bstar * ∑ i ∈ range j, mStrat S N i
  /-- stopping dichotomy -/
  dichotomy : S.K (Zr S N) = ⊥ ∨ ∑ j ∈ range (L + 1), mStrat S N j = N

/-- **Global finite macro-round bank constructor.** From the cell-supply interface (and `q > 0`,
basal inheritance, the chain bound, the cap), the process `run S N` satisfies every invariant. -/
theorem macro_bank {L N : ℕ} (hq : 0 < S.q) (hS : CellSupply S) (hB : BasalInherit S)
    (hL : ChainBound S L) (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) : MacroBank S L N := by
  obtain ⟨hdeg, hcard, hcells, hpw⟩ := run_inv hq hS hcap N le_rfl
  have hok : ∀ p ∈ run S N, PlacedOK S p := fun p hp => (hcells p hp).1
  have hsum := sum_mStrat hq hS hL hcap
  refine
    { disjoint := hpw
      cells := fun p hp => ?_
      modes_basal := fun σ => modeUnion_basal hB σ _ hok hpw
      modes_charge := fun σ => charge_modeUnion σ _ hok hpw
      modes_sub := fun σ => modeUnion_subset σ _
      maxdeg := hdeg
      edges := fun t ht => (run_inv hq hS hcap t ht).2.1
      edges_exact := card_edgesOf_eq hpw
      sat := fun t ht => (card_Zr_le hq hS hcap ht).1
      small := fun t ht => (card_Zr_le hq hS hcap ht).2
      zero := by simp [Zr, Zof, run, satSet_empty hq]
      mono := Zr_mono
      active := fun r hr => active_of_lt_numRounds hr
      round_exact := countP_round N
      strata_le := fun r hr => sidx_le hq hS hL hcap hr
      numStrata_le := numStrata_le hq hS hL hcap
      m_pos_iff := fun j => mStrat_pos_iff_lt_numStrata
      m_zero := fun j hj => mStrat_eq_zero hq hS hL hcap hj
      m_sum := hsum
      interval := fun r hr j => sidx_eq_iff hr
      K_const := fun r hr => K_eq_Kstrat hr rfl
      stratum_exact := countP_stratum N
      prefix_bound := card_Zstrat_le hq hS hcap
      dichotomy := by rw [hsum]; exact stop_dichotomy N }
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcells p hp
  have hlt : p.round < numRounds S N :=
    (active_iff_lt_numRounds h2).1 h3
  exact ⟨h1, hlt, h4, h5⟩

end

end S07V40
