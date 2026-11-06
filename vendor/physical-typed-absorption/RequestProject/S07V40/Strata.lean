/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V40.Process
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# Global finite macro-round bank, part 2: executed rounds and strata (V40)

* `numRounds S N` = number of executed rounds among `0, …, N-1`; they are exactly `0, …, R-1`.
* `sidx S r` = number of strict changes of `K (Z_s)` for `s < r`; the stratum of round `r`.
* `mStrat S N j` = number of executed rounds in stratum `j`; `preStrat S N j = ∑ i < j, m i`.
* Stratum `j` is exactly the interval `[pre j, pre (j+1))` of executed rounds, `K` is constant on
  it (equal to `Kstrat S N j = K (Zstrat S N j)`, `Zstrat S N j = Z_{pre j}`), and each label active
  for `Kstrat S N j` has EXACTLY `mStrat S N j` cells in stratum `j` (`countP_stratum`).
-/

@[expose] public section

namespace S07V40

open Finset Classical

noncomputable section

variable {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- Membership in a downward-closed filter of `range R` is an initial segment. -/
lemma lt_card_filter_range_iff {R : ℕ} {f : ℕ → Prop} [DecidablePred f] (hf : ∀ s t, s ≤ t → f t → f s)
    {t : ℕ} (ht : t < R) : f t ↔ t < ((range R).filter f).card := by
  constructor
  · intro hft
    have : range (t + 1) ⊆ (range R).filter f := by
      intro s hs
      rw [mem_range] at hs
      exact mem_filter.2 ⟨mem_range.2 (by omega), hf s t (by omega) hft⟩
    have := card_le_card this
    rw [card_range] at this
    omega
  · intro hlt
    by_contra hft
    have : (range R).filter f ⊆ range t := by
      intro s hs
      rw [mem_filter, mem_range] at hs
      rw [mem_range]
      by_contra hst
      exact hft (hf t s (by omega) hs.2)
    have := card_le_card this
    rw [card_range] at this
    omega

variable (S : MacroSetting V Q C)

/-- Number of executed rounds among the first `N`. -/
def numRounds (N : ℕ) : ℕ := ((range N).filter (fun t => Active S t)).card

variable {S}

lemma numRounds_le (N : ℕ) : numRounds S N ≤ N := by
  unfold numRounds
  exact (card_filter_le _ _).trans (card_range N).le

/-- The executed rounds are exactly `0, …, R-1`. -/
lemma active_iff_lt_numRounds {N t : ℕ} (ht : t < N) : Active S t ↔ t < numRounds S N :=
  lt_card_filter_range_iff (fun _ _ h ha => active_of_le h ha) ht

lemma active_of_lt_numRounds {N t : ℕ} (ht : t < numRounds S N) : Active S t :=
  (active_iff_lt_numRounds (lt_of_lt_of_le ht (numRounds_le N))).2 ht

/-- **Stopping dichotomy.** Either all `N` rounds were executed, or `K (Z_N) = ⊥`
(the process stopped at `K = 0`). -/
theorem stop_dichotomy (N : ℕ) : S.K (Zr S N) = ⊥ ∨ numRounds S N = N := by
  by_cases h : numRounds S N = N
  · exact Or.inr h
  · left
    have hlt : numRounds S N < N := lt_of_le_of_ne (numRounds_le N) h
    have hR : ¬ Active S (numRounds S N) :=
      fun ha => lt_irrefl _ ((active_iff_lt_numRounds hlt).1 ha)
    have : ¬ Active S N := fun ha => hR (active_of_le hlt.le ha)
    unfold Active at this
    exact not_not.1 this

/-- After the stop, the saturated set no longer changes; the final `K` equals `K (Z_R)`. -/
lemma K_numRounds_eq_bot {N : ℕ} (h : numRounds S N < N) : S.K (Zr S (numRounds S N)) = ⊥ := by
  have hR : ¬ Active S (numRounds S N) :=
    fun ha => lt_irrefl _ ((active_iff_lt_numRounds h).1 ha)
  unfold Active at hR
  exact not_not.1 hR

variable (S)

/-- Stratum index of round `r`: the number of strict changes of `K` before `r`. -/
def sidx (r : ℕ) : ℕ := ((range r).filter (fun s => S.K (Zr S (s + 1)) ≠ S.K (Zr S s))).card

/-- Number of executed rounds in stratum `j`. -/
def mStrat (N j : ℕ) : ℕ := ((range (numRounds S N)).filter (fun r => sidx S r = j)).card

/-- First round of stratum `j`: `∑ i < j, m i`. -/
def preStrat (N j : ℕ) : ℕ := ∑ i ∈ range j, mStrat S N i

/-- Initial saturated set of stratum `j`. -/
def Zstrat (N j : ℕ) : Finset V := Zr S (preStrat S N j)

/-- The constant subgroup of stratum `j`. -/
def Kstrat (N j : ℕ) : AddSubgroup Q := S.K (Zstrat S N j)

/-- Number of nonempty strata. -/
def numStrata (N : ℕ) : ℕ := if numRounds S N = 0 then 0 else sidx S (numRounds S N - 1) + 1

variable {S}

lemma sidx_zero : sidx S 0 = 0 := by simp [sidx]

lemma sidx_succ (r : ℕ) :
    sidx S (r + 1) = sidx S r + if S.K (Zr S (r + 1)) ≠ S.K (Zr S r) then 1 else 0 := by
  unfold sidx
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

lemma sidx_succ_le (r : ℕ) : sidx S (r + 1) ≤ sidx S r + 1 := by
  rw [sidx_succ]; split_ifs <;> omega

lemma sidx_mono : Monotone (sidx S) :=
  monotone_nat_of_le_succ (fun r => by rw [sidx_succ]; omega)

/-- Equal stratum index forces equal `K`. -/
lemma K_eq_of_sidx_eq {r r' : ℕ} (hrr : r ≤ r') (h : sidx S r = sidx S r') :
    S.K (Zr S r) = S.K (Zr S r') := by
  induction r', hrr using Nat.le_induction with
  | base => rfl
  | succ r' hr ih =>
    have h1 := sidx_mono (S := S) hr
    have h2 := sidx_succ (S := S) r'
    have hr' : sidx S r = sidx S r' := by
      have := sidx_mono (S := S) (Nat.le_succ r'); omega
    rw [ih hr']
    by_contra hne
    rw [if_pos (Ne.symm hne)] at h2
    omega

/-- Every stratum index up to `sidx r` is attained at or before `r`. -/
lemma exists_sidx_eq (r : ℕ) : ∀ j ≤ sidx S r, ∃ r' ≤ r, sidx S r' = j := by
  induction r with
  | zero => intro j hj; rw [sidx_zero] at hj; exact ⟨0, le_rfl, by rw [sidx_zero]; omega⟩
  | succ r ih =>
    intro j hj
    by_cases hj' : j ≤ sidx S r
    · obtain ⟨r', hr', h⟩ := ih j hj'
      exact ⟨r', by omega, h⟩
    · have := sidx_succ_le (S := S) r
      exact ⟨r + 1, le_rfl, by omega⟩

lemma card_filter_sidx_lt (N j : ℕ) :
    ((range (numRounds S N)).filter (fun r => sidx S r < j)).card = preStrat S N j := by
  induction j with
  | zero => simp [preStrat]
  | succ j ih =>
    rw [preStrat, sum_range_succ, ← preStrat, ← ih, mStrat, ← card_union_of_disjoint]
    · congr 1
      ext r; simp only [mem_filter, mem_union, mem_range]; constructor <;> intro h <;> omega
    · rw [disjoint_filter]; intro r _ h1 h2; omega

lemma preStrat_le (N j : ℕ) : preStrat S N j ≤ numRounds S N := by
  rw [← card_filter_sidx_lt]
  exact (card_filter_le _ _).trans (card_range _).le

lemma preStrat_succ (N j : ℕ) : preStrat S N (j + 1) = preStrat S N j + mStrat S N j :=
  sum_range_succ _ _

/-- `sidx r < j ↔ r < pre j` on executed rounds. -/
lemma sidx_lt_iff {N r j : ℕ} (hr : r < numRounds S N) : sidx S r < j ↔ r < preStrat S N j := by
  rw [← card_filter_sidx_lt]
  exact lt_card_filter_range_iff (fun s t hst h => lt_of_le_of_lt (sidx_mono (S := S) hst) h) hr

/-- **Stratum `j` is the interval `[pre j, pre (j+1))` of executed rounds.** -/
lemma sidx_eq_iff {N r j : ℕ} (hr : r < numRounds S N) :
    sidx S r = j ↔ preStrat S N j ≤ r ∧ r < preStrat S N (j + 1) := by
  have h1 := sidx_lt_iff (j := j) hr
  have h2 := sidx_lt_iff (j := j + 1) hr
  constructor
  · intro h
    exact ⟨not_lt.1 (fun h' => by have := h1.2 h'; omega), h2.1 (by omega)⟩
  · rintro ⟨ha, hb⟩
    have := h2.2 hb
    have : ¬ sidx S r < j := fun h' => by have := h1.1 h'; omega
    omega

/-- `K` is constant on stratum `j`, equal to `Kstrat S N j`. -/
lemma K_eq_Kstrat {N r j : ℕ} (hr : r < numRounds S N) (hj : sidx S r = j) :
    S.K (Zr S r) = Kstrat S N j := by
  obtain ⟨h1, h2⟩ := (sidx_eq_iff hr).1 hj
  have hp : preStrat S N j < numRounds S N := lt_of_le_of_lt h1 hr
  have hpj : sidx S (preStrat S N j) = j := (sidx_eq_iff hp).2 ⟨le_rfl, by omega⟩
  exact (K_eq_of_sidx_eq h1 (by rw [hpj, hj])).symm

lemma mStrat_pos_iff {N j : ℕ} : 0 < mStrat S N j ↔ ∃ r < numRounds S N, sidx S r = j := by
  unfold mStrat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨r, hr⟩; rw [mem_filter, mem_range] at hr; exact ⟨r, hr⟩
  · rintro ⟨r, hr, h⟩; exact ⟨r, mem_filter.2 ⟨mem_range.2 hr, h⟩⟩

/-- Nonempty strata are exactly `j < numStrata`. -/
lemma mStrat_pos_iff_lt_numStrata {N j : ℕ} : 0 < mStrat S N j ↔ j < numStrata S N := by
  rw [mStrat_pos_iff, numStrata]
  split_ifs with h0
  · simp [h0]
  · constructor
    · rintro ⟨r, hr, rfl⟩
      have := sidx_mono (S := S) (show r ≤ numRounds S N - 1 by omega)
      omega
    · intro hj
      obtain ⟨r', hr', h⟩ := exists_sidx_eq (S := S) (numRounds S N - 1) j (by omega)
      exact ⟨r', by omega, h⟩

/-! ### Exact counts per stratum (supply-free) -/

omit [Fintype V] [Fintype C] in
/-- Decomposing a count by the round field. -/
lemma countP_eq_sum_round {P : ℕ} (N : ℕ) (f : Placed V C P → Bool) :
    ∀ (L : List (Placed V C P)), (∀ p ∈ L, p.round < N) →
      L.countP f = ∑ r ∈ range N, L.countP (fun p => f p && decide (p.round = r))
  | [], _ => by simp
  | a :: L, hL => by
    rw [List.countP_cons, countP_eq_sum_round N f L (fun p hp => hL p (List.mem_cons_of_mem _ hp))]
    simp only [List.countP_cons]
    rw [sum_add_distrib]
    congr 1
    have ha := hL a (List.mem_cons_self ..)
    by_cases hfa : f a = true
    · simp [hfa, ha]
    · simp [hfa]

/-- **Exactly `m_j` cells per active label in stratum `j`.** For every stratum `j` and label
`l`, the number of bank cells of stratum `j` with label `l` is `m_j` if `g c ∈ Kstrat j` and `0`
otherwise.  (This is an equality, so no stratum can hide an incomplete round.) -/
theorem countP_stratum (N j : ℕ) (l : Lab C S.P) :
    (run S N).countP (fun p => decide (sidx S p.round = j ∧ p.lab = l)) =
      if S.g l.2.1 ∈ Kstrat S N j then mStrat S N j else 0 := by
  rw [countP_eq_sum_round N (fun p => sidx S p.round = j ∧ p.lab = l) (run S N)
    (run_round_lt N)]
  have hterm : ∀ r ∈ range N,
      (run S N).countP (fun p => decide (sidx S p.round = j ∧ p.lab = l) &&
          decide (p.round = r)) =
        if r < numRounds S N ∧ sidx S r = j ∧ S.g l.2.1 ∈ S.K (Zr S r) then 1 else 0 := by
    intro r hr
    rw [mem_range] at hr
    by_cases hj : sidx S r = j
    · rw [List.countP_congr (q := fun p => decide (p.round = r ∧ p.lab = l))
        (fun p _ => by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩; exact ⟨⟨by rw [h3, hj], h2⟩, h3⟩),
        countP_run]
      have ha := active_iff_lt_numRounds (S := S) hr
      by_cases h : r < numRounds S N <;> simp [hr, hj, h, ha]
    · rw [List.countP_eq_zero.2 (fun p _ => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro ⟨h1, _⟩ h3; rw [h3] at h1; exact hj h1)]
      simp [hj]
  rw [sum_congr rfl hterm, sum_boole]
  simp only [Nat.cast_id]
  split_ifs with hg
  · unfold mStrat
    congr 1
    ext r
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_lt_of_le h1 (numRounds_le N), h1, h2, by rw [K_eq_Kstrat h1 h2]; exact hg⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro r - ⟨h1, h2, h3⟩
    rw [K_eq_Kstrat h1 h2] at h3
    exact hg h3

/-- **Exactly one cell per executed round and active label**, in terms of `numRounds`. -/
theorem countP_round (N r : ℕ) (l : Lab C S.P) :
    (run S N).countP (fun p => decide (p.round = r ∧ p.lab = l)) =
      if r < numRounds S N ∧ S.g l.2.1 ∈ S.K (Zr S r) then 1 else 0 := by
  rw [countP_run]
  by_cases hr : r < N
  · rw [active_iff_lt_numRounds hr]
    by_cases h : r < numRounds S N <;> simp [hr, h]
  · have : ¬ r < numRounds S N := fun h => hr (lt_of_lt_of_le h (numRounds_le N))
    simp [hr, this]

/-! ### Bounded number of strata and the prefix bound (use the supply via `run_inv`) -/

lemma card_Zr_le {N t : ℕ} (hq : 0 < S.q) (hS : CellSupply S)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) (ht : t ≤ N) :
    S.q * (Zr S t).card ≤ 2 * S.E * S.Bstar * t ∧ (Zr S t).card ≤ S.zmax :=
  card_Zr_of_inv hq hcap ht (run_inv hq hS hcap t ht).2.1

/-- **At most `L+1` strata**: every executed round has stratum index `≤ L`. -/
theorem sidx_le {N L : ℕ} (hq : 0 < S.q) (hS : CellSupply S) (hL : ChainBound S L)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) {r : ℕ} (hr : r < numRounds S N) :
    sidx S r ≤ L := by
  have hR := numRounds_le (S := S) N
  have h1 : sidx S r ≤ sidx S (numRounds S N - 1) := sidx_mono (by omega)
  have h2 : sidx S (numRounds S N - 1) ≤ L :=
    hL (numRounds S N - 1) (Zr S) Zr_mono
      (fun i hi => (card_Zr_le hq hS hcap (by omega)).2)
  omega

theorem numStrata_le {N L : ℕ} (hq : 0 < S.q) (hS : CellSupply S) (hL : ChainBound S L)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) : numStrata S N ≤ L + 1 := by
  unfold numStrata
  split_ifs with h0
  · omega
  · have := sidx_le hq hS hL hcap (show numRounds S N - 1 < numRounds S N by omega)
    omega

theorem mStrat_eq_zero {N L : ℕ} (hq : 0 < S.q) (hS : CellSupply S) (hL : ChainBound S L)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) {j : ℕ} (hj : L < j) : mStrat S N j = 0 := by
  by_contra h
  obtain ⟨r, hr, rfl⟩ := mStrat_pos_iff.1 (Nat.pos_of_ne_zero h)
  have := sidx_le hq hS hL hcap hr
  omega

/-- The strata `0, …, L` cover all executed rounds. -/
theorem sum_mStrat {N L : ℕ} (hq : 0 < S.q) (hS : CellSupply S) (hL : ChainBound S L)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) :
    ∑ j ∈ range (L + 1), mStrat S N j = numRounds S N := by
  rw [← preStrat, ← card_filter_sidx_lt, filter_true_of_mem, card_range]
  intro r hr
  have := sidx_le hq hS hL hcap (mem_range.1 hr)
  omega

/-- **Prefix bound** for the initial saturated set of every stratum. -/
theorem card_Zstrat_le {N : ℕ} (hq : 0 < S.q) (hS : CellSupply S)
    (hcap : 2 * S.E * S.Bstar * N ≤ S.q * S.zmax) (j : ℕ) :
    S.q * (Zstrat S N j).card ≤ 2 * S.E * S.Bstar * ∑ i ∈ range j, mStrat S N i :=
  (card_Zr_le hq hS hcap ((preStrat_le N j).trans (numRounds_le N))).1

end

end S07V40
