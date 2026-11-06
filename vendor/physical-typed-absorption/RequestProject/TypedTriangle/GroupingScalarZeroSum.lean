module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TypedTriangle.GroupingExplicit

/-- A scalar zero-sum family can be ordered with all translated partial
    sums inside the original interval. -/
theorem scalar_bounded_order {ι : Type} (z : ι → ℤ) (D : ℕ)
    (s : Finset ι) (hz : ∀ i ∈ s, |z i| ≤ (D : ℤ))
    (a : ℤ) (ha : |a| ≤ (D : ℤ)) (hs : a + ∑ i ∈ s, z i = 0) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = s ∧
      ∀ k ≤ l.length, |a + ((l.take k).map z).sum| ≤ (D : ℤ) := by
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, by simp, by simpa using ha⟩
    have hnext : ∃ i ∈ s, |a + z i| ≤ (D : ℤ) := by
      by_cases ha0 : 0 ≤ a
      · have hex : ∃ i ∈ s, z i ≤ 0 := by
          by_contra h
          have hall : ∀ i ∈ s, 0 < z i := by simpa only [not_exists, not_and,
            not_le] using h
          have hsum : 0 < ∑ i ∈ s, z i := Finset.sum_pos hall hne
          omega
        obtain ⟨i, hi, hzi⟩ := hex
        exact ⟨i, hi, abs_le.mpr ⟨by have := (abs_le.mp (hz i hi)).1; omega,
          by have := (abs_le.mp ha).2; omega⟩⟩
      · have hex : ∃ i ∈ s, 0 ≤ z i := by
          by_contra h
          have hall : ∀ i ∈ s, z i < 0 := by simpa only [not_exists, not_and,
            not_le] using h
          have hsum : ∑ i ∈ s, z i < 0 := Finset.sum_neg hall hne
          omega
        obtain ⟨i, hi, hzi⟩ := hex
        exact ⟨i, hi, abs_le.mpr ⟨by have := (abs_le.mp ha).1; omega,
          by have := (abs_le.mp (hz i hi)).2; omega⟩⟩
    obtain ⟨i, hi, hai⟩ := hnext
    have hrest : a + z i + ∑ j ∈ s.erase i, z j = 0 := by
      have heq := Finset.sum_erase_add s z hi
      omega
    obtain ⟨l, hn, hl, hb⟩ := ih (s.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hz j (Finset.mem_of_mem_erase hj)) (a + z i) hai hrest
    refine ⟨i :: l, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨by simpa [← List.mem_toFinset, hl] using Finset.not_mem_erase i s, hn⟩
    · simp only [List.toFinset_cons, hl, Finset.insert_erase hi]
    · intro k hk
      cases k with
      | zero => simpa using ha
      | succ k =>
        have h := hb k (by simpa using hk)
        simpa [List.take_succ_cons, add_assoc] using h

#print axioms scalar_bounded_order

/-- An inclusion-minimal scalar zero-sum family has bounded cardinality. -/
theorem scalar_atom_card_bound {ι : Type} (z : ι → ℤ) (D : ℕ)
    (s : Finset ι) (hz : ∀ i ∈ s, |z i| ≤ (D : ℤ))
    (hs : ∑ i ∈ s, z i = 0)
    (hmin : ∀ t ⊆ s, t.Nonempty → (∑ i ∈ t, z i = 0) → t = s) :
    s.card ≤ 2 * D + 1 := by
  obtain ⟨l, hn, hl, hb⟩ := scalar_bounded_order z D s hz 0 (by simp) (by simpa using hs)
  let p : ℕ → Finset ι := fun k => (l.take k).toFinset
  have hc : ∀ k ≤ l.length, (p k).card = k := by
    intro k hk
    simp only [p, List.toFinset_card_of_nodup (hn.take (i := k)), List.length_take,
      Nat.min_eq_left hk]
  have hsub : ∀ a b, a ≤ b → p a ⊆ p b := by
    intro a b hab x hx
    simp only [p, List.mem_toFinset] at hx ⊢
    exact List.take_subset_take_left l hab hx
  have hps : ∀ k, p k ⊆ s := by
    intro k x hx
    rw [← hl, List.mem_toFinset]
    exact List.take_subset k l (by simpa only [p, List.mem_toFinset] using hx)
  have hsum : ∀ k, (∑ i ∈ p k, z i) = ((l.take k).map z).sum := by
    intro k
    exact List.sum_toFinset z (hn.take (i := k))
  have hstrict : ∀ a b, a < b → b < l.length →
      (∑ i ∈ p a, z i) ≠ ∑ i ∈ p b, z i := by
    intro a b hab hbl heq
    have hsubset := hsub a b hab.le
    have hcard : (p b \ p a).card = b - a := by
      rw [Finset.card_sdiff_of_subset hsubset, hc b hbl.le, hc a (by omega)]
    have hne : (p b \ p a).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    have hzero : ∑ i ∈ p b \ p a, z i = 0 := by
      have ht := Finset.sum_sdiff hsubset (f := z)
      omega
    have ht := hmin (p b \ p a) (sdiff_subset.trans (hps b)) hne hzero
    have hlcard : s.card = l.length := by rw [← hl, List.toFinset_card_of_nodup hn]
    rw [ht, hlcard] at hcard
    omega
  have hbound := Finset.card_le_card_of_injOn
    (s := Finset.range l.length) (t := Finset.Icc (-(D : ℤ)) (D : ℤ))
    (fun k => ∑ i ∈ p k, z i)
    (by
      intro k hk
      change (∑ i ∈ p k, z i) ∈ Finset.Icc (-(D : ℤ)) (D : ℤ)
      rw [Finset.mem_Icc, ← abs_le, hsum]
      simpa using hb k (Finset.mem_range.mp hk).le)
    (by
      intro a ha b hb heq
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact hstrict a b hab hb' heq
      · exact hstrict b a hba ha' heq.symm)
  have hi : (Finset.Icc (-(D : ℤ)) (D : ℤ)).card = 2 * D + 1 := by
    rw [Int.card_Icc]
    omega
  rw [Finset.card_range, hi] at hbound
  simpa only [← hl, List.toFinset_card_of_nodup hn] using hbound

/-- Every nonempty scalar zero-sum family contains a short zero-sum block. -/
theorem scalar_zero_sum_small_block {ι : Type} (z : ι → ℤ) (D : ℕ)
    (s : Finset ι) (hz : ∀ i ∈ s, |z i| ≤ (D : ℤ))
    (hne : s.Nonempty) (hs : ∑ i ∈ s, z i = 0) :
    ∃ t ⊆ s, t.Nonempty ∧ t.card ≤ 2 * D + 1 ∧ ∑ i ∈ t, z i = 0 := by
  let good := s.powerset.filter fun t => t.Nonempty ∧ ∑ i ∈ t, z i = 0
  have hsg : s ∈ good := by simp only [good, Finset.mem_filter,
    Finset.mem_powerset, subset_refl, true_and]; exact ⟨hne, hs⟩
  obtain ⟨t, htg, htmin⟩ := Finset.exists_min_image good Finset.card ⟨s, hsg⟩
  obtain ⟨hts, htn, ht0⟩ := by simpa only [good, Finset.mem_filter,
    Finset.mem_powerset] using htg
  refine ⟨t, hts, htn, scalar_atom_card_bound z D t
    (fun i hi => hz i (hts hi)) ht0 ?_, ht0⟩
  intro u hut hun hu0
  have hug : u ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hut.trans hts, hun, hu0⟩
  exact Finset.eq_of_subset_of_card_le hut (htmin u hug)

/-- A scalar zero-sum family partitions into uniformly short zero-sum blocks. -/
theorem scalar_zero_sum_partition {ι : Type} (z : ι → ℤ) (D : ℕ)
    (s : Finset ι) (hz : ∀ i ∈ s, |z i| ≤ (D : ℤ))
    (hs : ∑ i ∈ s, z i = 0) :
    ∃ P : Finpartition s, ∀ t ∈ P.parts,
      t.card ≤ 2 * D + 1 ∧ ∑ i ∈ t, z i = 0 := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Finpartition.empty _, by simp⟩
    obtain ⟨t, hts, htn, htc, ht0⟩ := scalar_zero_sum_small_block z D s hz hne hs
    have hrest : ∑ i ∈ s \ t, z i = 0 := by
      have ht := Finset.sum_sdiff hts (f := z)
      omega
    obtain ⟨P, hP⟩ := ih (s \ t) (Finset.sdiff_ssubset hts htn)
      (fun i hi => hz i (Finset.mem_sdiff.mp hi).1) hrest
    refine ⟨P.extend (b := t) (Finset.nonempty_iff_ne_empty.mp htn)
      Finset.sdiff_disjoint (Finset.sdiff_union_of_subset hts), ?_⟩
    intro u hu
    rw [Finpartition.extend_parts, Finset.mem_insert] at hu
    rcases hu with rfl | hu
    · exact ⟨htc, ht0⟩
    · exact hP u hu

#print axioms scalar_atom_card_bound
#print axioms scalar_zero_sum_small_block
#print axioms scalar_zero_sum_partition

end TypedTriangle.GroupingExplicit
