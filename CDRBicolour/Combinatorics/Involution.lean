/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Set.Function
public import Mathlib.Tactic.Linarith

/-!
# Fixed-point-free involutions

* `exists_pairing_of_even_fibres`: if every fibre of `ω : I → X` has even size, there is a
  fixed-point-free involution `σ` of `I` with `ω ∘ σ = ω` (pair up each fibre).
* `exists_conj_of_card_eq`: two fixed-point-free involutions on finite types of the same
  cardinality are conjugate by a bijection.

Both are used in L184: classes omitting the same point are paired (A), and the pairs are
matched with the reserved perfect matching `M_A` of the class `A` (B).
-/

@[expose] public section

namespace CDRBicolour

open Finset

section Pairing

variable {I X : Type*} [DecidableEq I] [DecidableEq X] (ω : I → X)

theorem exists_pairing_on (n : ℕ) :
    ∀ s : Finset I, s.card = n → (∀ x, Even (s.filter fun i => ω i = x).card) →
      ∃ σ : I → I, (∀ i, σ (σ i) = i) ∧
        (∀ i ∈ s, σ i ≠ i ∧ σ i ∈ s ∧ ω (σ i) = ω i) ∧ (∀ i ∉ s, σ i = i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs heven
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · exact ⟨id, fun _ => rfl, by simp, fun _ _ => rfl⟩
    -- a partner of `i` in its fibre
    have hfib : 1 < (s.filter fun z => ω z = ω i).card := by
      have hpos : 0 < (s.filter fun z => ω z = ω i).card :=
        card_pos.2 ⟨i, mem_filter.2 ⟨hi, rfl⟩⟩
      obtain ⟨m, hm⟩ := heven (ω i)
      omega
    obtain ⟨j, hj, hji⟩ : ∃ j ∈ s.filter (fun z => ω z = ω i), j ≠ i := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hfib
      by_cases hai : a = i
      · exact ⟨b, hb, fun h => hab (hai.trans h.symm)⟩
      · exact ⟨a, ha, hai⟩
    rw [mem_filter] at hj
    obtain ⟨hjs, hωj⟩ := hj
    set t := (s.erase i).erase j with ht
    have hjt : j ∈ s.erase i := mem_erase.2 ⟨hji, hjs⟩
    have htcard : t.card + 2 = n := by
      rw [ht, card_erase_of_mem hjt, card_erase_of_mem hi]
      have : 2 ≤ s.card := by
        have := card_le_card (filter_subset (fun z => ω z = ω i) s); omega
      omega
    have hteven : ∀ x, Even (t.filter fun z => ω z = x).card := by
      intro x
      by_cases hx : x = ω i
      · subst hx
        have hi' : i ∈ s.filter fun z => ω z = ω i := mem_filter.2 ⟨hi, rfl⟩
        have hj' : j ∈ (s.filter fun z => ω z = ω i).erase i :=
          mem_erase.2 ⟨hji, mem_filter.2 ⟨hjs, hωj⟩⟩
        have hfe : (t.filter fun z => ω z = ω i) =
            ((s.filter fun z => ω z = ω i).erase i).erase j := by
          rw [ht, filter_erase, filter_erase]
        rw [hfe, card_erase_of_mem hj', card_erase_of_mem hi']
        obtain ⟨m, hm⟩ := heven (ω i)
        have : 2 ≤ (s.filter fun z => ω z = ω i).card := hfib
        exact ⟨m - 1, by omega⟩
      · have hfe : (t.filter fun z => ω z = x) = s.filter fun z => ω z = x := by
          rw [ht, filter_erase, filter_erase]
          rw [erase_eq_of_notMem, erase_eq_of_notMem]
          · intro h; exact hx ((mem_filter.1 h).2.symm)
          · intro h
            have h' := (mem_filter.1 (mem_of_mem_erase h)).2
            exact hx (h'.symm.trans hωj)
        rw [hfe]; exact heven x
    obtain ⟨σ', hinv, hin, hout⟩ := ih t.card (by omega) t rfl hteven
    have hit : i ∉ t := by simp [ht]
    have hjt' : j ∉ t := by simp [ht]
    have hσ'i : σ' i = i := hout i hit
    have hσ'j : σ' j = j := hout j hjt'
    refine ⟨fun z => if z = i then j else if z = j then i else σ' z, ?_, ?_, ?_⟩
    · intro z
      by_cases hzi : z = i
      · simp [hzi, hji]
      by_cases hzj : z = j
      · simp [hzj, hji]
      simp only [hzi, hzj, ite_false]
      by_cases hzt : z ∈ t
      · obtain ⟨-, hσt, -⟩ := hin z hzt
        have h1 : σ' z ≠ i := fun h => hit (h ▸ hσt)
        have h2 : σ' z ≠ j := fun h => hjt' (h ▸ hσt)
        simp [h1, h2, hinv z]
      · have := hout z hzt
        simp [this, hzi, hzj]
    · intro z hz
      by_cases hzi : z = i
      · subst hzi; simp [hji, hjs, hωj, Ne.symm hji]
      by_cases hzj : z = j
      · subst hzj; simp [hji, Ne.symm hji, hi, hωj]
      have hzt : z ∈ t := by simp [ht, hz, hzi, hzj]
      obtain ⟨h1, h2, h3⟩ := hin z hzt
      have hσs : σ' z ∈ s := mem_of_mem_erase (mem_of_mem_erase h2)
      simp only [hzi, hzj, ite_false]
      exact ⟨h1, hσs, h3⟩
    · intro z hz
      have hzi : z ≠ i := fun h => hz (h ▸ hi)
      have hzj : z ≠ j := fun h => hz (h ▸ hjs)
      have hzt : z ∉ t := fun h => hz (mem_of_mem_erase (mem_of_mem_erase h))
      simp [hzi, hzj, hout z hzt]

/-- **(A)** Even fibres admit a fibre-preserving fixed-point-free involution. -/
theorem exists_pairing_of_even_fibres [Fintype I]
    (heven : ∀ x, Even (univ.filter fun i => ω i = x).card) :
    ∃ σ : I → I, (∀ i, σ (σ i) = i) ∧ (∀ i, σ i ≠ i) ∧ (∀ i, ω (σ i) = ω i) := by
  obtain ⟨σ, hinv, hin, -⟩ := exists_pairing_on ω _ univ rfl heven
  exact ⟨σ, hinv, fun i => (hin i (mem_univ i)).1, fun i => (hin i (mem_univ i)).2.2⟩

end Pairing

section Conjugacy

variable {I A : Type*} [DecidableEq I] [DecidableEq A]
  (σ : I → I) (μ : A → A)

theorem exists_conj_on (a₀ : A) (hσ : ∀ i, σ (σ i) = i) (hσ' : ∀ i, σ i ≠ i)
    (hμ : ∀ u, μ (μ u) = u) (hμ' : ∀ u, μ u ≠ u) (n : ℕ) :
    ∀ (s : Finset I) (t : Finset A), s.card = n → s.card = t.card →
      (∀ i ∈ s, σ i ∈ s) → (∀ u ∈ t, μ u ∈ t) →
      ∃ φ : I → A, Set.BijOn φ s t ∧ ∀ i ∈ s, φ (σ i) = μ (φ i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hs hst hsc htc
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · have ht : t = ∅ := by rw [← card_eq_zero]; simp at hst; omega
      subst ht
      exact ⟨fun _ => a₀, ⟨by simp [Set.MapsTo], by simp [Set.InjOn], by simp [Set.SurjOn]⟩,
        by simp⟩
    obtain ⟨u, hu⟩ : t.Nonempty := by
      rw [← card_pos, ← hst]; exact card_pos.2 ⟨i, hi⟩
    have hσi : σ i ∈ s.erase i := mem_erase.2 ⟨hσ' i, hsc i hi⟩
    have hμu : μ u ∈ t.erase u := mem_erase.2 ⟨hμ' u, htc u hu⟩
    set s' := (s.erase i).erase (σ i) with hs'
    set t' := (t.erase u).erase (μ u) with ht'
    have hs'card : s'.card + 2 = s.card := by
      rw [hs', card_erase_of_mem hσi, card_erase_of_mem hi]
      have : 2 ≤ s.card := by
        have h2 : ({i, σ i} : Finset I) ⊆ s := by
          intro z hz; simp at hz; rcases hz with rfl | rfl
          · exact hi
          · exact hsc i hi
        have := card_le_card h2
        rw [card_pair (Ne.symm (hσ' i))] at this; exact this
      omega
    have ht'card : t'.card + 2 = t.card := by
      rw [ht', card_erase_of_mem hμu, card_erase_of_mem hu]
      omega
    have hs'c : ∀ z ∈ s', σ z ∈ s' := by
      intro z hz
      simp only [hs', mem_erase] at hz ⊢
      obtain ⟨hzσ, hzi, hzs⟩ := hz
      refine ⟨fun h => hzi ?_, fun h => hzσ ?_, hsc z hzs⟩
      · have := congrArg σ h; rw [hσ, hσ] at this; exact this
      · rw [← h, hσ]
    have ht'c : ∀ z ∈ t', μ z ∈ t' := by
      intro z hz
      simp only [ht', mem_erase] at hz ⊢
      obtain ⟨hzμ, hzu, hzt⟩ := hz
      refine ⟨fun h => hzu ?_, fun h => hzμ ?_, htc z hzt⟩
      · have := congrArg μ h; rw [hμ, hμ] at this; exact this
      · rw [← h, hμ]
    obtain ⟨φ', ⟨hmap, hinj, hsurj⟩, hcomm⟩ :=
      ih s'.card (by omega) s' t' rfl (by omega) hs'c ht'c
    have hi_s' : i ∉ s' := by simp [hs']
    have hσi_s' : σ i ∉ s' := by simp [hs']
    have hu_t' : u ∉ t' := by simp [ht']
    have hμu_t' : μ u ∉ t' := by simp [ht']
    let φ : I → A := fun z => if z = i then u else if z = σ i then μ u else φ' z
    have hφi : φ i = u := by simp [φ]
    have hφσi : φ (σ i) = μ u := by simp [φ, hσ' i]
    have hφz : ∀ z, z ≠ i → z ≠ σ i → φ z = φ' z := by
      intro z h1 h2; simp [φ, h1, h2]
    have hmem : ∀ z ∈ s, z = i ∨ z = σ i ∨ z ∈ s' := by
      intro z hz
      by_cases h1 : z = i
      · exact Or.inl h1
      by_cases h2 : z = σ i
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (by simp [hs', hz, h1, h2]))
    have hφ'ne : ∀ z ∈ s', φ' z ≠ u ∧ φ' z ≠ μ u := by
      intro z hz
      have := hmap hz
      exact ⟨fun h => hu_t' (h ▸ this), fun h => hμu_t' (h ▸ this)⟩
    have hne_of : ∀ z ∈ s', z ≠ i ∧ z ≠ σ i := by
      intro z hz
      exact ⟨fun h => hi_s' (h ▸ hz), fun h => hσi_s' (h ▸ hz)⟩
    refine ⟨φ, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      rcases hmem z hz with rfl | rfl | hz'
      · rw [hφi]; exact hu
      · rw [hφσi]; exact htc u hu
      · obtain ⟨h1, h2⟩ := hne_of z hz'
        rw [hφz z h1 h2]
        exact mem_of_mem_erase (mem_of_mem_erase (hmap hz'))
    · intro z hz w hw hzw
      rcases hmem z hz with rfl | rfl | hz' <;> rcases hmem w hw with rfl | rfl | hw'
      · rfl
      · rw [hφi, hφσi] at hzw; exact absurd hzw.symm (hμ' _)
      · obtain ⟨h1, h2⟩ := hne_of w hw'
        rw [hφi, hφz w h1 h2] at hzw; exact absurd hzw.symm (hφ'ne w hw').1
      · rw [hφi, hφσi] at hzw; exact absurd hzw (hμ' _)
      · rfl
      · obtain ⟨h1, h2⟩ := hne_of w hw'
        rw [hφσi, hφz w h1 h2] at hzw; exact absurd hzw.symm (hφ'ne w hw').2
      · obtain ⟨h1, h2⟩ := hne_of z hz'
        rw [hφi, hφz z h1 h2] at hzw; exact absurd hzw (hφ'ne z hz').1
      · obtain ⟨h1, h2⟩ := hne_of z hz'
        rw [hφσi, hφz z h1 h2] at hzw; exact absurd hzw (hφ'ne z hz').2
      · obtain ⟨h1, h2⟩ := hne_of z hz'
        obtain ⟨h3, h4⟩ := hne_of w hw'
        rw [hφz z h1 h2, hφz w h3 h4] at hzw
        exact hinj hz' hw' hzw
    · intro w hw
      by_cases h1 : w = u
      · exact ⟨i, hi, by rw [hφi, h1]⟩
      by_cases h2 : w = μ u
      · exact ⟨σ i, hsc i hi, by rw [hφσi, h2]⟩
      have hw' : w ∈ t' := by
        simp only [ht', mem_erase]; exact ⟨h2, h1, mem_coe.1 hw⟩
      obtain ⟨z, hz, hzw⟩ := hsurj hw'
      obtain ⟨h3, h4⟩ := hne_of z hz
      exact ⟨z, mem_of_mem_erase (mem_of_mem_erase hz), by rw [hφz z h3 h4]; exact hzw⟩
    · intro z hz
      rcases hmem z hz with rfl | rfl | hz'
      · rw [hφσi, hφi]
      · rw [hσ, hφi, hφσi, hμ]
      · obtain ⟨h1, h2⟩ := hne_of z hz'
        have hσz := hs'c z hz'
        obtain ⟨h3, h4⟩ := hne_of (σ z) hσz
        rw [hφz z h1 h2, hφz (σ z) h3 h4]
        exact hcomm z hz'

/-- **(B)** Two fixed-point-free involutions on finite types of equal cardinality are
conjugate. -/
theorem exists_conj_of_card_eq [Fintype I] [Fintype A]
    (hσ : ∀ i, σ (σ i) = i) (hσ' : ∀ i, σ i ≠ i)
    (hμ : ∀ u, μ (μ u) = u) (hμ' : ∀ u, μ u ≠ u)
    (hcard : Fintype.card I = Fintype.card A) :
    ∃ φ : I → A, Function.Bijective φ ∧ ∀ i, φ (σ i) = μ (φ i) := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · have hA : IsEmpty A := by
      rw [← Fintype.card_eq_zero_iff, ← hcard, Fintype.card_eq_zero_iff]; exact hI
    exact ⟨fun i => isEmptyElim i, ⟨fun i => isEmptyElim i, fun u => isEmptyElim u⟩,
      fun i => isEmptyElim i⟩
  have a₀ : A := by
    have : 0 < Fintype.card A := hcard ▸ Fintype.card_pos_iff.2 ⟨i₀⟩
    exact Classical.choice (Fintype.card_pos_iff.1 this)
  obtain ⟨φ, hbij, hcomm⟩ := exists_conj_on σ μ a₀ hσ hσ' hμ hμ' _ univ univ rfl
    (by simpa using hcard) (fun i _ => mem_univ _) (fun u _ => mem_univ _)
  refine ⟨φ, ?_, fun i => hcomm i (mem_univ i)⟩
  rw [← Set.bijOn_univ]
  simpa using hbij

end Conjugacy

end CDRBicolour
