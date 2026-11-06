/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedHingeTransport

@[expose] public section

/-! H4 inheritance on the actual surviving vertex type. NOT kernel-checked. -/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma surviving_hinges_card_le (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) (u v a b : Survivors Z) (i : ℕ)
    (hTa : IsAllowed H F {u.1,v.1,a.1}) (hTb : IsAllowed H F {u.1,v.1,b.1}) :
    ((hinges H F u.1 v.1 a.1 b.1 i).filter (fun J => Disjoint (support J) Z)).card ≤
      (hinges (restrictedHost H Z) F u v a b i).card := by
  refine Finset.card_le_card_of_injOn (fun J => restrictEdgeSet Z J) ?_ ?_
  · intro J hJ
    obtain ⟨hJ,hd⟩ := Finset.mem_filter.1 hJ
    have hparts := (Finset.mem_filter.1 hJ).2
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _, isHinge_restrictEdgeSet H F Z u v a b hparts.1 hd hTa hTb,
      (card_support_restrictEdgeSet Z J hd).trans hparts.2⟩
  · intro J hJ K hK heq
    exact restrictEdgeSet_injective_on_avoiding Z
      (Finset.mem_filter.1 hJ).2 (Finset.mem_filter.1 hK).2 heq

/-- H4 loses at most a factor two under a uniform vertex-deletion budget. -/
theorem hingeCond_restrictedHost {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 ≤ α) (hH4 : HingeCond H F α h) (Z : Finset V)
    (hZ : (Z.card : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ α / 2 * Fintype.card V) :
    HingeCond (restrictedHost H Z) F (α/2) h := by
  intro u v a b hab hTa hTb
  have hab' : a.1 ≠ b.1 := fun heq => hab (Subtype.ext heq)
  have hTa' : IsAllowed H F {u.1,v.1,a.1} := by
    apply (isAllowed_restricted_triple H F Z u v a).1
    convert hTa using 1 <;> ext x <;> simp
  have hTb' : IsAllowed H F {u.1,v.1,b.1} := by
    apply (isAllowed_restricted_triple H F Z u v b).1
    convert hTb using 1 <;> ext x <;> simp
  obtain ⟨i,hi6,hih,hsupply⟩ := hH4 u.1 v.1 a.1 b.1 hab' hTa' hTb'
  have hpow : (Fintype.card V : ℝ) ^ (i-4) =
      Fintype.card V * (Fintype.card V : ℝ) ^ (i-5) := by
    rw [← pow_succ']; congr 1; omega
  have hchoose : (2 : ℝ) ^ Nat.choose (i+1) 2 ≤ 2 ^ Nat.choose (h+1) 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (by omega))
  have hbudget : (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i-5) * 2 ^ Nat.choose (i+1) 2 ≤
      α/2 * (Fintype.card V : ℝ) ^ (i-4) := by
    rw [hpow]
    calc (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i-5) * 2 ^ Nat.choose (i+1) 2
        ≤ (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i-5) * 2 ^ Nat.choose (h+1) 2 :=
          mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = ((Z.card : ℝ) * 2 ^ Nat.choose (h+1) 2) * (Fintype.card V : ℝ) ^ (i-5) := by ring
      _ ≤ (α/2 * Fintype.card V) * (Fintype.card V : ℝ) ^ (i-5) :=
          mul_le_mul_of_nonneg_right hZ (by positivity)
      _ = α/2 * (Fintype.card V * (Fintype.card V : ℝ) ^ (i-5)) := by ring
  have hfresh := fresh_hinges hab' hTa' hTb' i (by omega) α Z hsupply hbudget
  have hfilter :
      (hinges H F u.1 v.1 a.1 b.1 i).filter
        (fun J => ∀ z ∈ Z, z ∈ support J → z ∈ ({u.1,v.1,a.1,b.1} : Finset V)) =
      (hinges H F u.1 v.1 a.1 b.1 i).filter (fun J => Disjoint (support J) Z) := by
    apply Finset.filter_congr
    intro J _
    constructor
    · intro hJ
      rw [Finset.disjoint_left]
      intro z hzJ hzZ
      have hzR := hJ z hzZ hzJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzR
      rcases hzR with rfl | rfl | rfl | rfl
      exacts [u.2 hzZ, v.2 hzZ, a.2 hzZ, b.2 hzZ]
    · intro hd z hzZ hzJ
      exact False.elim (Finset.disjoint_left.1 hd hzJ hzZ)
  rw [hfilter] at hfresh
  have hcount := surviving_hinges_card_le H F Z u v a b i hTa' hTb'
  have hN : (Fintype.card (Survivors Z) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun v : Survivors Z => v.1) Subtype.val_injective
  refine ⟨i,hi6,hih,?_⟩
  calc α/2 * (Fintype.card (Survivors Z) : ℝ) ^ (i-4)
      ≤ α/2 * (Fintype.card V : ℝ) ^ (i-4) := by gcongr
    _ ≤ ((hinges H F u.1 v.1 a.1 b.1 i).filter (fun J => Disjoint (support J) Z)).card := hfresh
    _ ≤ (hinges (restrictedHost H Z) F u v a b i).card := by exact_mod_cast hcount

lemma original_geometry_vertex_budget {α : ℝ} (hα : 0 < α) (h : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ {n z : ℝ}, 0 ≤ n → z ≤ δ*n →
        z ≤ α*n/2 ∧ z * 2 ^ Nat.choose (h+1) 2 ≤ α/2*n := by
  let M : ℝ := 2 ^ Nat.choose (h+1) 2
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  let δ : ℝ := min (1/2) (α/(4*M))
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ,hd,min_le_left _ _,?_⟩
  intro n z hn hz
  have hzM : z*M ≤ α*n/4 := by
    have hδ : δ ≤ α/(4*M) := min_le_right _ _
    have h1 := mul_le_mul_of_nonneg_right hδ hn
    have h2 := mul_le_mul_of_nonneg_right (hz.trans h1) (by positivity : 0 ≤ M)
    calc z*M ≤ (α/(4*M)*n)*M := h2
      _ = α*n/4 := by field_simp
  have hz0 : z ≤ α*n/4 := by
    by_cases hnon : 0 ≤ z
    · exact (le_mul_of_one_le_right hnon hM).trans hzM
    · have : z < 0 := lt_of_not_ge hnon
      exact this.le.trans (by positivity)
  have hαn : 0 ≤ α*n := mul_nonneg hα.le hn
  change z ≤ α*n/2 ∧ z*M ≤ α/2*n
  constructor <;> linarith

theorem original_geometry_restrictedHost {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 ≤ α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Z : Finset V)
    (hZ3 : (Z.card : ℝ) ≤ α * Fintype.card V / 2)
    (hZ4 : (Z.card : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ α/2 * Fintype.card V) :
    CommonNbrCond (restrictedHost H Z) F (α/2) ∧
      HingeCond (restrictedHost H Z) F (α/2) h :=
  ⟨commonNbrCond_restrictedHost hα hH3 Z hZ3,
    hingeCond_restrictedHost hα hH4 Z hZ4⟩

end TypedTriangle
