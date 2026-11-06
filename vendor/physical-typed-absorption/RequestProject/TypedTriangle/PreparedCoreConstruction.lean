/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VertexFirstEntry
public import RequestProject.TypedTriangle.CertDispersal

@[expose] public section

/-! Construct the prepared core from the original physical hypotheses.
Local proof candidate, pending the rc3 audit. No persistence provider is an
assumption of the final existence theorem. -/

open Finset Classical
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma restrictedHost_G_eq_dispersal (H : Host V I) (Z : Finset V) :
    (restrictedHost H Z).G = Dispersal.subG H.G Z := by
  ext u v
  rfl

lemma restrictedHost_lab_eq_dispersal (H : Host V I) (Z : Finset V) :
    (restrictedHost H Z).lab = Dispersal.subLab H.lab Z := rfl

lemma prepared_commonNbrCond_iff (H : Host V I) (F : Set (Multiset I)) (α : ℝ) :
    CommonNbrCond H F α ↔ SparseEdge.CommonNbrCond H.G H.lab F α := Iff.rfl

lemma prepared_hingeCond_iff (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) :
    HingeCond H F α h ↔ SparseEdge.HingeCond H.G H.lab F α h := Iff.rfl

lemma edgeZeroExtend_touch_lift (A : Finset V) (Z : Finset (Survivors A))
    (y : Sym2 (Survivors A) → ℤ)
    (hy : ∀ e, TouchZ Z e → y e = 0) :
    ∀ e, TouchZ (liftVertexSet A Z) e → edgeZeroExtend A y e = 0 := by
  intro e he
  by_cases hav : ∀ v ∈ e, v ∉ A
  · obtain ⟨v, hv, hve⟩ := he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    have hw' : w ∈ e.attachWith hav := by
      have hvmap : w.1 ∈ (e.attachWith hav).map Subtype.val := by
        rw [Sym2.attachWith_map_subtypeVal]
        exact hve
      obtain ⟨w', hw', heq⟩ := Sym2.mem_map.mp hvmap
      have heq' : w' = w := Subtype.ext heq
      simpa only [heq'] using hw'
    change (if h : ∀ v ∈ e, v ∉ A then y (e.attachWith h) else 0) = 0
    rw [dif_pos hav]
    exact hy _ ⟨w, hw, hw'⟩
  · push_neg at hav
    obtain ⟨v, hve, hv⟩ := hav
    exact edgeZeroExtend_vanish A y e ⟨v, hv, hve⟩

/-- The first-entry persistence statement transports to the genuine induced host. -/
lemma induced_lattice_persistence (H : Host V I) (F : Set (Multiset I))
    (A : Finset V) (b : ℕ)
    (hp : ∀ B : Finset V, B.card ≤ b → ∀ x ∈ lattice (vertexDeleted H A) F,
      (∀ e, TouchZ B e → x e = 0) → x ∈ lattice (vertexDeleted H (A ∪ B)) F)
    (Z : Finset (Survivors A)) (hZ : Z.card ≤ b)
    {y : Sym2 (Survivors A) → ℤ} (hy : y ∈ lattice (restrictedHost H A) F)
    (hz : ∀ e, TouchZ Z e → y e = 0) :
    edgeRestrict Z y ∈ lattice (restrictedHost (restrictedHost H A) Z) F := by
  have hB : (liftVertexSet A Z).card ≤ b := by
    rw [card_liftVertexSet]
    exact hZ
  have hx := hp (liftVertexSet A Z) hB (edgeZeroExtend A y)
    (edgeZeroExtend_mem_lattice H F A hy) (edgeZeroExtend_touch_lift A Z y hz)
  rw [← vertexDeleted_vertexDeleted H A (liftVertexSet A Z)] at hx
  have hr := edgeRestrict_mem_lattice (vertexDeleted H (liftVertexSet A Z)) F A hx
  rw [restrictedHost_vertexDeleted, subtype_liftVertexSet, edgeRestrict_zeroExtend] at hr
  exact edgeRestrict_mem_lattice (restrictedHost H A) F Z hr

/-- Uniformly prepare an induced core with integer persistence under all small
deletions. Constants and the order threshold precede the host. -/
theorem preparedCore_with_geometry_of_H3H4 (α : ℝ) (h N : ℕ) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab
            F (α / 4) h N β := by
  obtain ⟨ε, hε, d, T, nEntry, hT, hentry⟩ :=
    physical_vertex_first_entry_lattice α h hα
  obtain ⟨δ₀, hδ₀, hδ₀half, hbudget₀⟩ := original_geometry_vertex_budget hα h
  obtain ⟨δ₁, hδ₁, hδ₁half, hbudget₁⟩ :=
    original_geometry_vertex_budget (by positivity : 0 < α / 2) h
  let L := d + (d + 1) * Nat.log 2 T
  let η : ℝ := min (min ε δ₀) (1 / 2)
  let β : ℝ := min (η / (2 * (L + 1))) δ₁
  have hη : 0 < η := lt_min (lt_min hε hδ₀) (by norm_num)
  have hβ : 0 < β := lt_min (by positivity) hδ₁
  have hηε : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hβδ : β ≤ δ₁ := min_le_right _ _
  have hβscale : (L + 1 : ℝ) * β ≤ η / 2 := by
    have hb : β ≤ η / (2 * (L + 1)) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ L + 1 by positivity)
    have heq : (L + 1 : ℝ) * (η / (2 * (L + 1))) = η / 2 := by field_simp
    linarith
  have hβquarter : β ≤ 1 / 4 := by
    have : β ≤ (L + 1 : ℝ) * β := by nlinarith [show (0 : ℝ) ≤ L by positivity]
    linarith
  refine ⟨β, hβ, max nEntry (4 * N + 1), ?_⟩
  intro V I _ H F hn hH3 hH4
  let n := Fintype.card V
  let b := ⌊β * n⌋₊
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hb : (b : ℝ) ≤ β * n := Nat.floor_le (by positivity)
  have hscale : ((L + 1 : ℕ) : ℝ) * b ≤ η * n / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (L + 1 : ℕ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hβscale hn0
    push_cast at h1 ⊢
    nlinarith
  have hentryBudget : (((L + 1) * b : ℕ) : ℝ) ≤ ε * n := by
    push_cast
    have := mul_le_mul_of_nonneg_right hηε hn0
    nlinarith
  obtain ⟨A, hA, hp⟩ := hentry H F ((le_max_left _ _).trans hn) hH3 hH4 b hentryBudget
  letI : DecidableEq (Survivors A) := Classical.decEq _
  have hAR : (A.card : ℝ) ≤ η * n / 2 := by
    have hAN : A.card ≤ (L + 1) * b := hA.trans (Nat.mul_le_mul_right b (Nat.le_succ L))
    have hANR : (A.card : ℝ) ≤ (((L + 1) * b : ℕ) : ℝ) := by exact_mod_cast hAN
    push_cast at hANR hscale
    exact hANR.trans hscale
  have hAquart : (A.card : ℝ) ≤ (n : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hηhalf hn0
    linarith
  have hAδ : (A.card : ℝ) ≤ δ₀ * n := by
    have := mul_le_mul_of_nonneg_right hηδ hn0
    nlinarith
  obtain ⟨hA3, hA4⟩ := hbudget₀ hn0 hAδ
  have hg := original_geometry_restrictedHost hα.le hH3 hH4 A hA3 hA4
  have hcard := card_survivors_add_card A
  have hcardR : (Fintype.card (Survivors A) : ℝ) + A.card = n := by exact_mod_cast hcard
  have hnA : (Fintype.card (Survivors A) : ℝ) ≤ n := by
    nlinarith [show (0 : ℝ) ≤ A.card by positivity]
  refine ⟨A, hAquart, hg.1, hg.2, ?_⟩
  have hzδ (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β * Fintype.card (Survivors A)) :
      (Z.card : ℝ) ≤ δ₁ * Fintype.card (Survivors A) :=
    hZ.trans (mul_le_mul_of_nonneg_right hβδ (by positivity))
  have hgeom (Z : Finset (Survivors A))
      (hZ : (Z.card : ℝ) ≤ β * Fintype.card (Survivors A)) :=
    original_geometry_restrictedHost (by positivity : 0 ≤ α / 2) hg.1 hg.2 Z
      (hbudget₁ (by positivity) (hzδ Z hZ)).1
      (hbudget₁ (by positivity) (hzδ Z hZ)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z hZ
    rw [← restrictedHost_G_eq_dispersal (restrictedHost H A) Z]
    rw [← restrictedHost_lab_eq_dispersal (restrictedHost H A) Z]
    apply (prepared_commonNbrCond_iff _ _ _).mp
    convert (hgeom Z hZ).1 using 1 <;> ring
  · intro Z hZ
    rw [← restrictedHost_G_eq_dispersal (restrictedHost H A) Z]
    rw [← restrictedHost_lab_eq_dispersal (restrictedHost H A) Z]
    apply (prepared_hingeCond_iff _ _ _ _).mp
    convert (hgeom Z hZ).2 using 1 <;> ring
  · intro Z hZ
    have hZquart : (Z.card : ℝ) ≤ (Fintype.card (Survivors A) : ℝ) / 4 := by
      have := mul_le_mul_of_nonneg_right hβquarter
        (show (0 : ℝ) ≤ Fintype.card (Survivors A) by positivity)
      linarith
    have hcardZ := card_survivors_add_card Z
    have hcardZR : (Fintype.card (Survivors Z) : ℝ) + Z.card =
        Fintype.card (Survivors A) := by
      simp only [← Nat.card_eq_fintype_card] at hcardZ ⊢
      exact_mod_cast hcardZ
    have hlarge : 4 * N + 1 ≤ n := (le_max_right _ _).trans hn
    have hlargeR : (4 : ℝ) * N + 1 ≤ n := by exact_mod_cast hlarge
    have horder : (N : ℝ) ≤ Fintype.card (Survivors Z) := by linarith
    have horderN : N ≤ Fintype.card (Survivors Z) := by exact_mod_cast horder
    simpa only [← Nat.card_eq_fintype_card] using horderN
  · intro Z hZ y hy hz
    have hzN : Z.card ≤ b := by
      apply Nat.le_floor
      exact hZ.trans (mul_le_mul_of_nonneg_left hnA hβ.le)
    exact induced_lattice_persistence H F A b hp Z hzN hy hz

/-- The original prepared-core interface, obtained by forgetting the retained geometry. -/
theorem preparedCore_of_H3H4 (α : ℝ) (h N : ℕ) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab
            F (α / 4) h N β := by
  obtain ⟨β, hβ, n₀, hcore⟩ := preparedCore_with_geometry_of_H3H4 α h N hα
  refine ⟨β, hβ, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨A, hA, _, _, hpc⟩ := hcore H F hn hH3 hH4
  exact ⟨A, hA, hpc⟩

end TypedTriangle
