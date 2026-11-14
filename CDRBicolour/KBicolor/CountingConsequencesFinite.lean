/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Completion
public import Mathlib.Data.Fintype.Perm

/-! # Finite counting losses under isomorphism and exact type statistics

Uncoloured isomorphism classes are represented by their full permutation
orbits, even when only part of an orbit respects the fixed labelling.
Exact type vectors contain only off-diagonal ordered colour pairs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor
open Finset
variable {n k : ℕ}

/-- Relabel a block family, without imposing any colour preservation. -/
def relabelBlocks (e : Equiv.Perm (Fin n)) (D : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) := D.image (fun T => T.image e)

/-- The entire uncoloured isomorphism orbit of a block family. -/
def blockOrbit (D : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  univ.image (fun e : Equiv.Perm (Fin n) => relabelBlocks e D)

theorem self_mem_blockOrbit (D : Finset (Finset (Fin n))) : D ∈ blockOrbit D := by
  classical
  exact mem_image.mpr ⟨Equiv.refl _, mem_univ _, by simp [relabelBlocks]⟩

theorem blockOrbit_relabel (e : Equiv.Perm (Fin n)) (D : Finset (Finset (Fin n))) :
    blockOrbit (relabelBlocks e D) = blockOrbit D := by
  classical
  ext E
  simp only [blockOrbit, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨e.trans f, by simp [relabelBlocks, image_image, Function.comp_def]⟩
  · rintro ⟨f, rfl⟩
    exact ⟨e.symm.trans f, by simp [relabelBlocks, image_image, Function.comp_def]⟩

/-- Equality of the orbit representatives is precisely uncoloured isomorphism. -/
theorem blockOrbit_eq_iff (D E : Finset (Finset (Fin n))) :
    blockOrbit D = blockOrbit E ↔ ∃ e : Equiv.Perm (Fin n), relabelBlocks e D = E := by
  classical
  constructor
  · intro h
    have hm := self_mem_blockOrbit E
    rw [← h] at hm
    simpa only [blockOrbit, mem_image, mem_univ, true_and] using hm
  · rintro ⟨e, rfl⟩
    exact (blockOrbit_relabel e D).symm

theorem card_blockOrbit_le (D : Finset (Finset (Fin n))) : #(blockOrbit D) ≤ n.factorial := by
  classical
  simpa only [blockOrbit, card_univ, Fintype.card_perm, Fintype.card_fin] using
    (card_image_le (s := (univ : Finset (Equiv.Perm (Fin n))))
      (f := fun e => relabelBlocks e D))

/-- Number of uncoloured isomorphism classes represented by the fixed partition. -/
def kIsoCount (lab : Fin n → Fin k) : ℕ := #((kBlocks lab).image blockOrbit)

theorem kIsoCount_le (lab : Fin n → Fin k) : kIsoCount lab ≤ kCount lab := by
  classical
  exact card_image_le

theorem kCount_le_factorial_mul_iso (lab : Fin n → Fin k) :
    kCount lab ≤ n.factorial * kIsoCount lab := by
  classical
  apply card_le_mul_card_image (f := blockOrbit) (kBlocks lab) n.factorial
  intro O hO
  obtain ⟨D, _, rfl⟩ := mem_image.mp hO
  refine (card_le_card ?_).trans (card_blockOrbit_le D)
  intro E hE
  have h := self_mem_blockOrbit E
  rw [(mem_filter.mp hE).2] at h
  exact h

/-- Off-diagonal ordered pairs of colours, the coordinates of an exact type matrix. -/
abbrev TypeCoord (k : ℕ) := ↥((univ : Finset (Fin k)).offDiag)

theorem card_typeCoord (k : ℕ) : Fintype.card (TypeCoord k) = k * (k - 1) := by
  change Fintype.card ↥((univ : Finset (Fin k)).offDiag) = _
  rw [Fintype.card_coe, offDiag_card, card_univ, Fintype.card_fin]
  simp [Nat.mul_sub_left_distrib]

def typeVector (lab : Fin n → Fin k) (D : Finset (Finset (Fin n))) : TypeCoord k → ℕ :=
  fun p => kTypeCount lab D p.1.1 p.1.2

def exactTypeFibre (lab : Fin n → Fin k) (t : TypeCoord k → ℕ) :
    Finset (Finset (Finset (Fin n))) := (kBlocks lab).filter (fun D => typeVector lab D = t)

def exactTypeCount (lab : Fin n → Fin k) (t : TypeCoord k → ℕ) : ℕ := #(exactTypeFibre lab t)

def possibleTypeVectors (n k : ℕ) : Finset (TypeCoord k → ℕ) :=
  Fintype.piFinset (fun _ => range (n ^ 2 + 1))

theorem typeVector_mem_possible (lab : Fin n → Fin k) {D : Finset (Finset (Fin n))}
    (hD : D ∈ kBlocks lab) : typeVector lab D ∈ possibleTypeVectors n k := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro p
  have hsts : _root_.STS.IsSTS D := (mem_filter.mp hD).2.1
  have hle : kTypeCount lab D p.1.1 p.1.2 ≤ n ^ 2 :=
    (card_filter_le D _).trans (card_sts_le_sq hsts)
  exact mem_range.mpr (Nat.lt_succ_of_le hle)

theorem card_possibleTypeVectors (n k : ℕ) :
    #(possibleTypeVectors n k) = (n ^ 2 + 1) ^ (k * (k - 1)) := by
  rw [possibleTypeVectors, Fintype.card_piFinset]
  simp only [card_range, prod_const, card_univ, card_typeCoord]

theorem exactTypeCount_le (lab : Fin n → Fin k) (t : TypeCoord k → ℕ) :
    exactTypeCount lab t ≤ kCount lab := by
  classical
  exact card_filter_le _ _

/-- A maximum realised fibre loses at most the number of possible type vectors. -/
theorem exists_large_exactTypeFibre (lab : Fin n → Fin k) (hN : 0 < kCount lab) :
    ∃ t : TypeCoord k → ℕ, (∃ D ∈ kBlocks lab, typeVector lab D = t) ∧
      0 < exactTypeCount lab t ∧
      kCount lab ≤ (n ^ 2 + 1) ^ (k * (k - 1)) * exactTypeCount lab t := by
  classical
  have hne : (kBlocks lab).Nonempty := card_pos.mp hN
  obtain ⟨t, ht, hmax⟩ := ((kBlocks lab).image (typeVector lab)).exists_max_image
    (exactTypeCount lab) (hne.image _)
  obtain ⟨D, hD, hDt⟩ := mem_image.mp ht
  have hpos : 0 < exactTypeCount lab t :=
    card_pos.mpr ⟨D, mem_filter.mpr ⟨hD, hDt⟩⟩
  have hcard : #((kBlocks lab).image (typeVector lab)) ≤ (n ^ 2 + 1) ^ (k * (k - 1)) := by
    rw [← card_possibleTypeVectors]
    apply card_le_card
    intro s hs
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hs
    exact typeVector_mem_possible lab hE
  refine ⟨t, ⟨D, hD, hDt⟩, hpos, ?_⟩
  have hbound := card_le_mul_card_image (f := typeVector lab) (kBlocks lab)
    (exactTypeCount lab t) (fun s hs => hmax s hs)
  calc
    kCount lab ≤ exactTypeCount lab t * #((kBlocks lab).image (typeVector lab)) := hbound
    _ ≤ exactTypeCount lab t * (n ^ 2 + 1) ^ (k * (k - 1)) :=
      Nat.mul_le_mul_left (exactTypeCount lab t) hcard
    _ = _ := Nat.mul_comm _ _

/-- The exact logarithmic loss associated with a bounded finite fibre. -/
theorem log_count_le_log_factor_add {N B M : ℕ} (hN : 0 < N) (hB : 0 < B)
    (h : N ≤ B * M) : 0 < M ∧ Real.log (N : ℝ) ≤ Real.log (B : ℝ) + Real.log (M : ℝ) := by
  have hM : 0 < M := by
    by_contra hn
    have hz : M = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, mul_zero] at h
    omega
  refine ⟨hM, ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hh : (N : ℝ) ≤ (B : ℝ) * M := by exact_mod_cast h
  simpa only [Real.log_mul hBR.ne' hMR.ne'] using Real.log_le_log hNR hh

end CDRBicolour.KBicolor
