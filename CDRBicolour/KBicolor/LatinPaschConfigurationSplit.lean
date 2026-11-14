/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.PaschPartiteParity
public import RequestProject.TypedTriangle.PaschMixedConfigurationBounds

/-! # The zero/one/two/four split and reusable mixed-configuration bounds -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mixed_zero_eq (Q R : Finset (Finset V)) :
    Pasch.mixedConfigurations Q R 0 ∅ = Pasch.configurations R := by
  ext S
  simp only [Pasch.mixedConfigurations, mem_filter, empty_subset, and_true,
    Pasch.mem_configurations]
  constructor
  · rintro ⟨⟨_, hcard, hp⟩, hz⟩
    exact ⟨sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hz), hcard, hp⟩
  · rintro ⟨hSR, hcard, hp⟩
    exact ⟨⟨hSR.trans subset_union_right, hcard, hp⟩,
      by rw [sdiff_eq_empty_iff_subset.mpr hSR]; simp⟩

theorem mixed_four_eq (Q R : Finset (Finset V)) (hd : Disjoint Q R) :
    Pasch.mixedConfigurations Q R 4 ∅ = Pasch.configurations Q := by
  ext S
  simp only [Pasch.mixedConfigurations, mem_filter, empty_subset, and_true,
    Pasch.mem_configurations]
  constructor
  · rintro ⟨⟨hSU, hcard, hp⟩, hc⟩
    have hinter : S ∩ R = ∅ := card_eq_zero.mp (by
      have hh := card_sdiff_add_card_inter S R
      omega)
    have hSQ : S ⊆ Q := by
      intro T hT
      rcases mem_union.mp (hSU hT) with hQ | hR
      · exact hQ
      · have hh : T ∈ S ∩ R := mem_inter.mpr ⟨hT, hR⟩
        rw [hinter] at hh
        exact False.elim (notMem_empty T hh)
    exact ⟨hSQ, hcard, hp⟩
  · rintro ⟨hSQ, hcard, hp⟩
    have hSR : Disjoint S R := hd.mono_left hSQ
    exact ⟨⟨hSQ.trans subset_union_left, hcard, hp⟩,
      by rw [sdiff_eq_self_of_disjoint hSR, hcard]⟩

theorem mixed_three_eq_empty (part : V → Option (Fin 3)) (Q R : Finset (Finset V))
    (hd : Disjoint Q R) (hR : ∀ T ∈ R, ¬ IsPartite part T)
    (hQ : ∀ T ∈ Q, IsPartite part T) : Pasch.mixedConfigurations Q R 3 ∅ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hconf, _, hc, _⟩ := Pasch.mixedConfigurations_data hS
  obtain ⟨hSU, _, hp⟩ := Pasch.mem_configurations.mp hconf
  have heq : S \ R = S ∩ Q := by
    ext T
    simp only [mem_sdiff, mem_inter]
    constructor
    · rintro ⟨hT, hn⟩
      exact ⟨hT, (mem_union.mp (hSU hT)).resolve_right hn⟩
    · rintro ⟨hT, hTQ⟩
      exact ⟨hT, fun hTR => disjoint_left.mp hd hTQ hTR⟩
  apply no_three_partite_blocks part R Q hR hQ hp
    (by simpa only [union_comm] using hSU)
  rwa [← heq]

theorem count_union_four_terms (part : V → Option (Fin 3)) (Q R : Finset (Finset V))
    (hd : Disjoint Q R) (hR : ∀ T ∈ R, ¬ IsPartite part T)
    (hQ : ∀ T ∈ Q, IsPartite part T) :
    Pasch.count (Q ∪ R) = Pasch.count R + Pasch.count Q +
      #(Pasch.mixedConfigurations Q R 1 ∅) + #(Pasch.mixedConfigurations Q R 2 ∅) := by
  let C := Pasch.configurations (Q ∪ R)
  let J : Finset ℕ := {0, 1, 2, 3, 4}
  have hmap : ∀ S ∈ C, (S \ R).card ∈ J := by
    intro S hS
    have hc := (Pasch.mem_configurations.mp hS).2.1
    have hh : (S \ R).card ≤ S.card := card_le_card sdiff_subset
    simp only [J, mem_insert, mem_singleton]
    omega
  have hsum := card_eq_sum_card_fiberwise hmap
  have hfibre : ∀ j, C.filter (fun S => (S \ R).card = j) =
      Pasch.mixedConfigurations Q R j ∅ := by
    intro j
    ext S
    simp only [C, Pasch.mixedConfigurations, mem_filter, empty_subset, and_true]
  simp_rw [hfibre] at hsum
  simp [J] at hsum
  rw [mixed_three_eq_empty part Q R hd hR hQ, mixed_zero_eq,
    mixed_four_eq Q R hd] at hsum
  simpa [C, Pasch.count, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum

theorem mixed_candidate_bounds (Q R : Finset (Finset V))
    (hR : Pasch.PairCodegreeBound R 1) (htrip : ∀ T ∈ R, T.card = 3)
    (hcard : R.card ≤ (Fintype.card V)^2) :
    #(Pasch.mixedConfigurations Q R 1 ∅) ≤ 27*(Fintype.card V)^3 ∧
      #(Pasch.mixedConfigurations Q R 2 ∅) ≤ 6*(Fintype.card V)^4 := by
  constructor
  · have hh := Pasch.mixedConfigurations_one_card_le Q R ∅ 1 hR htrip
    calc
      _ ≤ 27*Fintype.card V*1^2*R.card := hh
      _ ≤ 27*Fintype.card V*1^2*(Fintype.card V)^2 := Nat.mul_le_mul_left _ hcard
      _ = _ := by ring
  · have hh := Pasch.mixedConfigurations_two_card_le Q R ∅ 1 hR htrip
    calc
      _ ≤ 6*(Fintype.card V)^2*1*R.card := hh
      _ ≤ 6*(Fintype.card V)^2*1*(Fintype.card V)^2 := Nat.mul_le_mul_left _ hcard
      _ = _ := by ring

end CDRBicolour.KBicolor.LatinPasch
