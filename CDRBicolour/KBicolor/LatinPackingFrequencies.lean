/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.LatinPackingGeometry
public import CDRBicolour.KBicolor.LatinPaschConfigurationSplit

/-! # Exact frequencies of the one- and two-block mixed Pasch events -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

theorem placed_overlap_one {i j q i' j' q' : Fin m}
    (ho : ((placedTriangle r c s i j q) ∩ (placedTriangle r c s i' j' q')).card = 1) :
    (i=i' ∧ j ≠ j' ∧ q ≠ q') ∨ (j=j' ∧ i ≠ i' ∧ q ≠ q') ∨
      (q=q' ∧ i ≠ i' ∧ j ≠ j') := by
  have hsmall : ∀ a b : Fin n, a ≠ b →
      a ∈ placedTriangle r c s i j q → b ∈ placedTriangle r c s i j q →
      a ∈ placedTriangle r c s i' j' q' → b ∈ placedTriangle r c s i' j' q' → False := by
    intro a b hab ha hb ha' hb'
    have hh := card_le_card (insert_subset_iff.mpr ⟨mem_inter.mpr ⟨ha,ha'⟩,
      singleton_subset_iff.mpr (mem_inter.mpr ⟨hb,hb'⟩)⟩)
    have hc : ({a,b} : Finset (Fin n)).card = 2 := by simp [hab]
    omega
  have hij : ¬ (i=i' ∧ j=j') := by
    rintro ⟨rfl,rfl⟩
    exact hsmall _ _ (h.rc i j) (by simp [placedTriangle]) (by simp [placedTriangle])
      (by simp [placedTriangle]) (by simp [placedTriangle])
  have hiq : ¬ (i=i' ∧ q=q') := by
    rintro ⟨rfl,rfl⟩
    exact hsmall _ _ (h.rs i q) (by simp [placedTriangle]) (by simp [placedTriangle])
      (by simp [placedTriangle]) (by simp [placedTriangle])
  have hjq : ¬ (j=j' ∧ q=q') := by
    rintro ⟨rfl,rfl⟩
    exact hsmall _ _ (h.cs j q) (by simp [placedTriangle]) (by simp [placedTriangle])
      (by simp [placedTriangle]) (by simp [placedTriangle])
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < #((placedTriangle r c s i j q) ∩
      placedTriangle r c s i' j' q') by rw [ho]; norm_num)
  rcases vtypeK h (mem_inter.mp hv).1 (mem_inter.mp hv).2 with ⟨_,hi⟩ | ⟨_,hj⟩ | ⟨_,hq⟩
  · exact Or.inl ⟨hi, fun hj => hij ⟨hi,hj⟩, fun hq => hiq ⟨hi,hq⟩⟩
  · exact Or.inr (Or.inl ⟨hj, fun hi => hij ⟨hi,hj⟩, fun hq => hjq ⟨hj,hq⟩⟩)
  · exact Or.inr (Or.inr ⟨hq, fun hi => hiq ⟨hi,hq⟩, fun hj => hjq ⟨hj,hq⟩⟩)

theorem packing_single_frequency (l : Fin m → Fin m → Fin m) {T : Finset (Fin n)}
    (hT : T ∈ latinUniverse r c s) :
    (m : ℝ) * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      if T ∈ latPackK r c s (isotopyValue l ρ σ) then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2 := by
  obtain ⟨⟨i,j,q⟩, _, rfl⟩ := mem_image.mp hT
  simp_rw [placedTriangle_mem_packing h]
  simpa only [Fintype.card_fin] using isotopy_single_frequency l i j q

theorem packing_pair_frequency (l : Fin m → Fin m → Fin m) (hl : _root_.STS.IsLatin l)
    {T U : Finset (Fin n)} (hT : T ∈ latinUniverse r c s) (hU : U ∈ latinUniverse r c s)
    (ho : (T ∩ U).card = 1) :
    (m*(m-1) : ℕ) * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      if T ∈ latPackK r c s (isotopyValue l ρ σ) ∧
        U ∈ latPackK r c s (isotopyValue l ρ σ) then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2 := by
  obtain ⟨⟨i,j,q⟩, _, rfl⟩ := mem_image.mp hT
  obtain ⟨⟨i',j',q'⟩, _, rfl⟩ := mem_image.mp hU
  simp_rw [placedTriangle_mem_packing h]
  rcases placed_overlap_one h ho with ⟨rfl,hj,hq⟩ | ⟨rfl,hi,hq⟩ | ⟨rfl,hi,hj⟩
  · simpa only [Fintype.card_fin] using
      isotopy_shared_row_frequency l (fun a => (hl.1 a).1) i j j' q q' hj hq
  · simpa only [Fintype.card_fin] using
      isotopy_shared_column_frequency l (fun b => (hl.2 b).1) i i' j q q' hi hq
  · simpa only [Fintype.card_fin] using
      isotopy_shared_symbol_frequency l (fun a => (hl.1 a).1) hl.2 i i' j j' q hi hj

omit h in
theorem subconfiguration_presence_iff (Q R A S : Finset (Finset (Fin n)))
    (hS : S ∈ Pasch.configurations (A ∪ R)) :
    S ∈ Pasch.configurations (Q ∪ R) ↔ S \ R ⊆ Q := by
  obtain ⟨hsub, hcard, hp⟩ := Pasch.mem_configurations.mp hS
  rw [Pasch.mem_configurations]
  constructor
  · rintro ⟨hnew, _, _⟩ T hT
    exact (mem_union.mp (hnew (mem_sdiff.mp hT).1)).resolve_right (mem_sdiff.mp hT).2
  · intro hnew
    refine ⟨?_,hcard,hp⟩
    intro T hT
    by_cases hTR : T ∈ R
    · exact mem_union_right _ hTR
    · exact mem_union_left _ (hnew (mem_sdiff.mpr ⟨hT,hTR⟩))

theorem mixed_single_frequency (l : Fin m → Fin m → Fin m) (R : Finset (Finset (Fin n)))
    {S : Finset (Finset (Fin n))} (hS : S ∈ Pasch.mixedConfigurations (latinUniverse r c s) R 1 ∅) :
    (m : ℝ) * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 1 ∅
        then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2 := by
  obtain ⟨hc, hout, hcard, _⟩ := Pasch.mixedConfigurations_data hS
  obtain ⟨T,hT⟩ := card_eq_one.mp hcard
  have hTU : T ∈ latinUniverse r c s := hout (by rw [hT]; simp)
  have heq : ∀ Q, S ∈ Pasch.mixedConfigurations Q R 1 ∅ ↔ T ∈ Q := by
    intro Q
    simp [Pasch.mixedConfigurations, hcard,
      and_true, subconfiguration_presence_iff Q R _ S hc, hT, singleton_subset_iff]
  simp_rw [heq]
  exact packing_single_frequency h l hTU

theorem mixed_pair_frequency (l : Fin m → Fin m → Fin m) (hl : _root_.STS.IsLatin l)
    (R : Finset (Finset (Fin n))) {S : Finset (Finset (Fin n))}
    (hS : S ∈ Pasch.mixedConfigurations (latinUniverse r c s) R 2 ∅) :
    (m*(m-1) : ℕ) * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 2 ∅
        then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2 := by
  obtain ⟨hc, hout, hcard, _⟩ := Pasch.mixedConfigurations_data hS
  obtain ⟨T,U,hTU,hpair⟩ := card_eq_two.mp hcard
  have hTM : T ∈ S \ R := by rw [hpair]; simp
  have hUM : U ∈ S \ R := by rw [hpair]; simp
  have hp := (Pasch.mem_configurations.mp hc).2.2
  have ho := Pasch.inter_card_eq_one hp (mem_sdiff.mp hTM).1 (mem_sdiff.mp hUM).1 hTU
  have heq : ∀ Q, S ∈ Pasch.mixedConfigurations Q R 2 ∅ ↔ T ∈ Q ∧ U ∈ Q := by
    intro Q
    simp [Pasch.mixedConfigurations, hcard,
      subconfiguration_presence_iff Q R _ S hc, hpair, hTU,
      insert_subset_iff, singleton_subset_iff]
  simp_rw [heq]
  exact packing_pair_frequency h l hl (hout hTM) (hout hUM) ho

end CDRBicolour.KBicolor.LatinPasch
