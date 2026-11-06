module
public import RequestProject.TypedTriangle.ExplicitMonitorCore
public import RequestProject.TypedTriangle.ExplicitIntLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V34.Explicit
open S07V32 S07V37 S07V37.Explicit TypedTriangle.GroupingExplicit

theorem zero_monitor_word_bound (d R : ℕ) (S D C : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ))
    (hD : ∀ s ∈ D, ∀ j, |s j| ≤ (R : ℤ))
    (hC : ∀ c ∈ C, ∀ j, |c j| ≤ (R : ℤ))
    (ψ : Qt S ⧸ Hgrp S D →+ (Fin (monitorDimension d R) → ℤ))
    (hker : (ψ.ker : Set (Qt S ⧸ Hgrp S D)).Finite)
    (hM : ∀ c ∈ C, l1 (ψ (canonicalMap S D c)) ≤ (monitorMagnitude d R : ℤ))
    (a : C → ℤ) (ha : ψ (wordMap (fun c : C => canonicalMap S D c.val) a) = 0) :
    ∃ b : C → ℤ,
      wordMap (fun c : C => canonicalMap S D c.val) b =
        wordMap (fun c : C => canonicalMap S D c.val) a ∧
      l1c b ≤ ((relationCount d R * relationBound d R * paymentExponent d R : ℕ) : ℤ) := by
  let K := monitorDimension d R
  let M := monitorMagnitude d R
  let L := relationBound d R
  let E := paymentExponent d R
  let g : C → Qt S ⧸ Hgrp S D := fun c => canonicalMap S D c.val
  let A : C → Fin K → ℤ := fun c => ψ (g c)
  have hA : ∀ c j, |A c j| ≤ (M : ℤ) := by
    intro c j
    exact (single_le_sum (fun i _ => abs_nonneg (A c i)) (mem_univ j)).trans
      (hM c.val c.property)
  obtain ⟨Z, hZcard, hZnorm, hZspan⟩ := presentation_uniform_explicit M A hA ∅ (by simp)
  simp only [Finset.coe_empty] at hZspan
  have hCZ : Fintype.card ↥C ≤ boxSize d R := by
    rw [Fintype.card_coe]
    calc
      C.card ≤ (TypedTriangle.QuotientBox.box d R).card := card_le_card (fun c hc =>
        TypedTriangle.QuotientBox.mem_box.mpr (hC c hc))
      _ = boxSize d R := TypedTriangle.QuotientBox.card_box d R
  have hZcount : Z.card ≤ relationCount d R := by
    have hz : Z.card ≤ (2 * L + 1) ^ Fintype.card ↥C := hZcard
    have hp := Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le (2 * L))) hCZ
    exact hz.trans hp
  have hZL : ∀ z ∈ Z, l1c z ≤ (L : ℤ) := hZnorm
  have hPres : a ∈ presMod A (∅ : Set (Fin K → ℤ)) := by
    apply mem_presMod.mpr
    simp only [span_empty, mem_bot]
    change wordMap A a = 0
    rw [← map_wordMap ψ g a]
    exact ha
  have hSpan : a ∈ span ℤ (Z : Set (C → ℤ)) := by rw [hZspan]; exact hPres
  obtain ⟨t, ht⟩ := Submodule.mem_span_finset'.mp hSpan
  have hKill (r : Z) : (E : ℤ) • wordMap g r.val = 0 := by
    have hp : r.val ∈ presMod A (∅ : Set (Fin K → ℤ)) := by
      rw [← hZspan]
      exact subset_span r.property
    have hz : wordMap A r.val = 0 := by
      change (∑ c : C, r.val c • A c) = 0
      simpa only [span_empty, mem_bot] using (mem_presMod.mp hp)
    let v := wordMap (Subtype.val : C → Fin d → ℤ) r.val
    have hv : ∀ j, |v j| ≤ ((R * L : ℕ) : ℤ) :=
      wordMap_box_bound (κ := ↥C) (d := d) (R := R) (L := L)
        (Subtype.val : C → Fin d → ℤ) (fun c j => hC c.val c.property j)
        r.val (hZL r.val r.property)
    have hcan : canonicalMap S D v = wordMap g r.val := by
      change canonicalMap S D (∑ c : C, r.val c • c.val) = ∑ c : C, r.val c • g c
      rw [map_sum]
      simp only [map_zsmul]
      rfl
    have hzero : ψ (canonicalMap S D v) = 0 := by
      rw [hcan, map_wordMap ψ g r.val]
      exact hz
    have he := bounded_kernel_class_annihilated d (R * L) R S D hS hD ψ hker v hv hzero
    change (E : ℤ) • canonicalMap S D v = 0 at he
    simpa only [hcan] using he
  have hE : 0 < E := Nat.factorial_pos _
  have hEInt : (0 : ℤ) < E := by exact_mod_cast hE
  let t' : Z → ℤ := fun r => t r % (E : ℤ)
  have ht' : ∀ r, |t' r| ≤ (E : ℤ) := by
    intro r
    have hp : 0 ≤ t' r := Int.emod_nonneg _ (ne_of_gt hEInt)
    rw [abs_of_nonneg hp]
    exact (Int.emod_lt_of_pos _ hEInt).le
  let b : C → ℤ := ∑ r : Z, t' r • r.val
  have hword : wordMap g b = wordMap g a := by
    rw [← ht]
    change wordMap g (∑ r : Z, t' r • r.val) = wordMap g (∑ r : Z, t r • r.val)
    rw [map_sum, map_sum]
    simp only [map_smul]
    apply sum_congr rfl
    intro r _
    let w : Qt S ⧸ Hgrp S D := wordMap g r.val
    change t' r • w = t r • w
    symm
    calc
      t r • w = (t' r + (E : ℤ) * (t r / (E : ℤ))) • w := by
        rw [show t' r + (E : ℤ) * (t r / (E : ℤ)) = t r from Int.emod_add_mul_ediv _ _]
      _ = t' r • w + (t r / (E : ℤ)) • ((E : ℤ) • w) := by
        calc
          (t' r + (E : ℤ) * (t r / (E : ℤ))) • w =
              t' r • w + ((E : ℤ) * (t r / (E : ℤ))) • w := add_zsmul w _ _
          _ = t' r • w + (t r / (E : ℤ)) • ((E : ℤ) • w) := by
            congr 1
            rw [Int.mul_comm]
            exact mul_zsmul w _ _
      _ = t' r • w := by
        rw [show (E : ℤ) • w = 0 from hKill r, zsmul_zero]
        first
        | exact @add_zero (Qt S ⧸ Hgrp S D)
            (QuotientAddGroup.Quotient.addGroup (Hgrp S D)).toAddZeroClass _
        | exact @add_zero (Qt S ⧸ Hgrp S D)
            (QuotientAddGroup.Quotient.addCommGroup (Hgrp S D)).toAddZeroClass _
  refine ⟨b, hword, (coefficient_norm_sum_bound Z t' E L ht' hZL).trans ?_⟩
  have hc : Z.card * E * L ≤ relationCount d R * L * E := by
    calc
      Z.card * E * L = Z.card * (L * E) := by ring
      _ ≤ relationCount d R * (L * E) := Nat.mul_le_mul_right _ hZcount
      _ = relationCount d R * L * E := by ring
  exact_mod_cast hc

#print axioms zero_monitor_word_bound
end S07V34.Explicit

namespace S07V34.Explicit
open S07V32 S07V37 TypedTriangle.IntLiftExplicit

theorem bounded_monitor_payment (d R : ℕ) (S D C : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ))
    (hD : ∀ s ∈ D, ∀ j, |s j| ≤ (R : ℤ))
    (hC : ∀ c ∈ C, ∀ j, |c j| ≤ (R : ℤ))
    (ψ : Qt S ⧸ Hgrp S D →+ (Fin (monitorDimension d R) → ℤ))
    (hker : (ψ.ker : Set (Qt S ⧸ Hgrp S D)).Finite)
    (hM : ∀ c ∈ C, l1 (ψ (canonicalMap S D c)) ≤ (monitorMagnitude d R : ℤ))
    (x : Qt S) (hx : x ∈ Kgrp S C) :
    ∃ z : C → ℤ, x + ∑ c : C, z c • qmk S c.val ∈ Hgrp S D ∧
      l1c z ≤ (paymentCost d R : ℤ) * (1 + l1 (ψ (x : Qt S ⧸ Hgrp S D))) := by
  let K := monitorDimension d R
  let M := monitorMagnitude d R
  let L := relationBound d R
  let U := relationCount d R * relationBound d R * paymentExponent d R
  let p := QuotientAddGroup.mk' (Hgrp S D)
  let g : C → Qt S ⧸ Hgrp S D := fun c => canonicalMap S D c.val
  let A : C → Fin K → ℤ := fun c => ψ (g c)
  have hA : ∀ c j, |A c j| ≤ (M : ℤ) := by
    intro c j
    exact (single_le_sum (fun i _ => abs_nonneg (A c i)) (mem_univ j)).trans
      (hM c.val c.property)
  obtain ⟨a, ha⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.mp
    ((Kgrp_eq_closure_range S C) ▸ hx)
  have hword : wordMap g a = p x := by
    rw [ha, map_sum]
    simp only [map_zsmul]
    rfl
  have hImage : wordMap A a = ψ (p x) := by
    rw [← map_wordMap ψ g a, hword]
  have hSpan : ψ (p x) ∈ span ℤ (Set.range A) := by
    rw [← hImage]
    apply Submodule.sum_mem
    intro c _
    exact Submodule.smul_mem _ _ (subset_span (Set.mem_range_self c))
  obtain ⟨u, hu, huNorm⟩ := int_lift_uniform_explicit K M A hA (ψ (p x)) hSpan
  change wordMap A u = ψ (p x) at hu
  have hMpos : 1 ≤ M := le_max_left _ _
  rw [max_eq_right hMpos] at huNorm
  have hUNorm : l1c u ≤ (L : ℤ) * l1 (ψ (p x)) := huNorm
  have hzero : ψ (wordMap g (a - u)) = 0 := by
    rw [map_wordMap ψ g (a - u)]
    change wordMap A (a - u) = 0
    rw [map_sub, hImage, hu, sub_self]
  obtain ⟨b, hb, hbNorm⟩ := zero_monitor_word_bound d R S D C hS hD hC ψ hker hM (a - u) hzero
  have hTotal : wordMap g (u + b) = p x := by
    rw [map_add, hb, map_sub, hword]
    abel
  refine ⟨-(u + b), ?_, ?_⟩
  · apply (QuotientAddGroup.eq_zero_iff _).mp
    change p (x + wordMap (fun c : C => qmk S c.val) (-(u + b))) = 0
    have hpword : p (wordMap (fun c : C => qmk S c.val) (-(u + b))) =
        wordMap g (-(u + b)) := by
      change p (∑ c : C, (-(u + b)) c • qmk S c.val) = ∑ c : C, (-(u + b)) c • g c
      rw [map_sum]
      simp only [map_zsmul]
      rfl
    rw [map_add, hpword]
    change p x + wordMap g (-(u + b)) = 0
    rw [map_neg, hTotal, add_neg_cancel]
  · change l1c (-(u + b)) ≤ ((L + U : ℕ) : ℤ) * (1 + l1 (ψ (p x)))
    have hPsi : 0 ≤ l1 (ψ (p x)) := l1_nonneg _
    have hU : (0 : ℤ) ≤ U := by positivity
    calc
      l1c (-(u + b)) = ∑ c : C, |u c + b c| := by
        simp only [l1c, Pi.neg_apply, Pi.add_apply, abs_neg]
      _ ≤ ∑ c : C, (|u c| + |b c|) := sum_le_sum (fun c _ => abs_add_le _ _)
      _ = l1c u + l1c b := sum_add_distrib
      _ ≤ (L : ℤ) * l1 (ψ (p x)) + (U : ℤ) := add_le_add hUNorm hbNorm
      _ ≤ ((L + U : ℕ) : ℤ) * (1 + l1 (ψ (p x))) := by
        push_cast
        nlinarith only [mul_nonneg hU hPsi, show (0 : ℤ) ≤ L by positivity]

#print axioms bounded_monitor_payment
end S07V34.Explicit

namespace S07V34.Explicit
open S07V32 S07V37

theorem uniform_monitor_payment_kmax_explicit (d R : ℕ) :
    ∀ S D : Finset (Fin d → ℤ), S ⊆ box d R → D ⊆ box d R →
      ∃ ψ : Qt S ⧸ Hgrp S D →+ (Fin (monitorDimension d R) → ℤ),
        (ψ.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b ∈ box d R, l1 (ψ ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ monitorMagnitude d R) ∧
        ∀ C : Finset (Fin d → ℤ), C ⊆ box d R → ∀ x ∈ Kgrp S C,
          ∃ z : (Fin d → ℤ) → ℤ, (∀ b, b ∉ C → z b = 0) ∧
            x + ∑ b ∈ box d R, z b • qmk S b ∈ Hgrp S D ∧
            ∑ b ∈ box d R, |z b| ≤ (paymentCost d R : ℤ) * (1 + l1 (ψ (x : Qt S ⧸ Hgrp S D))) := by
  intro S D hS hD
  have hs : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ) := fun s hs => mem_box.mp (hS hs)
  have hd : ∀ s ∈ D, ∀ j, |s j| ≤ (R : ℤ) := fun s hs => mem_box.mp (hD hs)
  obtain ⟨ψ, hker, hM⟩ := bounded_monitor_exists d R S D hs hd
  refine ⟨ψ, hker, (fun b hb => hM b (mem_box.mp hb)), ?_⟩
  intro C hC x hx
  obtain ⟨z, hz, hb⟩ := bounded_monitor_payment d R S D C hs hd
    (fun c hc => mem_box.mp (hC hc)) ψ hker (fun c hc => hM c (mem_box.mp (hC hc))) x hx
  let w : (Fin d → ℤ) → ℤ := fun b => if h : b ∈ C then z ⟨b, h⟩ else 0
  have hsum : ∀ f : ℤ → Qt S → Qt S, (∀ q, f 0 q = 0) →
      ∑ b ∈ box d R, f (w b) (qmk S b) = ∑ c : C, f (z c) (qmk S c) := by
    intro f hf0
    rw [← sum_subset hC (fun b _ hbC => by simp [w, hbC, hf0]), ← sum_coe_sort C]
    exact sum_congr rfl fun c _ => by simp [w, c.2]
  refine ⟨w, (fun b hb => by simp [w, hb]), ?_, ?_⟩
  · rw [hsum (fun a q => a • q) (fun q => zero_smul ℤ q)]
    exact hz
  · have hh : ∑ b ∈ box d R, |w b| = ∑ c : C, |z c| := by
      rw [← sum_subset hC (fun b _ hbC => by simp [w, hbC]), ← sum_coe_sort C]
      exact sum_congr rfl fun c _ => by simp [w, c.2]
    rw [hh]
    exact hb

#print axioms uniform_monitor_payment_kmax_explicit
end S07V34.Explicit
