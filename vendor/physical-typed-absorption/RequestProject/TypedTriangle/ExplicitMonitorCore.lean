module
public import RequestProject.TypedTriangle.GroupingExplicitBound
public import RequestProject.S07V34.Uniform
public import RequestProject.TypedTriangle.ExplicitFinitePresentation
public import RequestProject.S07V44.Padding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace S07V34.Explicit
open TypedTriangle.Grouping TypedTriangle.QuotientBox

def torsionExponent (d B R : ℕ) : ℕ := (explicitGroupBound d B R).factorial

/-- A bounded vector that is torsion modulo the exact lattice has a
    positive annihilating multiple bounded by the explicit grouping constant. -/
theorem small_multiple_mem_span (d B R : ℕ) (S : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ)) (x : Fin d → ℤ)
    (hx : ∀ j, |x j| ≤ (B : ℤ))
    (n : ℕ) (hn : 0 < n) (hmem : (n : ℤ) • x ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ k : ℕ, 0 < k ∧ k ≤ explicitGroupBound d B R ∧
      (k : ℤ) • x ∈ span ℤ (S : Set (Fin d → ℤ)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨P, hP⟩ := uniform_grouping_numerical d B R
    (span ℤ (S : Set (Fin d → ℤ))) (S : Set (Fin d → ℤ)) rfl hS
    (fun _ : Fin n => x) (fun _ j => hx j) (by
      simpa only [sum_const, card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul] using hmem)
  obtain ⟨J, hJ⟩ := P.parts_nonempty (show (univ : Finset (Fin n)) ≠ ⊥ from univ_nonempty.ne_empty)
  have hJne : J ≠ ∅ := by
    intro he
    exact P.ne_bot hJ he
  refine ⟨J.card, card_pos.mpr (nonempty_iff_ne_empty.mpr hJne), (hP J hJ).1, ?_⟩
  simpa only [sum_const, Nat.cast_smul_eq_nsmul] using (hP J hJ).2

/-- One specified factorial annihilates every bounded torsion vector;
    this needs no numerical choice of a torsion basis or Smith form. -/
theorem factorial_multiple_mem_span (d B R : ℕ) (S : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ)) (x : Fin d → ℤ)
    (hx : ∀ j, |x j| ≤ (B : ℤ))
    (ht : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • x ∈ span ℤ (S : Set (Fin d → ℤ))) :
    (torsionExponent d B R : ℤ) • x ∈ span ℤ (S : Set (Fin d → ℤ)) := by
  obtain ⟨n, hn, hm⟩ := ht
  obtain ⟨k, hk, hkle, hkmem⟩ := small_multiple_mem_span d B R S hS x hx n hn hm
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hk hkle
  have h := Submodule.smul_mem (span ℤ (S : Set (Fin d → ℤ))) (r : ℤ) hkmem
  rw [smul_smul, mul_comm] at h
  simpa only [torsionExponent, hr, Nat.cast_mul] using h

#print axioms small_multiple_mem_span
#print axioms factorial_multiple_mem_span
end S07V34.Explicit

open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace S07V34.Explicit

theorem mem_closure_int_iff {A : Type*} [AddCommGroup A] (S : Set A) (x : A) :
    x ∈ AddSubgroup.closure S ↔ x ∈ span ℤ S := by
  have h₁ : AddSubgroup.closure S ≤ (span ℤ S).toAddSubgroup :=
    (AddSubgroup.closure_le _).mpr (fun _ hx => subset_span hx)
  have h₂ : span ℤ S ≤ (AddSubgroup.closure S).toIntSubmodule :=
    Submodule.span_le.mpr (fun _ hx => AddSubgroup.subset_closure hx)
  exact ⟨fun hx => h₁ hx, fun hx => h₂ hx⟩

def canonicalMap {d : ℕ} (S D : Finset (Fin d → ℤ)) :
    (Fin d → ℤ) →+ (Qt S ⧸ Hgrp S D) :=
  (QuotientAddGroup.mk' (Hgrp S D)).comp
    (QuotientAddGroup.mk' (AddSubgroup.closure (S : Set (Fin d → ℤ))))

theorem canonicalMap_surjective {d : ℕ} (S D : Finset (Fin d → ℤ)) :
    Function.Surjective (canonicalMap S D) :=
  (QuotientAddGroup.mk'_surjective (Hgrp S D)).comp
    (QuotientAddGroup.mk'_surjective (AddSubgroup.closure (S : Set (Fin d → ℤ))))

theorem canonicalMap_eq_zero_iff {d : ℕ} (S D : Finset (Fin d → ℤ)) (x : Fin d → ℤ) :
    canonicalMap S D x = 0 ↔ x ∈ span ℤ ((S ∪ D : Finset _) : Set (Fin d → ℤ)) := by
  let p := QuotientAddGroup.mk' (AddSubgroup.closure (S : Set (Fin d → ℤ)))
  constructor
  · intro hx
    have hp : p x ∈ Hgrp S D := (QuotientAddGroup.eq_zero_iff _).mp hx
    have hmap : Hgrp S D ≤ (AddSubgroup.closure (D : Set (Fin d → ℤ))).map p := by
      apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, AddSubgroup.subset_closure hy, rfl⟩
    obtain ⟨y, hy, hyp⟩ := hmap hp
    have hxy : x - y ∈ AddSubgroup.closure (S : Set (Fin d → ℤ)) := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change p (x - y) = 0
      rw [map_sub, ← hyp, sub_self]
    have hS : AddSubgroup.closure (S : Set (Fin d → ℤ)) ≤
        AddSubgroup.closure ((S ∪ D : Finset _) : Set (Fin d → ℤ)) :=
      AddSubgroup.closure_mono (fun _ ha => mem_union_left _ ha)
    have hD : AddSubgroup.closure (D : Set (Fin d → ℤ)) ≤
        AddSubgroup.closure ((S ∪ D : Finset _) : Set (Fin d → ℤ)) :=
      AddSubgroup.closure_mono (fun _ ha => mem_union_right _ ha)
    apply (mem_closure_int_iff _ _).mp
    simpa only [sub_add_cancel] using
      (AddSubgroup.add_mem _ (hS hxy) (hD hy))
  · intro hx
    have hcl : AddSubgroup.closure ((S ∪ D : Finset _) : Set (Fin d → ℤ)) ≤
        (canonicalMap S D).ker := by
      apply (AddSubgroup.closure_le _).mpr
      intro y hy
      change canonicalMap S D y = 0
      rcases mem_union.mp hy with hy | hy
      · have hp : qmk S y = 0 := (QuotientAddGroup.eq_zero_iff _).mpr
          (AddSubgroup.subset_closure hy)
        change (QuotientAddGroup.mk' (Hgrp S D)) (qmk S y) = 0
        rw [hp, map_zero]
      · apply (QuotientAddGroup.eq_zero_iff _).mpr
        exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
    exact hcl ((mem_closure_int_iff _ _).mpr hx)

#print axioms canonicalMap_eq_zero_iff
end S07V34.Explicit

open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V34.Explicit
open S07V37 S07V37.Explicit TypedTriangle.GroupingExplicit TypedTriangle.QuotientBox

def boxSize (d R : ℕ) : ℕ := (2 * R + 1) ^ d
def dualBound (d R : ℕ) : ℕ := kernelBound (boxSize d R) R
def monitorDimension (d R : ℕ) : ℕ := (2 * dualBound d R + 1) ^ d
def monitorMagnitude (d R : ℕ) : ℕ := max 1 (monitorDimension d R * dualBound d R * R)

def rowMap {d : ℕ} (r : Fin d → ℤ) : (Fin d → ℤ) →+ ℤ where
  toFun v := ∑ i, r i * v i
  map_zero' := by simp
  map_add' v w := by simp [mul_add, sum_add_distrib]

theorem rowMap_add_rows {d : ℕ} (r s v : Fin d → ℤ) :
    rowMap (r + s) v = rowMap r v + rowMap s v := by
  simp [rowMap, add_mul, sum_add_distrib]

theorem rowMap_smul_rows {d : ℕ} (a : ℤ) (r v : Fin d → ℤ) :
    rowMap (a • r) v = a * rowMap r v := by
  simp [rowMap, mul_sum, mul_assoc, smul_eq_mul]

theorem rowMap_bound {d L R : ℕ} (r v : Fin d → ℤ)
    (hr : l1c r ≤ (L : ℤ)) (hv : ∀ i, |v i| ≤ (R : ℤ)) :
    |rowMap r v| ≤ ((L * R : ℕ) : ℤ) := by
  calc
    |rowMap r v| ≤ ∑ i, |r i * v i| := by
      change |∑ i, r i * v i| ≤ ∑ i, |r i * v i|
      exact abs_sum_le_sum_abs _ _
    _ = ∑ i, |r i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, |r i| * (R : ℤ) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
    _ = l1c r * (R : ℤ) := by
      change (∑ i, |r i| * (R : ℤ)) = (∑ i, |r i|) * (R : ℤ)
      rw [sum_mul]
    _ ≤ ((L * R : ℕ) : ℤ) := by
      exact_mod_cast mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg R)

/-- The integer annihilator of any subset of a fixed coordinate box is
    generated by a specified number of rows of specified norm. -/
theorem bounded_annihilator_generators (d R : ℕ) (Γ : Finset (Fin d → ℤ))
    (hΓ : ∀ b ∈ Γ, ∀ j, |b j| ≤ (R : ℤ)) :
    ∃ Z : Finset (Fin d → ℤ), Z.card ≤ monitorDimension d R ∧
      (∀ z ∈ Z, l1c z ≤ (dualBound d R : ℤ)) ∧
      ∀ z : Fin d → ℤ, z ∈ span ℤ (Z : Set (Fin d → ℤ)) ↔
        ∀ b ∈ Γ, rowMap z b = 0 := by
  let B := TypedTriangle.QuotientBox.box d R
  let e := Fintype.equivFin ↥B
  let c : Fin d → Fin (Fintype.card ↥B) → ℤ :=
    fun j i => if (e.symm i).val ∈ Γ then (e.symm i).val j else 0
  have hc : ∀ j i, |c j i| ≤ (R : ℤ) := by
    intro j i
    dsimp only [c]
    split_ifs
    · exact TypedTriangle.QuotientBox.mem_box.mp (e.symm i).property j
    · simp
  obtain ⟨Z, hZcard, hZnorm, hZspan⟩ := presentation_uniform_explicit R c hc ∅ (by simp)
  have hN : Fintype.card ↥B = boxSize d R := by
    simp only [Fintype.card_coe, B, TypedTriangle.QuotientBox.card_box, boxSize]
  have hcard : Z.card ≤ monitorDimension d R := by
    simpa only [presKBound, presLBound, hN, Fintype.card_fin, monitorDimension, dualBound] using hZcard
  have hnorm : ∀ z ∈ Z, l1c z ≤ (dualBound d R : ℤ) := by
    simpa only [presLBound, hN, dualBound] using hZnorm
  have hmem (z : Fin d → ℤ) : z ∈ presMod c (∅ : Set (Fin (Fintype.card ↥B) → ℤ)) ↔
      ∀ b ∈ Γ, rowMap z b = 0 := by
    simp only [mem_presMod, span_empty, mem_bot]
    constructor
    · intro hz b hb
      have hbB : b ∈ B := TypedTriangle.QuotientBox.mem_box.mpr (hΓ b hb)
      let b₀ : B := ⟨b, hbB⟩
      have h := congrFun hz (e b₀)
      simpa [c, b₀, hb, rowMap, smul_eq_mul] using h
    · intro hz
      funext i
      by_cases hi : (e.symm i).val ∈ Γ
      · simpa [c, hi, rowMap, smul_eq_mul] using hz (e.symm i).val hi
      · simp [c, hi]
  refine ⟨Z, hcard, hnorm, ?_⟩
  intro z
  rw [hZspan]
  simpa only [Finset.coe_empty] using hmem z

#print axioms bounded_annihilator_generators
end S07V34.Explicit

open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V34.Explicit
open S07V32 S07V37 S07V44

theorem intHom_eq_row {d : ℕ} (f : (Fin d → ℤ) →+ ℤ) (v : Fin d → ℤ) :
    f v = rowMap (fun i => f (Pi.single i 1)) v := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  change (∑ i, f (Pi.single i (v i))) = ∑ i, f (Pi.single i 1) * v i
  apply sum_congr rfl
  intro i _
  have hs : Pi.single i (v i) = (v i) • (Pi.single i 1 : Fin d → ℤ) := by
    ext j
    by_cases hij : i = j
    · subst j; simp
    · simp [Pi.single_apply, hij]
  rw [hs, map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_id, mul_comm]

/-- Bounded integer rows provide a monitor of specified dimension and
    magnitude. The old FG monitor is used solely to prove kernel finiteness. -/
theorem bounded_monitor_exists (d R : ℕ) (S D : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ))
    (hD : ∀ s ∈ D, ∀ j, |s j| ≤ (R : ℤ)) :
    ∃ ψ : Qt S ⧸ Hgrp S D →+ (Fin (monitorDimension d R) → ℤ),
      (ψ.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
      ∀ b : Fin d → ℤ, (∀ j, |b j| ≤ (R : ℤ)) →
        l1 (ψ (canonicalMap S D b)) ≤ (monitorMagnitude d R : ℤ) := by
  obtain ⟨Z, hZcard, hZnorm, hSpan⟩ := bounded_annihilator_generators d R (S ∪ D) (by
    intro b hb j
    rcases mem_union.mp hb with hb | hb
    · exact hS b hb j
    · exact hD b hb j)
  let k := Fintype.card ↥Z
  let K := monitorDimension d R
  let e := Fintype.equivFin ↥Z
  have hk : k ≤ K := by simpa only [k, K, Fintype.card_coe] using hZcard
  let f : (Fin d → ℤ) →+ (Fin k → ℤ) :=
    { toFun := fun v i => rowMap (e.symm i).val v
      map_zero' := by ext i; exact map_zero _
      map_add' := fun v w => by ext i; exact map_add _ v w }
  have hRows (z : Z) : ∀ b ∈ S ∪ D, rowMap z.val b = 0 :=
    (hSpan z.val).mp (subset_span z.property)
  have hs : AddSubgroup.closure (S : Set (Fin d → ℤ)) ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro b hb
    change f b = 0
    funext i
    exact hRows (e.symm i) b (mem_union_left _ hb)
  let g := QuotientAddGroup.lift _ f hs
  have hd : Hgrp S D ≤ g.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨b, hb, rfl⟩
    change f b = 0
    funext i
    exact hRows (e.symm i) b (mem_union_right _ hb)
  let raw := QuotientAddGroup.lift _ g hd
  let ψ := (padL k K).comp raw
  have hraw (v : Fin d → ℤ) : raw (canonicalMap S D v) = f v := rfl
  have hψ (v : Fin d → ℤ) (i : Fin k) :
      ψ (canonicalMap S D v) (Fin.castLE hk i) = rowMap (e.symm i).val v := by
    change padL k K (raw (canonicalMap S D v)) (Fin.castLE hk i) = _
    rw [padL_apply_castLE, hraw]
    rfl
  obtain ⟨kOld, old, hOld⟩ := exists_int_monitor (Qt S ⧸ Hgrp S D)
  have hContain : ∀ x, ψ x = 0 → old x = 0 := by
    intro x hx
    obtain ⟨v, rfl⟩ := canonicalMap_surjective S D x
    have hZeroRows : ∀ z ∈ Z, rowMap z v = 0 := by
      intro z hz
      let i := e (⟨z, hz⟩ : Z)
      have hh : ψ (canonicalMap S D v) (Fin.castLE hk i) = 0 := congrFun hx _
      simpa only [i, Equiv.symm_apply_apply] using (hψ v i).symm.trans hh
    have hZeroSpan : ∀ r ∈ span ℤ (Z : Set (Fin d → ℤ)), rowMap r v = 0 := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr => exact hZeroRows r hr
      | zero => simp [rowMap]
      | add r s _ _ hr hs => rw [rowMap_add_rows, hr, hs, zero_add]
      | smul a r _ hr => rw [rowMap_smul_rows, hr, mul_zero]
    funext j
    let ℓ : (Fin d → ℤ) →+ ℤ :=
      { toFun := fun w => old (canonicalMap S D w) j
        map_zero' := by simp
        map_add' := fun a b => by simp }
    let r : Fin d → ℤ := fun i => ℓ (Pi.single i 1)
    have hr : r ∈ span ℤ (Z : Set (Fin d → ℤ)) := by
      apply (hSpan r).mpr
      intro b hb
      rw [← intHom_eq_row ℓ b]
      change old (canonicalMap S D b) j = 0
      rw [(canonicalMap_eq_zero_iff S D b).mpr (subset_span hb), map_zero]
      rfl
    change ℓ v = 0
    rw [intHom_eq_row ℓ v]
    exact hZeroSpan r hr
  refine ⟨ψ, hOld.subset (fun x hx => hContain x hx), ?_⟩
  intro b hb
  change l1 (padL k K (raw (canonicalMap S D b))) ≤ _
  rw [l1_padL hk, hraw]
  change (∑ i : Fin k, |rowMap (e.symm i).val b|) ≤ _
  calc
    (∑ i : Fin k, |rowMap (e.symm i).val b|) ≤
        ∑ _i : Fin k, ((dualBound d R * R : ℕ) : ℤ) := by
      apply sum_le_sum
      intro i _
      exact rowMap_bound _ _ (hZnorm _ (e.symm i).property) hb
    _ = ((k * dualBound d R * R : ℕ) : ℤ) := by
      rw [sum_const, card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (monitorMagnitude d R : ℤ) := by
      apply Int.ofNat_le.mpr
      exact (Nat.mul_le_mul_right R (Nat.mul_le_mul_right (dualBound d R) hk)).trans
        (le_max_right _ _)

#print axioms bounded_monitor_exists
end S07V34.Explicit

namespace S07V34.Explicit
open S07V37

def wordMap {κ G : Type} [Fintype κ] [AddCommGroup G] (g : κ → G) :
    (κ → ℤ) →ₗ[ℤ] G where
  toFun a := ∑ i, a i • g i
  map_add' a b := by simp [add_smul, sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum, mul_smul]

theorem map_wordMap {κ G H : Type} [Fintype κ] [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (g : κ → G) (a : κ → ℤ) :
    f (wordMap g a) = wordMap (fun i => f (g i)) a := by
  change f (∑ i, a i • g i) = ∑ i, a i • f (g i)
  rw [map_sum]
  simp only [map_zsmul]

theorem wordMap_box_bound {κ : Type} [Fintype κ] {d R L : ℕ}
    (g : κ → Fin d → ℤ) (hg : ∀ i j, |g i j| ≤ (R : ℤ))
    (a : κ → ℤ) (ha : S07V37.l1c a ≤ (L : ℤ)) :
    ∀ j, |wordMap g a j| ≤ ((R * L : ℕ) : ℤ) := by
  intro j
  change |(∑ i, a i • g i) j| ≤ _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    |∑ i, a i * g i j| ≤ ∑ i, |a i * g i j| := abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |g i j| := by simp only [abs_mul]
    _ ≤ ∑ i, |a i| * (R : ℤ) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg _))
    _ = S07V37.l1c a * (R : ℤ) := by
      change (∑ i, |a i| * (R : ℤ)) = (∑ i, |a i|) * (R : ℤ)
      rw [sum_mul]
    _ ≤ ((R * L : ℕ) : ℤ) := by
      have hh := mul_le_mul_of_nonneg_right ha (show (0 : ℤ) ≤ R by positivity)
      simpa only [Nat.cast_mul, mul_comm] using hh

theorem finite_kernel_positive_multiple {G : Type} [AddCommGroup G] {k : ℕ}
    (ψ : G →+ (Fin k → ℤ)) (hker : (ψ.ker : Set G).Finite) (x : G) (hx : ψ x = 0) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  letI : Finite ψ.ker := hker.to_subtype
  have hn : 0 < Nat.card ψ.ker := Nat.card_pos
  have hh : Nat.card ψ.ker • (⟨x, hx⟩ : ψ.ker) = 0 := card_nsmul_eq_zero'
  exact ⟨Nat.card ψ.ker, hn, congrArg Subtype.val hh⟩

theorem coefficient_norm_sum_bound {κ : Type} [Fintype κ]
    (Z : Finset (κ → ℤ)) (t : Z → ℤ) (E L : ℕ)
    (ht : ∀ z, |t z| ≤ (E : ℤ)) (hZ : ∀ z ∈ Z, l1c z ≤ (L : ℤ)) :
    l1c (∑ z : Z, t z • z.val) ≤ ((Z.card * E * L : ℕ) : ℤ) := by
  calc
    l1c (∑ z : Z, t z • z.val) ≤ ∑ i : κ, ∑ z : Z, |t z| * |z.val i| := by
      apply sum_le_sum
      intro i _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simpa only [abs_mul] using (abs_sum_le_sum_abs (fun z : Z => t z * z.val i) univ)
    _ = ∑ z : Z, |t z| * l1c z.val := by
      rw [sum_comm]
      simp only [l1c, mul_sum]
    _ ≤ ∑ _z : Z, (E : ℤ) * (L : ℤ) := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul (ht z) (hZ _ z.property) (l1c_nonneg _) (Nat.cast_nonneg E)
    _ = ((Z.card * E * L : ℕ) : ℤ) := by simp; ring

#print axioms finite_kernel_positive_multiple
#print axioms coefficient_norm_sum_bound
end S07V34.Explicit

namespace S07V34.Explicit
open TypedTriangle.GroupingExplicit

def relationBound (d R : ℕ) : ℕ := kernelBound (monitorDimension d R) (monitorMagnitude d R)
def relationCount (d R : ℕ) : ℕ := (2 * relationBound d R + 1) ^ boxSize d R
def paymentExponent (d R : ℕ) : ℕ := torsionExponent d (R * relationBound d R) R
def paymentCost (d R : ℕ) : ℕ :=
  relationBound d R + relationCount d R * relationBound d R * paymentExponent d R

theorem bounded_kernel_class_annihilated (d B R : ℕ) (S D : Finset (Fin d → ℤ))
    (hS : ∀ s ∈ S, ∀ j, |s j| ≤ (R : ℤ))
    (hD : ∀ s ∈ D, ∀ j, |s j| ≤ (R : ℤ)) {k : ℕ}
    (ψ : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ))
    (hker : (ψ.ker : Set (Qt S ⧸ Hgrp S D)).Finite)
    (v : Fin d → ℤ) (hv : ∀ j, |v j| ≤ (B : ℤ))
    (hz : ψ (canonicalMap S D v) = 0) :
    (torsionExponent d B R : ℤ) • canonicalMap S D v = 0 := by
  obtain ⟨n, hn, hnzero⟩ := finite_kernel_positive_multiple ψ hker (canonicalMap S D v) hz
  have hmem : (n : ℤ) • v ∈ span ℤ ((S ∪ D : Finset _) : Set (Fin d → ℤ)) := by
    apply (canonicalMap_eq_zero_iff S D _).mp
    simpa only [map_zsmul, map_nsmul, natCast_zsmul] using hnzero
  have hΓ : ∀ s ∈ S ∪ D, ∀ j, |s j| ≤ (R : ℤ) := by
    intro s hs j
    rcases mem_union.mp hs with hs | hs
    · exact hS s hs j
    · exact hD s hs j
  have he := factorial_multiple_mem_span d B R (S ∪ D) hΓ v hv ⟨n, hn, hmem⟩
  have hq := (canonicalMap_eq_zero_iff S D _).mpr he
  simpa only [map_zsmul] using hq

#print axioms bounded_kernel_class_annihilated
end S07V34.Explicit
