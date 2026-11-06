/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V44.Activation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V46 §5 — the FULL-coordinate monitor: payment to the EXACT zero class

V44 `PhysicalMonitors C0 R Z` pays a class into `K_Z`.  The last step of the allocation must cancel
the residual EXACTLY (torsion included), i.e. pay into `⊥`.  This is the V34 monitor for the
relation set `D = ∅` (`Hgrp S ∅ = ⊥`), transported to the actual class group through real
preimages exactly as in V44 (no coupling map is introduced).

* `Hgrp_empty` : `Hgrp S ∅ = ⊥`.
* `coord_word_to_zero` : `[q x] + ∑ z b • [b] = 0` in `ℤ^d/⟨S⟩` (with `z` supported on realizable
  coordinates) ⇒ `[x] + ∑ z b • [realRep b] = 0` in `ClassQ`.
* `physMon_payment_zero` : the integer payment to the exact zero class, cost `≤ A (1 + ‖ψ x‖₁)`.
* `FullMonitor C0 R A M K` : the package (monitor, box bound, payment to `0`).
* `uniform_monitors_with_full d c E R` : ONE triple `A, M, K`, fixed from `(d, c, E, R)` before the
  host, serves every `PhysicalMonitors C0 R Z` (any `Z` with `CatalogGen`) AND a `FullMonitor`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V46

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

lemma Hgrp_empty (S : Finset (Fin d → ℤ)) : Hgrp S ∅ = ⊥ := by
  unfold Hgrp; simp

variable (C0 : CoreCompression H lab F W d c E)

/-- every catalog charge is the class of its chosen real preimage (`0` for dummies) -/
lemma gCat_eq_clsQ_realRep {R : ℕ} (v : Cat d R) :
    gCat C0 R v = clsQ H lab F W (realRep C0 v.1 : Sym2 V → ℤ) := by
  by_cases h : Realizable C0 v.1
  · exact gCat_eq_realRep C0 v h
  · rw [gCat_of_not C0 v h]
    unfold realRep; rw [dif_neg h]
    unfold clsQ; simp

/-- **coordinate word to the exact zero class** -/
theorem coord_word_to_zero (x : MCore H lab F W)
    (B Cc : Finset (Fin d → ℤ)) (hCc : Cc ⊆ B) (z : (Fin d → ℤ) → ℤ)
    (hz0 : ∀ b, b ∉ Cc → z b = 0) (hreal : ∀ b ∈ Cc, Realizable C0 b)
    (h : qmk C0.S (C0.q x) + ∑ b ∈ B, z b • qmk C0.S b ∈ Hgrp C0.S ∅) :
    clsQ H lab F W (x : Sym2 V → ℤ) +
      ∑ b ∈ Cc, z b • clsQ H lab F W (realRep C0 b : Sym2 V → ℤ) = 0 := by
  set y : MCore H lab F W := x + ∑ b ∈ Cc, z b • realRep C0 b with hy
  have hcq : cq C0 y = qmk C0.S (C0.q x) + ∑ b ∈ B, z b • qmk C0.S b := by
    rw [hy, map_add, map_sum, cq_apply]
    rw [← sum_subset hCc (fun b _ hb => by simp [hz0 b hb])]
    congr 1
    refine sum_congr rfl fun b hb => ?_
    rw [map_zsmul, cq_apply, q_realRep C0 (hreal b hb)]
  rw [Hgrp_empty, AddSubgroup.mem_bot, ← hcq, cq_apply] at h
  have h0 : qmk C0.S (C0.q y) = qmk C0.S (C0.q 0) := by rw [h, map_zero]; rfl
  rw [qmk_q_eq_iff] at h0
  have hcl : clsQ H lab F W (y : Sym2 V → ℤ) = clsQ H lab F W (x : Sym2 V → ℤ) +
      ∑ b ∈ Cc, z b • clsQ H lab F W (realRep C0 b : Sym2 V → ℤ) := by
    rw [← clsCore_apply, hy, map_add, map_sum, clsCore_apply]
    congr 1
  rw [← hcl, h0]
  unfold clsQ; simp

/-- **physical integer payment to the exact zero class** -/
theorem physMon_payment_zero {R R0 : ℕ} (hR : R ≤ R0) {K A : ℕ}
    (psi : Qt C0.S ⧸ Hgrp C0.S ∅ →+ (Fin K → ℤ))
    (hpay : ∀ C : Finset (Fin d → ℤ), C ⊆ box d R0 → ∀ y ∈ Kgrp C0.S C,
      ∃ z : (Fin d → ℤ) → ℤ, (∀ b, b ∉ C → z b = 0) ∧
        y + ∑ b ∈ box d R0, z b • qmk C0.S b ∈ Hgrp C0.S ∅ ∧
        ∑ b ∈ box d R0, |z b| ≤ (A : ℤ) * (1 + l1 (psi (y : Qt C0.S ⧸ Hgrp C0.S ∅))))
    (Cset : Finset (Cat d R)) (x : MCore H lab F W)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R '' (Cset : Set _))) :
    ∃ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) ∧ (∀ v, z v ≠ 0 → Realizable C0 v.1) ∧
      clsQ H lab F W (x : Sym2 V → ℤ) + ∑ v, z v • gCat C0 R v = 0 ∧
      ∑ v, |z v| ≤ (A : ℤ) * (1 + l1 (physMon C0 ∅ psi x)) := by
  set Cc := realCoords C0 Cset with hCcdef
  have hCcR : Cc ⊆ box d R := realCoords_subset_box C0 Cset
  have hCc0 : Cc ⊆ box d R0 := hCcR.trans (box_mono hR)
  obtain ⟨z, hz0, hzH, hzc⟩ := hpay Cc hCc0 _ (coord_mem_Kgrp_of_closure C0 Cset x hx)
  have hphys := coord_word_to_zero C0 x (box d R0) Cc hCc0 z hz0
    (fun b hb => realCoords_realizable C0 hb) hzH
  refine ⟨fun v => z v.1, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine hz0 _ fun hvC => hv ?_
    exact mem_realCoords_of_val C0 hvC
  · intro v hv
    by_contra hr
    exact hv (hz0 _ fun hvC => hr (realCoords_realizable C0 hvC))
  · have hterm : ∀ v : Cat d R, z v.1 • gCat C0 R v =
        z v.1 • clsQ H lab F W (realRep C0 v.1 : Sym2 V → ℤ) := fun v => by
      rw [gCat_eq_clsQ_realRep C0 v]
    have : ∑ v : Cat d R, z v.1 • gCat C0 R v =
        ∑ b ∈ Cc, z b • clsQ H lab F W (realRep C0 b : Sym2 V → ℤ) := by
      rw [Finset.sum_congr rfl fun v _ => hterm v]
      exact sum_cat_of_support hCcR (fun b => z b • clsQ H lab F W (realRep C0 b : Sym2 V → ℤ))
        (fun b hb => by simp [hz0 b hb])
    rw [this]; exact hphys
  · have h1 : ∑ v : Cat d R, |z v.1| = ∑ b ∈ Cc, |z b| :=
      sum_cat_of_support hCcR (fun b => |z b|) (fun b hb => by simp [hz0 b hb])
    have h2 : ∑ b ∈ box d R0, |z b| = ∑ b ∈ Cc, |z b| :=
      (sum_subset hCc0 fun b _ hb => by rw [hz0 b hb, abs_zero]).symm
    rw [h1, ← h2]
    exact hzc

/-- **the full-coordinate monitor package**: payment to the EXACT zero class -/
structure FullMonitor (C0 : CoreCompression H lab F W d c E) (R A M K : ℕ) where
  /-- the V34 monitor for the empty relation set -/
  psi : Qt C0.S ⧸ Hgrp C0.S ∅ →+ (Fin K → ℤ)
  /-- finite kernel -/
  ker_finite : (psi.ker : Set (Qt C0.S ⧸ Hgrp C0.S ∅)).Finite
  /-- uniform bound on the monitor box -/
  box_le : ∀ b ∈ box d (monR R E),
    l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S ∅)) ≤ M
  /-- integer payment to the exact zero class -/
  pay : ∀ (Cset : Finset (Cat d R)) (x : MCore H lab F W),
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R '' (Cset : Set _)) →
    ∃ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) ∧ (∀ v, z v ≠ 0 → Realizable C0 v.1) ∧
      clsQ H lab F W (x : Sym2 V → ℤ) + ∑ v, z v • gCat C0 R v = 0 ∧
      ∑ v, |z v| ≤ (A : ℤ) * (1 + l1 (physMon C0 ∅ psi x))

universe u v

/-- **One uniform triple `A, M, K` for all stratum monitors and the full monitor.** -/
theorem uniform_monitors_with_full (d c E R : ℕ) :
    ∃ A M K : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E),
      (∀ Z : Finset V, CatalogGen C0 R Z → Nonempty (PhysicalMonitors C0 R Z A M K)) ∧
      Nonempty (FullMonitor C0 R A M K) := by
  obtain ⟨A, M, K, h⟩ := uniform_monitor_payment_kmax d (box d (monR R E))
  refine ⟨A, M, K, ?_⟩
  intro V _ I H lab F W C0
  have hS : C0.S ⊆ box d (monR R E) := fun s hs => mem_box.2 fun i =>
    (C0.S_bound s hs i).trans (by exact_mod_cast E_le_monR R E)
  refine ⟨fun Z hgen => ?_, ?_⟩
  · have hD : Dset C0 R Z ⊆ box d (monR R E) :=
      (Dset_subset_box C0 R Z).trans (box_mono (R_le_monR R E))
    obtain ⟨psi, hker, hM, hpay⟩ := h C0.S (Dset C0 R Z) hS hD
    exact ⟨PhysicalMonitors.mk' C0 R Z hgen psi hker hM hpay⟩
  · obtain ⟨psi, hker, hM, hpay⟩ := h C0.S ∅ hS (empty_subset _)
    exact ⟨⟨psi, hker, hM, physMon_payment_zero C0 (R_le_monR R E) psi hpay⟩⟩

end S07V46
