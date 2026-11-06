/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V44.Payment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V44 §5 — UNIFORMLY bounded physical monitors and integer payment on the actual fixed core

`PhysicalMonitors C0 R E Z A M K` packages, for the actual fixed core compression `C0`, the
catalog radius `R` and the current deleted set `Z`:

* `psi` : a V34 monitor on the bounded coordinate presentation `Qt C0.S ⧸ ⟨[Dset C0 R Z]⟩` into
  `ℤ^K` with finite kernel and `‖ψ b‖₁ ≤ M` on the box of radius `monR R E = max(1, R, E)`;
* (1) `KZ_iff` : `[x] ∈ K_Z ↔ [q x] ∈ ⟨[Dset]⟩` for every `x ∈ M(H[W])`;
* (2) `annihilates`, `congr`, `ker_mod_KZ` : the physical monitor `physMon` vanishes on
  `M(H[W \ Z]) ∩ Λ(H − Z)`, depends only on the actual class, and has finite kernel modulo `K_Z`;
* (3) `catalog_le`, `l1_le`, `real_le`, `real_annihilates` : `‖physMon x‖₁ ≤ M` on catalog-bounded
  `x`, `‖physMon x‖₁ ≤ M (d c) l1E x`, and the individual real `ℤ`-linear coordinates;
* (4) `pay`, `pay_prev` : the integer catalog word reducing `[x]` into `K_Z` with cost
  `≤ A (1 + ‖physMon x‖₁)`, and `≤ A (1 + Eb + M S')` after a previous word of cost `S'`.

`uniform_physical_monitors d c E R` : `A, M, K` are fixed from `(d, c, E, R)` (in fact from
`(d, max(1,R,E))`) BEFORE the host; for every host, every `C0` and every `Z` with `CatalogGen`
the package exists.  `uniform_physical_monitors_H3H4` discharges `CatalogGen` from the original
H3/H4 core data and a `DelCompression` for `Z` (V42 `catalog_generates`), with `R = catR`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V44

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32

/-- the auxiliary monitor box radius `max(1, R, E)` -/
def monR (R E : ℕ) : ℕ := max 1 (max R E)

lemma one_le_monR (R E : ℕ) : 1 ≤ monR R E := le_max_left _ _
lemma R_le_monR (R E : ℕ) : R ≤ monR R E := (le_max_left R E).trans (le_max_right _ _)
lemma E_le_monR (R E : ℕ) : E ≤ monR R E := (le_max_right R E).trans (le_max_right _ _)

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- **the physical monitor package on the actual fixed core** -/
structure PhysicalMonitors (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V)
    (A M K : ℕ) where
  /-- the V34 monitor on the bounded coordinate presentation -/
  psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ)
  /-- finite kernel -/
  ker_finite : (psi.ker : Set (Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))).Finite
  /-- uniform bound on the monitor box -/
  box_le : ∀ b ∈ box d (monR R E),
    l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))) ≤ M
  /-- (1) the coordinate span of `Dset` models `K_Z` exactly on realizable coordinates -/
  KZ_iff : ∀ x : MCore H lab F W, clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z ↔
    qmk C0.S (C0.q x) ∈ Hgrp C0.S (Dset C0 R Z)
  /-- (2) annihilation of `M(H[W \ Z]) ∩ Λ(H − Z)` -/
  annihilates : ∀ x : MCore H lab F W, (x : Sym2 V → ℤ) ∈ MZ H lab F W Z →
    (x : Sym2 V → ℤ) ∈ LamDel H lab F Z → physMon C0 (Dset C0 R Z) psi x = 0
  /-- (2) dependence only on the actual class -/
  congr : ∀ x y : MCore H lab F W,
    clsQ H lab F W (x : Sym2 V → ℤ) = clsQ H lab F W (y : Sym2 V → ℤ) →
      physMon C0 (Dset C0 R Z) psi x = physMon C0 (Dset C0 R Z) psi y
  /-- (2) finite kernel modulo `K_Z` -/
  ker_mod_KZ : ∃ T : Finset (ClassQ H lab F W), ∀ x : MCore H lab F W,
    physMon C0 (Dset C0 R Z) psi x = 0 →
      ∃ t ∈ T, clsQ H lab F W (x : Sym2 V → ℤ) - t ∈ KZ H lab F W Z
  /-- (3) catalog bound -/
  catalog_le : ∀ x : MCore H lab F W, (∀ i, |C0.q x i| ≤ monR R E) →
    l1 (physMon C0 (Dset C0 R Z) psi x) ≤ M
  /-- (3) uniform `ℓ¹` bound -/
  l1_le : ∀ x : MCore H lab F W,
    l1 (physMon C0 (Dset C0 R Z) psi x) ≤ ((M * (d * c) : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ)
  /-- (3) real-valued `ℤ`-linear coordinates: bound -/
  real_le : ∀ (j : Fin K) (x : MCore H lab F W),
    |physMonReal C0 (Dset C0 R Z) psi j x| ≤
      ((M * (d * c) : ℕ) : ℝ) * (l1E (x : Sym2 V → ℤ) : ℝ)
  /-- (3) real-valued `ℤ`-linear coordinates: annihilation -/
  real_annihilates : ∀ (j : Fin K) (x : MCore H lab F W), (x : Sym2 V → ℤ) ∈ MZ H lab F W Z →
    (x : Sym2 V → ℤ) ∈ LamDel H lab F Z → physMonReal C0 (Dset C0 R Z) psi j x = 0
  /-- (4) integer payment in the actual class group -/
  pay : ∀ (Cset : Finset (Cat d R)) (x : MCore H lab F W),
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R '' (Cset : Set _)) →
    ∃ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) ∧ (∀ v, z v ≠ 0 → Realizable C0 v.1) ∧
      clsQ H lab F W (x : Sym2 V → ℤ) + ∑ v, z v • gCat C0 R v ∈ KZ H lab F W Z ∧
      ∑ v, |z v| ≤ (A : ℤ) * (1 + l1 (physMon C0 (Dset C0 R Z) psi x))
  /-- (4) payment after a previous word of cost `S'` (V43 recurrence form) -/
  pay_prev : ∀ (Cset : Finset (Cat d R)) {ι : Type} (T : Finset ι) (y0 : MCore H lab F W)
    (y : ι → MCore H lab F W) (n : ι → ℤ) (Eb S' : ℕ),
    (∀ i ∈ T, ∀ j, |C0.q (y i) j| ≤ monR R E) →
    l1 (physMon C0 (Dset C0 R Z) psi y0) ≤ Eb → ∑ i ∈ T, |n i| ≤ S' →
    clsQ H lab F W ((y0 + ∑ i ∈ T, n i • y i : MCore H lab F W) : Sym2 V → ℤ) ∈
      AddSubgroup.closure (gCat C0 R '' (Cset : Set _)) →
    ∃ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) ∧ (∀ v, z v ≠ 0 → Realizable C0 v.1) ∧
      clsQ H lab F W ((y0 + ∑ i ∈ T, n i • y i : MCore H lab F W) : Sym2 V → ℤ) +
        ∑ v, z v • gCat C0 R v ∈ KZ H lab F W Z ∧
      ∑ v, |z v| ≤ (A : ℤ) * (1 + Eb + M * S')

/-- **assembly of the package from one V34 monitor** -/
def PhysicalMonitors.mk' (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V)
    (hgen : CatalogGen C0 R Z) {A M K : ℕ}
    (psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ))
    (hker : (psi.ker : Set (Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))).Finite)
    (hM : ∀ b ∈ box d (monR R E),
      l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))) ≤ M)
    (hpay : ∀ C : Finset (Fin d → ℤ), C ⊆ box d (monR R E) → ∀ y ∈ Kgrp C0.S C,
      ∃ z : (Fin d → ℤ) → ℤ, (∀ b, b ∉ C → z b = 0) ∧
        y + ∑ b ∈ box d (monR R E), z b • qmk C0.S b ∈ Hgrp C0.S (Dset C0 R Z) ∧
        ∑ b ∈ box d (monR R E), |z b| ≤
          (A : ℤ) * (1 + l1 (psi (y : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))))) :
    PhysicalMonitors C0 R Z A M K where
  psi := psi
  ker_finite := hker
  box_le := hM
  KZ_iff := KZ_iff_coord C0 R Z hgen
  annihilates := physMon_annihilates C0 R Z hgen psi
  congr := fun _ _ h => physMon_congr C0 _ psi h
  ker_mod_KZ := physMon_ker_mod_KZ C0 R Z psi hker
  catalog_le := physMon_catalog_le C0 _ psi hM
  l1_le := physMon_l1_le C0 _ psi (one_le_monR R E) hM
  real_le := physMonReal_abs_le C0 _ psi (one_le_monR R E) hM
  real_annihilates := physMonReal_annihilates C0 R Z hgen psi
  pay := physMon_payment C0 (R_le_monR R E) Z psi hpay
  pay_prev := by
    intro Cset ι T y0 y n Eb S' hy hE hS hx
    obtain ⟨z, h1, h2, h3, h4⟩ := physMon_payment C0 (R_le_monR R E) Z psi hpay Cset _ hx
    refine ⟨z, h1, h2, h3, h4.trans ?_⟩
    have hw := physMon_word_le C0 _ psi hM T y0 y n hy hE hS
    have hA : (0 : ℤ) ≤ A := Int.natCast_nonneg A
    have : (1 : ℤ) + l1 (physMon C0 (Dset C0 R Z) psi (y0 + ∑ i ∈ T, n i • y i)) ≤
        1 + Eb + M * S' := by linarith
    calc (A : ℤ) * (1 + l1 (physMon C0 (Dset C0 R Z) psi (y0 + ∑ i ∈ T, n i • y i)))
        ≤ A * (1 + Eb + M * S') := mul_le_mul_of_nonneg_left this hA

universe u v

/-- **Uniform physical monitors and integer payment (main V44 theorem).** The constants
`A, M, K` are fixed from `(d, c, E, R)` before the host. -/
theorem uniform_physical_monitors (d c E R : ℕ) :
    ∃ A M K : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E)
      (Z : Finset V), CatalogGen C0 R Z → Nonempty (PhysicalMonitors C0 R Z A M K) := by
  obtain ⟨A, M, K, h⟩ := uniform_monitor_payment_kmax d (box d (monR R E))
  refine ⟨A, M, K, ?_⟩
  intro V _ I H lab F W C0 Z hgen
  have hS : C0.S ⊆ box d (monR R E) := fun s hs => mem_box.2 fun i =>
    (C0.S_bound s hs i).trans (by exact_mod_cast E_le_monR R E)
  have hD : Dset C0 R Z ⊆ box d (monR R E) :=
    (Dset_subset_box C0 R Z).trans (box_mono (R_le_monR R E))
  obtain ⟨psi, hker, hM, hpay⟩ := h C0.S (Dset C0 R Z) hS hD
  exact ⟨PhysicalMonitors.mk' C0 R Z hgen psi hker hM hpay⟩

/-- **The same, with catalog generation discharged from the original H3/H4 core data** and a
deleted-host compression for `Z` (V42 `catalog_generates`); the catalog radius is
`catR β d c E d' c' E'` and `A, M, K` are fixed from `(β, h, d, c, E, d', c', E')`. -/
theorem uniform_physical_monitors_H3H4 {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' : ℕ) :
    ∃ A M K : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ {Z : Finset V}, (Z.card : ℝ) ≤ coreDelta β h * W.card →
      DelCompression H lab F Z d' c' E' →
      Nonempty (PhysicalMonitors C0 (catR β d c E d' c' E') Z A M K) := by
  obtain ⟨A, M, K, hu⟩ := uniform_physical_monitors.{u, v} d c E (catR β d c E d' c' E')
  exact ⟨A, M, K, fun hH3 hH4 hW C0 _ hZ CZ =>
    hu C0 _ (catalogGen_of_H3H4 hβ hH3 hH4 hW C0 hZ CZ)⟩

end S07V44
