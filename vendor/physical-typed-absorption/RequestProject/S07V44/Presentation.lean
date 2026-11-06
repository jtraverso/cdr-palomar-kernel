/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Catalog
public import RequestProject.S07V44.Padding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V44 §2 — the REALIZABLE coordinate presentation of `K_Z` on the actual fixed core

Fix `C0 : CoreCompression H lab F W d c E` (V42).  Nothing here assumes `C0.q` surjective, and no
coupling map `Qt S →+ ClassQ` on all of `ℤ^d/⟨S⟩` is introduced.

* `Realizable C0 v` : `v = C0.q x` for an actual `x ∈ M(H[W])`.
* `Dset C0 R Z` : the catalog coordinates `v ∈ box d R` with a REAL preimage `x` whose actual class
  lies in `K_Z`.  Dummy catalog entries (no preimage, `gCat = 0`) are never in `Dset`.
* `CatalogGen C0 R Z` : the active fixed catalog generates `K_Z` (the exact conclusion of V42
  `catalog_generates`; `catalogGen_of_H3H4` derives it from the original H3/H4 data).
* `qmk_q_eq_iff` : for `x, y ∈ M(H[W])`, `[q x] = [q y]` in `ℤ^d/⟨S⟩` iff `[x] = [y]` in `ClassQ`
  (from `CoreCompression.class_eq_iff`; torsion exact).
* `coord_mem_H_imp_KZ` / `KZ_imp_coord_mem_H` / `KZ_iff_coord` : for every `x ∈ M(H[W])`,
  `[x] ∈ K_Z ↔ [q x] ∈ ⟨[Dset]⟩`, i.e. the coordinate span of `Dset` models `K_Z` EXACTLY on the
  realizable coordinate subgroup (the direction `→` uses `CatalogGen`; `←` uses nothing).
* `realCoupling C0` : the coupling defined ONLY on the realizable subgroup `range C0.q`,
  `realCoupling ⟨q x, _⟩ = [x]` (`realCoupling_apply`), with kernel exactly `range q ∩ ⟨S⟩`
  (`realCoupling_eq_zero_iff`).
-/

open Finset Classical Submodule

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V44

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- a coordinate vector is realizable when it is `C0.q` of an actual core local profile -/
def Realizable (C0 : CoreCompression H lab F W d c E) (v : Fin d → ℤ) : Prop :=
  ∃ x : MCore H lab F W, C0.q x = v

/-- catalog coordinates with a REAL core preimage whose actual class lies in `K_Z` -/
def Dset (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V) : Finset (Fin d → ℤ) :=
  (box d R).filter fun v => ∃ x : MCore H lab F W, C0.q x = v ∧
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z

/-- the active fixed catalog generates `K_Z` (conclusion of V42 `catalog_generates`) -/
def CatalogGen (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V) : Prop :=
  AddSubgroup.closure {k | ∃ v, gCat C0 R v = k ∧ gCat C0 R v ∈ KZ H lab F W Z} =
    (KZ H lab F W Z).toAddSubgroup

/-- the coordinate class hom `M(H[W]) → ℤ^d/⟨S⟩` -/
def cq (C0 : CoreCompression H lab F W d c E) : MCore H lab F W →+ Qt C0.S :=
  (QuotientAddGroup.mk' _).comp C0.q.toAddMonoidHom

/-- the actual class hom `M(H[W]) → ClassQ` -/
def clsCore (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (W : Finset V) :
    MCore H lab F W →+ ClassQ H lab F W :=
  (LamCore H lab F W).mkQ.toAddMonoidHom.comp (MCore H lab F W).subtype.toAddMonoidHom

lemma clsCore_apply (x : MCore H lab F W) :
    clsCore H lab F W x = clsQ H lab F W (x : Sym2 V → ℤ) := rfl

lemma cq_apply (C0 : CoreCompression H lab F W d c E) (x : MCore H lab F W) :
    cq C0 x = qmk C0.S (C0.q x) := rfl

lemma Dset_subset_box (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V) :
    Dset C0 R Z ⊆ box d R := filter_subset _ _

lemma mem_Dset {C0 : CoreCompression H lab F W d c E} {R : ℕ} {Z : Finset V}
    {v : Fin d → ℤ} : v ∈ Dset C0 R Z ↔ v ∈ box d R ∧ ∃ x : MCore H lab F W, C0.q x = v ∧
      clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z := by
  unfold Dset; rw [mem_filter]

/-- every element of `Dset` is realizable -/
lemma Dset_realizable {C0 : CoreCompression H lab F W d c E} {R : ℕ} {Z : Finset V}
    {v : Fin d → ℤ} (hv : v ∈ Dset C0 R Z) : Realizable C0 v := by
  obtain ⟨-, x, hx, -⟩ := mem_Dset.1 hv
  exact ⟨x, hx⟩

/-- dummy catalog coordinates (no real preimage) are never relations of the presentation -/
lemma not_mem_Dset_of_not_realizable {C0 : CoreCompression H lab F W d c E} {R : ℕ}
    {Z : Finset V} {v : Fin d → ℤ} (h : ¬ Realizable C0 v) : v ∉ Dset C0 R Z :=
  fun hv => h (Dset_realizable hv)

/-- dummy catalog entries are active (their charge is `0 ∈ K_Z`) -/
lemma dummy_active (C0 : CoreCompression H lab F W d c E) {R : ℕ} (Z : Finset V) (v : Cat d R)
    (h : ¬ Realizable C0 v.1) : gCat C0 R v ∈ KZ H lab F W Z := by
  rw [gCat_of_not C0 v h]; exact zero_mem _

/-- **exact coordinate classes iff exact physical classes** (torsion included) -/
theorem qmk_q_eq_iff (C0 : CoreCompression H lab F W d c E) (x y : MCore H lab F W) :
    qmk C0.S (C0.q x) = qmk C0.S (C0.q y) ↔
      clsQ H lab F W (x : Sym2 V → ℤ) = clsQ H lab F W (y : Sym2 V → ℤ) := by
  rw [C0.class_eq_iff]
  unfold qmk
  rw [QuotientAddGroup.eq, ← Submodule.span_int_eq_addSubgroupClosure,
    Submodule.mem_toAddSubgroup]
  have e : C0.q x - C0.q y = -(-C0.q x + C0.q y) := by abel
  rw [e, Submodule.neg_mem_iff]

/-- **`←` : coordinate membership in `⟨[Dset]⟩` gives actual membership in `K_Z`** -/
theorem coord_mem_H_imp_KZ (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V)
    (x : MCore H lab F W) (hx : qmk C0.S (C0.q x) ∈ Hgrp C0.S (Dset C0 R Z)) :
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z := by
  let P : AddSubgroup (Qt C0.S) :=
    ((KZ H lab F W Z).toAddSubgroup.comap (clsCore H lab F W)).map (cq C0)
  have hle : Hgrp C0.S (Dset C0 R Z) ≤ P := by
    unfold Hgrp
    rw [AddSubgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨-, y, hy, hyK⟩ := mem_Dset.1 (Finset.mem_coe.1 hv)
    exact ⟨y, hyK, by rw [cq_apply, hy]⟩
  obtain ⟨y, hyK, hy⟩ := hle hx
  rw [cq_apply, qmk_q_eq_iff] at hy
  rw [← hy]
  exact hyK

/-- **`→` : under catalog generation, actual membership in `K_Z` gives coordinate membership** -/
theorem KZ_imp_coord_mem_H (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V)
    (hgen : CatalogGen C0 R Z) (x : MCore H lab F W)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z) :
    qmk C0.S (C0.q x) ∈ Hgrp C0.S (Dset C0 R Z) := by
  let P : AddSubgroup (ClassQ H lab F W) :=
    ((Hgrp C0.S (Dset C0 R Z)).comap (cq C0)).map (clsCore H lab F W)
  have hle : AddSubgroup.closure {k | ∃ v, gCat C0 R v = k ∧ gCat C0 R v ∈ KZ H lab F W Z} ≤
      P := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl, hv⟩
    by_cases hr : ∃ y : MCore H lab F W, C0.q y = v.1
    · obtain ⟨y, hy⟩ := hr
      have hg := gCat_spec C0 v y hy
      refine ⟨y, ?_, hg.symm⟩
      show cq C0 y ∈ Hgrp C0.S (Dset C0 R Z)
      rw [cq_apply, hy]
      refine AddSubgroup.subset_closure ⟨v.1, Finset.mem_coe.2 (mem_Dset.2 ⟨v.2, y, hy, ?_⟩), rfl⟩
      rw [← hg]; exact hv
    · rw [gCat_of_not C0 v hr]
      exact zero_mem _
  have hx' : clsQ H lab F W (x : Sym2 V → ℤ) ∈
      AddSubgroup.closure {k | ∃ v, gCat C0 R v = k ∧ gCat C0 R v ∈ KZ H lab F W Z} := by
    rw [hgen]; exact hx
  obtain ⟨y, hyH, hy⟩ := hle hx'
  rw [clsCore_apply, ← qmk_q_eq_iff C0] at hy
  rw [← hy]
  exact hyH

/-- **the coordinate span of `Dset` models `K_Z` exactly on realizable coordinates** -/
theorem KZ_iff_coord (C0 : CoreCompression H lab F W d c E) (R : ℕ) (Z : Finset V)
    (hgen : CatalogGen C0 R Z) (x : MCore H lab F W) :
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z ↔
      qmk C0.S (C0.q x) ∈ Hgrp C0.S (Dset C0 R Z) :=
  ⟨KZ_imp_coord_mem_H C0 R Z hgen x, coord_mem_H_imp_KZ C0 R Z x⟩

/-- **catalog generation from the original H3/H4 data** (V42 `catalog_generates`) -/
theorem catalogGen_of_H3H4 {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    CatalogGen C0 (catR β d c E d' c' E') Z :=
  catalog_generates hβ hH3 hH4 hW C0 hZ CZ

/-! ## The coupling, defined only on the realizable coordinate subgroup -/

/-- the realizable coordinate subgroup `range C0.q ⊆ ℤ^d` -/
def realSub (C0 : CoreCompression H lab F W d c E) : AddSubgroup (Fin d → ℤ) :=
  C0.q.toAddMonoidHom.range

lemma ker_q_le (C0 : CoreCompression H lab F W d c E) :
    C0.q.toAddMonoidHom.ker ≤ (clsCore H lab F W).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker, clsCore_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 (C0.ker_le x hx)

/-- **the coupling on the realizable subgroup only**: `⟨q x, _⟩ ↦ [x]` -/
def realCoupling (C0 : CoreCompression H lab F W d c E) : realSub C0 →+ ClassQ H lab F W :=
  (QuotientAddGroup.lift _ (clsCore H lab F W) (ker_q_le C0)).comp
    (QuotientAddGroup.quotientKerEquivRange C0.q.toAddMonoidHom).symm.toAddMonoidHom

lemma realCoupling_apply (C0 : CoreCompression H lab F W d c E) (x : MCore H lab F W) :
    realCoupling C0 ⟨C0.q x, x, rfl⟩ = clsQ H lab F W (x : Sym2 V → ℤ) := by
  unfold realCoupling
  have : (QuotientAddGroup.quotientKerEquivRange C0.q.toAddMonoidHom).symm ⟨C0.q x, x, rfl⟩ =
      (x : MCore H lab F W ⧸ C0.q.toAddMonoidHom.ker) := by
    rw [AddEquiv.symm_apply_eq]; rfl
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  erw [this]
  rfl

/-- the realizable coupling has kernel exactly `range q ∩ ⟨S⟩` (exact torsion) -/
theorem realCoupling_eq_zero_iff (C0 : CoreCompression H lab F W d c E) (r : realSub C0) :
    realCoupling C0 r = 0 ↔ (r : Fin d → ℤ) ∈ span ℤ (C0.S : Set (Fin d → ℤ)) := by
  obtain ⟨_, x, rfl⟩ := r
  have h : realCoupling C0 ⟨C0.q.toAddMonoidHom x, x, rfl⟩ =
      clsQ H lab F W (x : Sym2 V → ℤ) := realCoupling_apply C0 x
  rw [h]
  show _ ↔ C0.q x ∈ _
  have := C0.class_eq_iff x 0
  simp only [map_zero, sub_zero, ZeroMemClass.coe_zero] at this
  rw [← this]
  unfold clsQ
  rfl

end S07V44
