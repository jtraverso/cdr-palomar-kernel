/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V44.Presentation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V44 §3 — physical integer monitors on the actual core `M(H[W])`

For any additive `ψ : Qt S ⧸ Hgrp S D →+ ℤ^K` on the bounded coordinate presentation
(`S = C0.S`, `D = Dset C0 R Z`) the PHYSICAL monitor is
`physMon C0 D ψ x = ψ ([C0.q x] mod ⟨[D]⟩)` for `x ∈ M(H[W])`.

* `physMon_congr` : it depends only on the actual class `[x] ∈ ClassQ`.
* `physMon_eq_zero_of_KZ`, `physMon_annihilates` : under `CatalogGen`, it vanishes on every
  `x` with `[x] ∈ K_Z`, in particular on every `x ∈ M(H[W \ Z]) ∩ Λ(H − Z)`.
* `physMon_ker_mod_KZ` : if `ker ψ` is finite there is a finite set `T` of actual classes such that
  `physMon x = 0 → ∃ t ∈ T, [x] − t ∈ K_Z` (finite kernel modulo `K_Z`; torsion exact).
* `physMon_catalog_le` : `‖physMon x‖₁ ≤ M` when `q x` lies in the monitor box and `ψ` is
  `M`-bounded on the box.
* `physMon_l1_le` : with unit vectors in the box (radius `≥ 1`),
  `‖physMon x‖₁ ≤ M · (d · c) · l1E x` (via `C0.bound`).
* `physMon_word_le` : `‖physMon (y0 + ∑ n i • y i)‖₁ ≤ Eb + M · S'` for catalog-bounded `y i`.
* `physMonReal C0 D ψ j : M(H[W]) →ₗ[ℤ] ℝ` : the individual real-valued `ℤ`-linear coordinates,
  with `|physMonReal j x| ≤ M (d c) l1E x` and vanishing on `M(H[W \ Z]) ∩ Λ(H − Z)`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V44

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- the coordinate class modulo `⟨[D]⟩` -/
def coordCls (C0 : CoreCompression H lab F W d c E) (D : Finset (Fin d → ℤ)) :
    MCore H lab F W →+ Qt C0.S ⧸ Hgrp C0.S D :=
  (QuotientAddGroup.mk' _).comp (cq C0)

lemma coordCls_apply (C0 : CoreCompression H lab F W d c E) (D : Finset (Fin d → ℤ))
    (x : MCore H lab F W) :
    coordCls C0 D x = ((qmk C0.S (C0.q x) : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D) := rfl

/-- **the physical monitor on the actual core** -/
def physMon (C0 : CoreCompression H lab F W d c E) (D : Finset (Fin d → ℤ)) {K : ℕ}
    (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ)) : MCore H lab F W →+ (Fin K → ℤ) :=
  psi.comp (coordCls C0 D)

lemma physMon_apply (C0 : CoreCompression H lab F W d c E) (D : Finset (Fin d → ℤ)) {K : ℕ}
    (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ)) (x : MCore H lab F W) :
    physMon C0 D psi x = psi ((qmk C0.S (C0.q x) : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D) := rfl

variable (C0 : CoreCompression H lab F W d c E) {K : ℕ}

/-- the physical monitor depends only on the actual class -/
theorem physMon_congr (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    {x y : MCore H lab F W}
    (h : clsQ H lab F W (x : Sym2 V → ℤ) = clsQ H lab F W (y : Sym2 V → ℤ)) :
    physMon C0 D psi x = physMon C0 D psi y := by
  rw [physMon_apply, physMon_apply, (qmk_q_eq_iff C0 x y).2 h]

/-- **the physical monitor annihilates every core vector with class in `K_Z`** -/
theorem physMon_eq_zero_of_KZ (R : ℕ) (Z : Finset V) (hgen : CatalogGen C0 R Z)
    (psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ)) (x : MCore H lab F W)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W Z) :
    physMon C0 (Dset C0 R Z) psi x = 0 := by
  rw [physMon_apply, (QuotientAddGroup.eq_zero_iff _).2 (KZ_imp_coord_mem_H C0 R Z hgen x hx),
    map_zero]

/-- **the physical monitor annihilates `M(H[W \ Z]) ∩ Λ(H − Z)`** -/
theorem physMon_annihilates (R : ℕ) (Z : Finset V) (hgen : CatalogGen C0 R Z)
    (psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ)) (x : MCore H lab F W)
    (hxM : (x : Sym2 V → ℤ) ∈ MZ H lab F W Z) (hxL : (x : Sym2 V → ℤ) ∈ LamDel H lab F Z) :
    physMon C0 (Dset C0 R Z) psi x = 0 :=
  physMon_eq_zero_of_KZ C0 R Z hgen psi x ((mem_KZ H lab F W).2 ⟨_, hxM, hxL, rfl⟩)

/-- **finite kernel modulo `K_Z`** (exact torsion; no catalog generation needed) -/
theorem physMon_ker_mod_KZ (R : ℕ) (Z : Finset V)
    (psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ))
    (hker : (psi.ker : Set (Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z))).Finite) :
    ∃ T : Finset (ClassQ H lab F W), ∀ x : MCore H lab F W,
      physMon C0 (Dset C0 R Z) psi x = 0 →
        ∃ t ∈ T, clsQ H lab F W (x : Sym2 V → ℤ) - t ∈ KZ H lab F W Z := by
  let rep : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) → ClassQ H lab F W := fun e =>
    if h : ∃ x : MCore H lab F W, coordCls C0 (Dset C0 R Z) x = e then
      clsQ H lab F W (h.choose : Sym2 V → ℤ) else 0
  refine ⟨hker.toFinset.image rep, fun x hx => ?_⟩
  set e := coordCls C0 (Dset C0 R Z) x with he
  have hex : ∃ y : MCore H lab F W, coordCls C0 (Dset C0 R Z) y = e := ⟨x, rfl⟩
  refine ⟨rep e, mem_image.2 ⟨e, hker.mem_toFinset.2 hx, rfl⟩, ?_⟩
  simp only [rep, dif_pos hex]
  set y := hex.choose with hy
  have hye : coordCls C0 (Dset C0 R Z) y = e := hex.choose_spec
  have h0 : coordCls C0 (Dset C0 R Z) (x - y) = 0 := by rw [map_sub, hye, he, sub_self]
  rw [coordCls_apply, QuotientAddGroup.eq_zero_iff] at h0
  have := coord_mem_H_imp_KZ C0 R Z (x - y) h0
  unfold clsQ at this ⊢
  rwa [Submodule.coe_sub, Submodule.Quotient.mk_sub] at this

/-- the box is monotone in the radius -/
lemma box_mono {R R' : ℕ} (h : R ≤ R') : box d R ⊆ box d R' := by
  intro v hv
  rw [mem_box] at hv ⊢
  exact fun i => (hv i).trans (by exact_mod_cast h)

/-- **catalog bound**: core vectors with coordinates in the box have monitor at most `M` -/
theorem physMon_catalog_le (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    {R0 M : ℕ}
    (hM : ∀ b ∈ box d R0, l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) ≤ M)
    (x : MCore H lab F W) (hx : ∀ i, |C0.q x i| ≤ R0) :
    l1 (physMon C0 D psi x) ≤ M :=
  hM _ (mem_box.2 hx)

/-- the unit vector `e_i` -/
def unitV (i : Fin d) : Fin d → ℤ := Pi.single i 1

lemma unitV_mem_box {R0 : ℕ} (h1 : 1 ≤ R0) (i : Fin d) : unitV i ∈ box d R0 := by
  rw [mem_box]
  intro j
  by_cases hij : j = i
  · subst hij; simp [unitV]; exact_mod_cast h1
  · simp [unitV, hij]

lemma eq_sum_unitV (v : Fin d → ℤ) : v = ∑ i, v i • unitV i := by
  funext j
  simp [unitV, Finset.sum_apply, Pi.single_apply]

/-- the coordinate class is the word of its coordinates in the unit vectors -/
lemma physMon_eq_sum (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    (x : MCore H lab F W) :
    physMon C0 D psi x = psi (∑ i, C0.q x i •
      ((qmk C0.S (unitV i) : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) := by
  rw [physMon_apply]
  congr 1
  have e : ((qmk C0.S (C0.q x) : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D) =
      ((qmk C0.S (∑ i, C0.q x i • unitV i) : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D) := by
    rw [← eq_sum_unitV]
  rw [e]
  unfold qmk
  rw [QuotientAddGroup.mk_sum, QuotientAddGroup.mk_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [QuotientAddGroup.mk_zsmul, QuotientAddGroup.mk_zsmul]

/-- coordinate `ℓ¹` bound from `C0.bound` -/
lemma sum_abs_q_le (x : MCore H lab F W) :
    ∑ i, |C0.q x i| ≤ ((d * c : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ) := by
  calc ∑ i, |C0.q x i| ≤ ∑ _i : Fin d, (c : ℤ) * l1E (x : Sym2 V → ℤ) :=
        sum_le_sum fun i _ => C0.bound x i
    _ = ((d * c : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

/-- **uniform `ℓ¹` bound of the physical monitor** by `M · (d · c) · l1E x` -/
theorem physMon_l1_le (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    {R0 M : ℕ} (h1 : 1 ≤ R0)
    (hM : ∀ b ∈ box d R0, l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) ≤ M)
    (x : MCore H lab F W) :
    l1 (physMon C0 D psi x) ≤ ((M * (d * c) : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ) := by
  let mkD : (Fin d → ℤ) →+ Qt C0.S ⧸ Hgrp C0.S D :=
    (QuotientAddGroup.mk' (Hgrp C0.S D)).comp
      (QuotientAddGroup.mk' (AddSubgroup.closure (C0.S : Set (Fin d → ℤ))))
  have hg : ∀ i ∈ (univ : Finset (Fin d)), l1 ((psi.comp mkD) (unitV i)) ≤ M :=
    fun i _ => hM (unitV i) (unitV_mem_box h1 i)
  have h0 := l1_map_sum_le (psi.comp mkD) univ unitV (fun i => C0.q x i) M hg
  have he : (psi.comp mkD) (∑ i ∈ univ, C0.q x i • unitV i) = physMon C0 D psi x := by
    rw [← eq_sum_unitV]; rfl
  have h1' : l1 (physMon C0 D psi x) ≤ M * ∑ i, |C0.q x i| := by
    rw [← he]; exact h0
  have h2 := sum_abs_q_le C0 x
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  calc l1 (physMon C0 D psi x) ≤ M * ∑ i, |C0.q x i| := h1'
    _ ≤ M * (((d * c : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ)) := mul_le_mul_of_nonneg_left h2 hM0
    _ = ((M * (d * c) : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ) := by
        rw [Nat.cast_mul (M) (d * c), mul_assoc]

/-- **monitor of a word in catalog-bounded vectors** (`Eb + M · S'`) -/
theorem physMon_word_le (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    {R0 M : ℕ}
    (hM : ∀ b ∈ box d R0, l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) ≤ M)
    {ι : Type*} (T : Finset ι) (y0 : MCore H lab F W) (y : ι → MCore H lab F W) (n : ι → ℤ)
    (hy : ∀ i ∈ T, ∀ j, |C0.q (y i) j| ≤ R0) {Eb S' : ℕ}
    (hE : l1 (physMon C0 D psi y0) ≤ Eb) (hS : ∑ i ∈ T, |n i| ≤ S') :
    l1 (physMon C0 D psi (y0 + ∑ i ∈ T, n i • y i)) ≤ Eb + M * S' := by
  rw [map_add, map_sum]
  simp only [map_zsmul]
  have h1 := l1_add_le (physMon C0 D psi y0) (∑ i ∈ T, n i • physMon C0 D psi (y i))
  have h2 := l1_map_sum_le (AddMonoidHom.id (Fin K → ℤ)) T (fun i => physMon C0 D psi (y i)) n M
    (fun i hi => physMon_catalog_le C0 D psi hM (y i) (hy i hi))
  simp only [AddMonoidHom.id_apply] at h2
  have h3 : (M : ℤ) * ∑ i ∈ T, |n i| ≤ M * S' := mul_le_mul_of_nonneg_left hS (by positivity)
  linarith

/-- an individual coordinate is bounded by the `ℓ¹` norm -/
lemma abs_le_l1 {K : ℕ} (v : Fin K → ℤ) (j : Fin K) : |v j| ≤ l1 v :=
  single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _) (mem_univ j)

/-- **individual real-valued `ℤ`-linear monitor coordinates** (for native functional gluing) -/
def physMonReal (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    (j : Fin K) : MCore H lab F W →ₗ[ℤ] ℝ :=
  ((Int.castAddHom ℝ).comp ((Pi.evalAddMonoidHom (fun _ : Fin K => ℤ) j).comp
    (physMon C0 D psi))).toIntLinearMap

lemma physMonReal_apply (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    (j : Fin K) (x : MCore H lab F W) :
    physMonReal C0 D psi j x = ((physMon C0 D psi x j : ℤ) : ℝ) := rfl

/-- **real-valued coordinate bound** `|physMonReal j x| ≤ M (d c) · l1E x` -/
theorem physMonReal_abs_le (D : Finset (Fin d → ℤ)) (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    {R0 M : ℕ} (h1 : 1 ≤ R0)
    (hM : ∀ b ∈ box d R0, l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) ≤ M)
    (j : Fin K) (x : MCore H lab F W) :
    |physMonReal C0 D psi j x| ≤ ((M * (d * c) : ℕ) : ℝ) * (l1E (x : Sym2 V → ℤ) : ℝ) := by
  rw [physMonReal_apply]
  have := (abs_le_l1 (physMon C0 D psi x) j).trans (physMon_l1_le C0 D psi h1 hM x)
  have h' : ((|physMon C0 D psi x j| : ℤ) : ℝ) ≤
      (((M * (d * c) : ℕ) : ℤ) * l1E (x : Sym2 V → ℤ) : ℤ) := by exact_mod_cast this
  push_cast at h' ⊢
  exact h'

/-- **real-valued coordinates vanish on `M(H[W \ Z]) ∩ Λ(H − Z)`** -/
theorem physMonReal_annihilates (R : ℕ) (Z : Finset V) (hgen : CatalogGen C0 R Z)
    (psi : Qt C0.S ⧸ Hgrp C0.S (Dset C0 R Z) →+ (Fin K → ℤ)) (j : Fin K) (x : MCore H lab F W)
    (hxM : (x : Sym2 V → ℤ) ∈ MZ H lab F W Z) (hxL : (x : Sym2 V → ℤ) ∈ LamDel H lab F Z) :
    physMonReal C0 (Dset C0 R Z) psi j x = 0 := by
  rw [physMonReal_apply, physMon_annihilates C0 R Z hgen psi x hxM hxL]
  simp

end S07V44
