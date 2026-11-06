/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V39.DeletedGauge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V39 §3 — the physical gluing lemma

Setting: an ambient graph `G` and a subhost `H ≤ G` on the same vertex type, labels and family;
`Z` a small vertex set; `J = H − Z = delG H Z` and `Gz = G − Z = delG G Z`. The module `M_X` is
the ACTUAL local-profile module `TypedTriangle.Composition.localProfile X lab F` (the local
module, NOT identified with the physical lattice). Canonical inclusions
`M_J ≤ M_H` (`localProfile_delG_le`) and `M_J ≤ M_Gz` (`localProfile_mono` with `delG_mono`).

Inputs of the gluing lemma (an additive functional / norm bound is an INPUT here, not a claim
that a localized bank monitor has been constructed):
* `f : M_H → ℝ`, `f₀ : M_Gz → ℝ` additive, `|f x|, |f₀ x| ≤ A ‖x‖₁`;
* `f = f₀` on `M_J` (under the canonical inclusions);
* `f₀` annihilates the physical lattice `SparseEdge.lattice Gz lab F`;
* H satisfies the ORIGINAL H3/H4 with `α > 0`, `n ≥ n1Of α`, `|Z| ≤ delOf α h · n`.
No assumption is made on `G` beyond `H ≤ G`.

Construction (`glue`): with `λ_H`, `λ₀` the V38 `bounded_extension`s of `f`, `f₀`
(`|λ| ≤ A`), `t` the matching potential on `J` (`matching_potential_delG`, `|t| ≤ (6/α²+1)·2A`)
and `t' = liftPot H Z t` (§2):
* on every native column of `H` (an edge of `H` in an allowed triangle of `H`), INCLUDING edges
  incident with `Z`: `λ = λ_H − natB_Hᵀ t'` (the row potential is subtracted, no zero-filling);
* on every other edge of `Gz`: `λ = λ₀`;
* on every remaining pair (ambient edges touching `Z` outside the native columns of `H`, and
  non-edges): `λ = 0`.

Treatment of edges unsupported by allowed triangles: an edge of `H` lying in NO allowed triangle
of `H` carries no local-profile mass (`localProfile_supp`) and `natB_Hᵀ t'` vanishes on it
(`rowField_of_not_ncol`), so subtracting the row potential there changes nothing; its coefficient
is taken from the `Gz` extension `λ₀` if it avoids `Z` and is `0` otherwise. This is needed for
the triangle identity, since such an edge may still lie in an allowed triangle of `Gz` that
uses edges of `G` outside `H`. Non-edges get `0`.

Proved (`physical_gluing`):
* `|λ_e| ≤ glueConst α A = (1 + 4 (6/α² + 1)) A` for EVERY pair `e` (constant depends only on
  `α` and `A`);
* `∑_e λ_e x_e = f x` for EVERY `x ∈ M_H`;
* overlap agreement (`glue_overlap`): on native columns of `H` that are edges of `Gz`,
  `λ_H − natB_Hᵀ t' = λ₀` (every such edge is a native column of `J`, by H3, and there §2 and the
  matching identity apply);
* `∑_{e ∈ E(T)} λ_e = 0` for every allowed triangle `T` of `Gz`;
* `|∑_{e ∈ E(T)} λ_e| ≤ 3 · glueConst α A · |T ∩ Z|` for every allowed triangle `T` of `G`.
-/

open Finset Classical

noncomputable section

namespace S07V39

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
  TypedTriangle.Composition
open S07V25 S07V36 S07V37

variable {V I : Type*} [Fintype V] {lab : V → I} {F : Set (Multiset I)}

/-! ### Canonical inclusions of local modules -/

/-- **Local profiles are monotone in the graph** (same labels and family). -/
theorem localProfile_mono {G₁ G₂ : SimpleGraph V} (hle : G₁ ≤ G₂) :
    localProfile G₁ lab F ≤ localProfile G₂ lab F := by
  intro x hx
  obtain ⟨hs, hc⟩ := hx
  refine ⟨fun e he => hs e fun h1 => he ?_, fun v => ?_⟩
  · rw [mem_edges] at h1 ⊢; exact SimpleGraph.edgeSet_mono hle h1
  · obtain ⟨c, hcv⟩ := hc v
    refine ⟨fun T => if IsAllowed G₁ lab F T then c T else 0, fun w hw => ?_⟩
    rw [hcv w hw, ← Finset.sum_filter]
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨S07V39.allowed_mono hle h1, h2⟩, h3⟩, h1⟩
    · rintro ⟨⟨⟨-, h2⟩, h3⟩, h1⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- The canonical inclusion `M_{H−Z} ≤ M_H`. -/
theorem localProfile_delG_le (H : SimpleGraph V) (Z : Finset V) :
    localProfile (delG H Z) lab F ≤ localProfile H lab F :=
  localProfile_mono (delG_le H Z)

/-- Pairing with a local profile only sees its native columns. -/
lemma sum_ncol_profile {G : SimpleGraph V} {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x)
    (c : Sym2 V → ℝ) : ∑ e : NCol G lab F, c e.1 * (x e.1 : ℝ) = ∑ e, c e * (x e : ℝ) := by
  rw [S07V38.sum_ncol (fun e => c e * (x e : ℝ))]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · rfl
  · rw [S07V38.localProfile_supp hx e he, Int.cast_zero, mul_zero]

/-! ### The glued weights -/

/-- The constant of the gluing lemma, depending only on `α` and `A`. -/
def glueConst (α A : ℝ) : ℝ := (1 + 4 * (6 / α ^ 2 + 1)) * A

/-- **The glued weights**: `λ_H − natB_Hᵀ (liftPot t)` on native columns of `H` (edges incident
with `Z` included), `λ₀` on the other edges of `G − Z`, and `0` elsewhere. -/
def glue (G H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (Z : Finset V)
    (lamH lam0 : Sym2 V → ℝ) (t : NRow (delG H Z) lab F → ℝ) (e : Sym2 V) : ℝ :=
  if IsNCol H lab F e then lamH e - rowField H lab F (liftPot H lab F Z t) e
  else if e ∈ (delG G Z).edgeSet then lam0 e else 0

variable {G H : SimpleGraph V} {Z : Finset V}

/-- A native column of `H` that is an edge of `G − Z` is a native column of `H − Z` (H3). -/
theorem ncol_delG_of_edge {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H lab F α)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {e : Sym2 V} (he : IsNCol H lab F e)
    (heG : e ∈ (delG G Z).edgeSet) : IsNCol (delG H Z) lab F e := by
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hGxy, hx, hy⟩ := heG
    have hact : LinkActive H lab F x y := S07V38.ncol_linkActive he
    obtain ⟨w, hwZ, hyw, hT⟩ := fresh_nbr hα hH3 hZ hact
    refine ⟨{x, y, w}, allowed_delG_iff.2 ⟨hT, ?_⟩, mem_triEdges.2 ⟨by simp, by simp, hGxy.ne⟩⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption

/-- **Overlap agreement.** If `natB_Jᵀ t = λ_H − λ₀` on the native columns of `J = H − Z`, then
on every native column of `H` that is an edge of `G − Z`, `λ_H − natB_Hᵀ (liftPot t) = λ₀`. -/
theorem glue_overlap {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H lab F α)
    (hH4 : HingeCond H lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (lamH lam0 : Sym2 V → ℝ)
    (t : NRow (delG H Z) lab F → ℝ)
    (ht : ∀ e : NCol (delG H Z) lab F, S07V35.dat (natB (delG H Z) lab F) t e = lamH e - lam0 e)
    {e : Sym2 V} (he : IsNCol H lab F e) (heG : e ∈ (delG G Z).edgeSet) :
    lamH e - rowField H lab F (liftPot H lab F Z t) e = lam0 e := by
  have hJ := ncol_delG_of_edge (G := G) hα hH3 hZ he heG
  rw [lift_rowField hα hH3 hH4 hn hZ t hJ]
  have := ht ⟨e, hJ⟩
  rw [← rowField_eq_dat] at this
  simp only at this
  rw [this]; ring

/-- On every edge of `G − Z` the glued weight is `λ₀` (given the matching identity). -/
theorem glue_of_edge {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H lab F α)
    (hH4 : HingeCond H lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) (lamH lam0 : Sym2 V → ℝ)
    (t : NRow (delG H Z) lab F → ℝ)
    (ht : ∀ e : NCol (delG H Z) lab F, S07V35.dat (natB (delG H Z) lab F) t e = lamH e - lam0 e)
    {e : Sym2 V} (heG : e ∈ (delG G Z).edgeSet) : glue G H lab F Z lamH lam0 t e = lam0 e := by
  unfold glue
  split_ifs with he
  · exact glue_overlap hα hH3 hH4 hn hZ lamH lam0 t ht he heG
  · rfl

/-- **Representation of `f` on all of `M_H`**: if `λ_H` represents `f`, so does `glue`. -/
theorem glue_represents (lamH lam0 : Sym2 V → ℝ) (t : NRow (delG H Z) lab F → ℝ)
    {x : Sym2 V → ℤ} (hx : IsLocalProfile H lab F x) :
    ∑ e, glue G H lab F Z lamH lam0 t e * (x e : ℝ) = ∑ e, lamH e * (x e : ℝ) := by
  have h1 : ∑ e, glue G H lab F Z lamH lam0 t e * (x e : ℝ) =
      ∑ e, (lamH e - rowField H lab F (liftPot H lab F Z t) e) * (x e : ℝ) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold glue
    split_ifs with he
    · rfl
    · rw [S07V38.localProfile_supp hx e he, Int.cast_zero, mul_zero, mul_zero]
    · rw [S07V38.localProfile_supp hx e he, Int.cast_zero, mul_zero, mul_zero]
  rw [h1]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [rowField_pairing_zero _ hx, sub_zero]

/-- Triangle sums of a functional that represents `f₀` and kills the lattice of `Gz`. -/
lemma triangle_sum_zero {K : SimpleGraph V} (lam0 : Sym2 V → ℝ)
    (f0 : localProfile K lab F →ₗ[ℤ] ℝ)
    (hrep : ∀ x : localProfile K lab F, ∑ e, lam0 e * (((x : Sym2 V → ℤ) e : ℤ) : ℝ) = f0 x)
    (hann : ∀ (x : Sym2 V → ℤ) (hx : x ∈ lattice K lab F),
      f0 ⟨x, lattice_le_localProfile K lab F hx⟩ = 0)
    {T : Finset V} (hT : IsAllowed K lab F T) : ∑ e ∈ triEdges T, lam0 e = 0 := by
  have hmem : ind (triEdges T) ∈ lattice K lab F := Submodule.subset_span ⟨T, hT, rfl⟩
  have := hrep ⟨ind (triEdges T), lattice_le_localProfile K lab F hmem⟩
  rw [hann _ hmem] at this
  rw [← this]
  simp only [ind]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun e => e ∈ triEdges T)]
  rw [Finset.sum_eq_zero (s := univ.filter fun e => e ∉ triEdges T) (fun e he => by
    rw [if_neg (Finset.mem_filter.1 he).2]; simp)]
  rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [if_pos he]; simp

omit [Fintype V] in
lemma card_triEdges_le {T : Finset V} (hT : T.card = 3) : (triEdges T).card ≤ 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
  rw [triEdges_triple hab hac hbc, wedge]
  exact (Finset.card_insert_le _ _).trans (by
    have := Finset.card_le_two (a := s(a, c)) (b := s(b, c)); omega)

/-- **The physical gluing lemma.** -/
theorem physical_gluing {α : ℝ} {h : ℕ} (hα : 0 < α) (hHG : H ≤ G)
    (hH3 : CommonNbrCond H lab F α) (hH4 : HingeCond H lab F α h)
    (hn : n1Of α ≤ Fintype.card V) (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V)
    {A : ℝ} (hA : 0 ≤ A)
    (f : localProfile H lab F →ₗ[ℤ] ℝ) (f0 : localProfile (delG G Z) lab F →ₗ[ℤ] ℝ)
    (hf : ∀ x : localProfile H lab F, |f x| ≤ A * ∑ e, |(((x : Sym2 V → ℤ) e : ℤ) : ℝ)|)
    (hf0 : ∀ x : localProfile (delG G Z) lab F,
      |f0 x| ≤ A * ∑ e, |(((x : Sym2 V → ℤ) e : ℤ) : ℝ)|)
    (hagree : ∀ (x : Sym2 V → ℤ) (hx : x ∈ localProfile (delG H Z) lab F),
      f ⟨x, localProfile_delG_le H Z hx⟩ = f0 ⟨x, localProfile_mono (delG_mono hHG Z) hx⟩)
    (hann : ∀ (x : Sym2 V → ℤ) (hx : x ∈ lattice (delG G Z) lab F),
      f0 ⟨x, lattice_le_localProfile (delG G Z) lab F hx⟩ = 0) :
    ∃ (lamH lam0 : Sym2 V → ℝ) (t : NRow (delG H Z) lab F → ℝ) (lam : Sym2 V → ℝ),
      lam = glue G H lab F Z lamH lam0 t ∧
      (∀ e, |lamH e| ≤ A) ∧ (∀ e, |lam0 e| ≤ A) ∧ (∀ i, |t i| ≤ (6 / α ^ 2 + 1) * (2 * A)) ∧
      (∀ x : localProfile H lab F, ∑ e, lamH e * (((x : Sym2 V → ℤ) e : ℤ) : ℝ) = f x) ∧
      (∀ x : localProfile (delG G Z) lab F,
        ∑ e, lam0 e * (((x : Sym2 V → ℤ) e : ℤ) : ℝ) = f0 x) ∧
      (∀ e : NCol (delG H Z) lab F,
        S07V35.dat (natB (delG H Z) lab F) t e = lamH e - lam0 e) ∧
      (∀ e, |lam e| ≤ glueConst α A) ∧
      (∀ x : localProfile H lab F, ∑ e, lam e * (((x : Sym2 V → ℤ) e : ℤ) : ℝ) = f x) ∧
      (∀ e, IsNCol H lab F e → lam e = lamH e - rowField H lab F (liftPot H lab F Z t) e) ∧
      (∀ e, e ∈ (delG G Z).edgeSet → lam e = lam0 e) ∧
      (∀ e, ¬ IsNCol H lab F e → e ∉ (delG G Z).edgeSet → lam e = 0) ∧
      (∀ T, IsAllowed (delG G Z) lab F T → ∑ e ∈ triEdges T, lam e = 0) ∧
      (∀ T, IsAllowed G lab F T →
        |∑ e ∈ triEdges T, lam e| ≤ 3 * glueConst α A * (T ∩ Z).card) := by
  obtain ⟨lamH, hlamH, hrepH⟩ := S07V38.bounded_extension _ f hA hf
  obtain ⟨lam0, hlam0, hrep0⟩ := S07V38.bounded_extension _ f0 hA hf0
  -- the matching potential on `J = H − Z`
  have hagreeJ : ∀ x : Sym2 V → ℤ, IsLocalProfile (delG H Z) lab F x →
      ∑ e : NCol (delG H Z) lab F, lamH e.1 * (x e.1 : ℝ) =
        ∑ e : NCol (delG H Z) lab F, lam0 e.1 * (x e.1 : ℝ) := by
    intro x hx
    rw [sum_ncol_profile hx lamH, sum_ncol_profile hx lam0]
    have h1 := hrepH ⟨x, localProfile_delG_le H Z hx⟩
    have h2 := hrep0 ⟨x, localProfile_mono (delG_mono hHG Z) hx⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hagree x hx
  obtain ⟨t, ht, htb⟩ := matching_potential_delG hα hH3 hZ (fun e => lam0 e.1)
    (fun e => lamH e.1) hA (fun e => hlam0 _) (fun e => hlamH _) hagreeJ
  set Tb := (6 / α ^ 2 + 1) * (2 * A) with hTb
  have hTb0 : 0 ≤ Tb := by positivity
  have hC : glueConst α A = A + 2 * Tb := by unfold glueConst; rw [hTb]; ring
  have hCA : A ≤ glueConst α A := by rw [hC]; linarith
  have hC0 : 0 ≤ glueConst α A := hA.trans hCA
  -- bound
  have hbound : ∀ e, |glue G H lab F Z lamH lam0 t e| ≤ glueConst α A := by
    intro e
    unfold glue
    split_ifs with he he'
    · have h1 := rowField_abs_le (liftPot H lab F Z t) hTb0 (liftPot_abs_le t hTb0 htb) e
      calc |lamH e - rowField H lab F (liftPot H lab F Z t) e|
          ≤ |lamH e| + |rowField H lab F (liftPot H lab F Z t) e| := abs_sub _ _
        _ ≤ A + 2 * Tb := by linarith [hlamH e]
        _ = glueConst α A := hC.symm
    · exact (hlam0 e).trans hCA
    · rw [abs_zero]; exact hC0
  have hedge : ∀ e, e ∈ (delG G Z).edgeSet → glue G H lab F Z lamH lam0 t e = lam0 e :=
    fun e he => glue_of_edge hα hH3 hH4 hn hZ lamH lam0 t ht he
  have htri : ∀ T, IsAllowed (delG G Z) lab F T →
      ∑ e ∈ triEdges T, glue G H lab F Z lamH lam0 t e = 0 := by
    intro T hT
    rw [Finset.sum_congr rfl fun e he => hedge e (by
      have := mem_edges_of_mem_triEdges (delG G Z) lab F hT he
      rwa [mem_edges] at this)]
    exact triangle_sum_zero lam0 f0 hrep0 hann hT
  refine ⟨lamH, lam0, t, _, rfl, hlamH, hlam0, htb, hrepH, hrep0, ht, hbound, fun x => ?_,
    fun e he => by unfold glue; rw [if_pos he], hedge,
    fun e he he' => by unfold glue; rw [if_neg he, if_neg he'], htri, fun T hT => ?_⟩
  · rw [glue_represents lamH lam0 t x.2]; exact hrepH x
  · by_cases hTZ : ∀ x ∈ T, x ∉ Z
    · rw [htri T (allowed_delG_iff.2 ⟨hT, hTZ⟩), abs_zero]; positivity
    · push_neg at hTZ
      obtain ⟨z, hzT, hzZ⟩ := hTZ
      have hcard : (1 : ℝ) ≤ (T ∩ Z).card := by
        exact_mod_cast Finset.card_pos.2 ⟨z, Finset.mem_inter.2 ⟨hzT, hzZ⟩⟩
      calc |∑ e ∈ triEdges T, glue G H lab F Z lamH lam0 t e|
          ≤ ∑ e ∈ triEdges T, |glue G H lab F Z lamH lam0 t e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _e ∈ triEdges T, glueConst α A := Finset.sum_le_sum fun e _ => hbound e
        _ = (triEdges T).card * glueConst α A := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * glueConst α A := by
          have : ((triEdges T).card : ℝ) ≤ 3 := by exact_mod_cast card_triEdges_le hT.1
          exact mul_le_mul_of_nonneg_right this hC0
        _ ≤ 3 * glueConst α A * (T ∩ Z).card := by
          have : 0 ≤ 3 * glueConst α A := by positivity
          nlinarith

end S07V39
