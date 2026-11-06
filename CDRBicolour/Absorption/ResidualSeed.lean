/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.ResidualHinge

/-!
# H1 for residual hosts, from a bounded right inverse (backlog item 2a)

`M` is the incidence operator of the allowed (bicoloured) triangles of the complete labelled
graph, from triangle weights to edge weights (`E0` = non-diagonal pairs), and
`ℓ d = ∑_{bichromatic} d - 2 ∑_{monochromatic} d`.  Every bicoloured triangle has one
monochromatic and two bichromatic edges, so `ℓ ∘ M = 0` (`ell_M`).

A **bounded right inverse** with constant `K` (`BRI`) is a linear `Φ` with `M (Φ d) = d` for
`ℓ d = 0` and `|Φ d T| ≤ K ‖d‖∞ / n`.  (Numerically, the minimal-norm inverse has `K ≈ 16`.)

**Reduction** (`residual_seed_of_bri`).  Let `μ₀` be a diffuse seed of the complete host
(constant `C₀`), `P` a packing of allowed triangles with leave `L` of maximum degree `Δ`, and
`8 K C₀² Δ ≤ n`.  Bad triangles (meeting `L`) are discarded; the deficit `d₀` (at most
`2 Δ C₀ / n` per edge, zero on `L`, `ℓ d₀ = 0`) is corrected by `1_good · Φ x`, where `x` solves
`x - R x = d₀` with `R x = M (1_bad · Φ x)`.  `R` preserves `W₀ = {ℓ = 0, zero on L}` (on an
edge of `L` every triangle is bad, so `R x = M Φ x = x = 0` there) and has norm `≤ 2ΔK/n ≤ 1/2`
on `W₀`; so `I - R` is injective, hence surjective, on the finite-dimensional `W₀`.  The result
is a diffuse seed of the residual host with constant `2 C₀`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-! ### An abstract solvability lemma -/

/-- If `R` preserves a subspace `W` of `ι → ℝ` and halves sup norms on it, then `x - R x = d`
has a solution `x ∈ W` with `‖x‖ ≤ 2 ‖d‖` for every `d ∈ W`. -/
theorem solve_contraction {ι : Type*} [Fintype ι] (W : Submodule ℝ (ι → ℝ))
    (R : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hW : ∀ x ∈ W, R x ∈ W)
    (hR : ∀ x ∈ W, ‖R x‖ ≤ ‖x‖ / 2) {d : ι → ℝ} (hd : d ∈ W) :
    ∃ x ∈ W, x - R x = d ∧ ‖x‖ ≤ 2 * ‖d‖ := by
  set g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.id - R with hg
  have hf : ∀ x ∈ W, g x ∈ W := fun x hx => by
    simp only [hg, LinearMap.sub_apply, LinearMap.id_apply]; exact W.sub_mem hx (hW x hx)
  set f : W →ₗ[ℝ] W := g.restrict hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : (x : ι → ℝ) - R x = 0 := by
      have := congrArg Subtype.val hx
      simpa [f, g, LinearMap.restrict_apply] using this
    have hxR : (x : ι → ℝ) = R x := sub_eq_zero.mp h0
    have := hR x x.2
    rw [← hxR] at this
    have hn : ‖(x : ι → ℝ)‖ = 0 := by linarith [norm_nonneg (x : ι → ℝ)]
    exact Subtype.ext (norm_eq_zero.mp hn)
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨d, hd⟩
  have hxd : (x : ι → ℝ) - R x = d := by
    have := congrArg Subtype.val hx
    simpa [f, g, LinearMap.restrict_apply] using this
  refine ⟨x, x.2, hxd, ?_⟩
  have h1 : (x : ι → ℝ) = d + R x := by rw [← hxd]; abel
  have h2 : ‖(x : ι → ℝ)‖ ≤ ‖d‖ + ‖R x‖ := by
    conv_lhs => rw [h1]
    exact norm_add_le _ _
  have h3 := hR x x.2
  linarith

/-! ### The incidence operator and the functional `ℓ` -/

section Incidence

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-- Non-diagonal pairs. -/
abbrev E0 (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

/-- The allowed triangles of the complete host. -/
abbrev tri : Finset (Finset V) := allowed (cHost lab) cdrF

/-- Incidence operator: triangle weights to edge weights. -/
def Minc : (Finset V → ℝ) →ₗ[ℝ] (E0 V → ℝ) where
  toFun c e := ∑ T ∈ (tri lab).filter (fun T => e.1 ∈ triEdges T), c T
  map_add' c c' := by ext e; simp [sum_add_distrib]
  map_smul' r c := by ext e; simp [mul_sum]

/-- Weight of an edge in `ℓ`: `1` if bichromatic, `-2` if monochromatic. -/
def wl (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => if lab u = lab v then (-2 : ℝ) else 1, fun u v => by simp [eq_comm]⟩ e

/-- The functional `ℓ`. -/
def ell : (E0 V → ℝ) →ₗ[ℝ] ℝ where
  toFun d := ∑ e, wl lab e.1 * d e
  map_add' d d' := by simp [mul_add, sum_add_distrib]
  map_smul' r d := by simp [mul_sum, mul_left_comm]

/-- A bounded right inverse of the incidence operator on `ker ℓ`. -/
structure BRI (K : ℝ) where
  Φ : (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ)
  exact : ∀ d, ell lab d = 0 → Minc lab (Φ d) = d
  bound : ∀ d, ell lab d = 0 → ∀ T, |Φ d T| ≤ K / Fintype.card V * ‖d‖

end Incidence

/-! ### `ℓ ∘ M = 0` -/

section Ell

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem sum_E0 (F : Sym2 V → ℝ) (S : Finset (Sym2 V)) (hS : ∀ f ∈ S, ¬ f.IsDiag) :
    ∑ e : E0 V, (if e.1 ∈ S then F e.1 else 0) = ∑ f ∈ S, F f := by
  rw [← Finset.sum_subtype (univ.filter fun f : Sym2 V => ¬ f.IsDiag) (by simp)
    (fun f => if f ∈ S then F f else 0), sum_ite_mem]
  congr 1
  ext f
  simp only [mem_inter, mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hS f h, h⟩⟩

theorem triEdges_nondiag (T : Finset V) : ∀ f ∈ triEdges T, ¬ f.IsDiag := by
  intro f hf
  simp only [triEdges, mem_filter] at hf
  exact hf.2

theorem wl_tri {T : Finset V} (hT : T ∈ tri lab) : ∑ f ∈ triEdges T, wl lab f = 0 := by
  have hA : IsAllowed (cHost lab) cdrF T := by
    classical
    unfold tri allowed at hT; exact (mem_filter.mp hT).2
  obtain ⟨h3, -, hF⟩ := hA
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp h3
  have hlab : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({x, y, z} : Finset V).val.map lab ∈ cdrF := hF
    rwa [val_map_triple lab hxy hxz.symm hyz.symm] at this
  rw [triEdges_triple hxy hxz hyz, sum_insert (by simp [hyz, hxz]),
    sum_insert (by simp [hxy, hxz]), sum_singleton]
  simp only [wl, Sym2.lift_mk]
  rcases cdrF_cases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, if_neg (by rw [← h1]; exact h2)]; norm_num
  · rw [if_neg h2, if_pos h1, if_neg (fun h => h2 (h1.trans h.symm))]; norm_num
  · rw [if_neg h2, if_neg (by rw [← h1]; exact h2), if_pos h1]; norm_num

/-- **`ℓ` vanishes on the image of `M`.** -/
theorem ell_M (c : Finset V → ℝ) : ell lab (Minc lab c) = 0 := by
  simp only [ell, Minc, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_eq_zero fun T hT => ?_
  have : ∀ e : E0 V, (if e.1 ∈ triEdges T then wl lab e.1 * c T else 0) =
      (if e.1 ∈ triEdges T then wl lab e.1 else 0) * c T := by
    intro e; split_ifs <;> simp
  simp_rw [this, ← sum_mul]
  rw [sum_E0 (wl lab) (triEdges T) (triEdges_nondiag T), wl_tri hT, zero_mul]

end Ell

/-! ### The reduction -/

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} (L : Finset (Sym2 V))

/-- Keep the good triangles (edge-disjoint from `L`). -/
def gm : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c T := if Disjoint (triEdges T) L then c T else 0
  map_add' c c' := by ext T; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r c := by ext T; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- Keep the bad triangles. -/
def bm : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c T := if Disjoint (triEdges T) L then 0 else c T
  map_add' c c' := by ext T; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r c := by ext T; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

theorem gm_add_bm (c : Finset V → ℝ) : gm L c + bm L c = c := by
  ext T; simp only [gm, bm, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]; split_ifs <;> simp

theorem not_disjoint_of_mem {T : Finset V} {f : Sym2 V} (hf : f ∈ triEdges T) (hL : f ∈ L) :
    ¬ Disjoint (triEdges T) L := fun h => disjoint_left.mp h hf hL

theorem Minc_bm_apply (c : Finset V → ℝ) (e : E0 V) :
    Minc lab (bm L c) e = ∑ T ∈ (tri lab).filter (fun T => e.1 ∈ triEdges T),
      (if Disjoint (triEdges T) L then 0 else c T) := rfl

/-- On an edge of `L`, every triangle through it is bad. -/
theorem Minc_bm_of_mem (c : Finset V → ℝ) (e : E0 V) (he : e.1 ∈ L) :
    Minc lab (bm L c) e = Minc lab c e := by
  rw [Minc_bm_apply]
  refine sum_congr rfl fun T hT => ?_
  rw [if_neg (not_disjoint_of_mem L (mem_filter.mp hT).2 he)]

theorem third_vertex {T : Finset V} {u v : V} (h3 : T.card = 3) (huv : u ≠ v) (hu : u ∈ T)
    (hv : v ∈ T) : ∃ w, w ≠ u ∧ w ≠ v ∧ T = {u, v, w} := by
  have hR : ((T.erase u).erase v).card = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm huv, hv⟩), card_erase_of_mem hu, h3]
  obtain ⟨w, hw⟩ := card_eq_one.1 hR
  have hwm : w ∈ (T.erase u).erase v := by rw [hw]; exact mem_singleton_self w
  simp only [mem_erase] at hwm
  refine ⟨w, hwm.2.1, hwm.1, ?_⟩
  ext x
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr (Or.inl hxv)
    have : x ∈ (T.erase u).erase v := by simp [hx, hxu, hxv]
    rw [hw, mem_singleton] at this
    exact Or.inr (Or.inr this)
  · rintro (rfl | rfl | rfl)
    · exact hu
    · exact hv
    · exact hwm.2.2

/-- At most `deg u + deg v` bad triangles through a good edge `uv`. -/
theorem bad_card {u v : V} (huv : u ≠ v) (hL : s(u, v) ∉ L) :
    #((tri lab).filter fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L) ≤
      degL L u + degL L v := by
  have hsub : ((tri lab).filter fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L) ⊆
      (nbL L u ∪ nbL L v).image fun w => ({u, v, w} : Finset V) := by
    intro T hT
    obtain ⟨hTt, he, hbad⟩ := mem_filter.mp hT
    have hA : IsAllowed (cHost lab) cdrF T := by
      classical
      unfold tri allowed at hTt; exact (mem_filter.mp hTt).2
    have huvT : u ∈ T ∧ v ∈ T := by
      simpa [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, huv] using he
    obtain ⟨w, hwu, hwv, rfl⟩ := third_vertex hA.1 huv huvT.1 huvT.2
    rw [triEdges_triple huv hwu.symm hwv.symm] at hbad
    rw [not_disjoint_iff] at hbad
    obtain ⟨f, hf, hfL⟩ := hbad
    simp only [mem_insert, mem_singleton] at hf
    refine mem_image.mpr ⟨w, ?_, rfl⟩
    rcases hf with rfl | rfl | rfl
    · exact absurd hfL hL
    · exact mem_union_left _ (by simp [nbL, Sym2.eq_swap, hfL])
    · exact mem_union_right _ (by simp [nbL, Sym2.eq_swap, hfL])
  calc _ ≤ #((nbL L u ∪ nbL L v).image fun w => ({u, v, w} : Finset V)) := card_le_card hsub
    _ ≤ #(nbL L u ∪ nbL L v) := card_image_le
    _ ≤ #(nbL L u) + #(nbL L v) := card_union_le _ _
    _ = degL L u + degL L v := rfl

/-- The packing indicator is covered exactly by its edges. -/
theorem Minc_indP (P : Finset (Finset V)) (hP : ∀ T ∈ P, T ∈ tri lab)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) (e : E0 V) :
    Minc lab (fun T => if T ∈ P then 1 else 0) e = if e.1 ∈ P.biUnion triEdges then 1 else 0 := by
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
  have hset : (tri lab).filter (fun T => e.1 ∈ triEdges T) ∩ P = P.filter fun T => e.1 ∈ triEdges T := by
    ext T; simp only [mem_inter, mem_filter]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hP T h.1, h.2⟩, h.1⟩⟩
  rw [hset]
  split_ifs with he
  · obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
    rw [Nat.cast_eq_one, card_eq_one]
    refine ⟨T, ?_⟩
    ext T'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hT', heT'⟩
      by_contra hne
      exact disjoint_left.mp (hPd hT' hT hne) heT' heT
    · rintro rfl; exact ⟨hT, heT⟩
  · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro T hT heT
    exact he (mem_biUnion.mpr ⟨T, hT, heT⟩)

/-- Sums of bad triangles through a good edge. -/
theorem bad_sum_le {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (c : Finset V → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hc : ∀ T ∈ tri lab, |c T| ≤ r) (e : E0 V) (he : e.1 ∉ L) :
    |Minc lab (bm L c) e| ≤ 2 * Δ * r := by
  rw [Minc_bm_apply]
  have : ∀ T, (if Disjoint (triEdges T) L then (0 : ℝ) else c T) =
      if ¬ Disjoint (triEdges T) L then c T else 0 := fun T => by split_ifs <;> rfl
  simp_rw [this]
  rw [← sum_filter, filter_filter]
  rcases e with ⟨e, hed⟩
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := by simpa using hed
  have hcard := bad_card (lab := lab) L huv he
  have hc2 : (#((tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧
      ¬ Disjoint (triEdges T) L)) : ℝ) ≤ 2 * Δ := by
    have h1 := hdeg u; have h2 := hdeg v
    have : #((tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧
        ¬ Disjoint (triEdges T) L)) ≤ 2 * Δ := by omega
    exact_mod_cast this
  calc |∑ T ∈ (tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L), c T|
      ≤ ∑ T ∈ (tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L), |c T| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ (tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L), r :=
        sum_le_sum fun T hT => hc T (mem_filter.mp hT).1
    _ = #((tri lab).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L)) * r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * Δ * r := mul_le_mul_of_nonneg_right hc2 hr

theorem mem_tri {T : Finset V} : T ∈ tri lab ↔ IsAllowed (cHost lab) cdrF T := by
  classical
  unfold tri allowed; simp

theorem mem_allowed_rHost {T : Finset V} :
    T ∈ allowed (rHost lab L) cdrF ↔ IsAllowed (rHost lab L) cdrF T := by
  classical
  unfold allowed; simp

/-- Allowed triangles of the residual host are the good allowed triangles of the complete one. -/
theorem allowed_rHost_iff {T : Finset V} :
    IsAllowed (rHost lab L) cdrF T ↔ T ∈ tri lab ∧ Disjoint (triEdges T) L := by
  constructor
  · intro hT
    refine ⟨mem_tri.mpr ⟨hT.1, fun x _ y _ hxy => hxy, hT.2.2⟩, ?_⟩
    rw [disjoint_left]
    intro f hf hfL
    induction f using Sym2.ind with
    | _ x y =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hf
    have := hT.2.1 x hf.1.1 y hf.1.2 hf.2
    rw [rG_adj] at this
    exact this.1 hfL
  · rintro ⟨hT, hD⟩
    have hA : IsAllowed (cHost lab) cdrF T := mem_tri.mp hT
    refine ⟨hA.1, fun x hx y hy hxy => ?_, hA.2.2⟩
    rw [rG_adj]
    refine ⟨fun hL => disjoint_left.mp hD ?_ hL, hxy⟩
    simp [triEdges, mem_filter, hx, hy, hxy]

/-- **H1 for the residual host from a bounded right inverse.** -/
theorem residual_seed_of_bri {K C₀ : ℝ} (hK : 0 ≤ K) (hC₀ : 1 ≤ C₀) (B : BRI lab K)
    {μ₀ : Finset V → ℝ} (hμ₀ : IsDiffuseSeed (cHost lab) cdrF C₀ μ₀)
    (P : Finset (Finset V)) (hP : ∀ T ∈ P, T ∈ tri lab)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) {Δ : ℕ}
    (hdeg : ∀ p, degL (P.biUnion triEdges) p ≤ Δ) (hV : 0 < Fintype.card V)
    (hΔ : 8 * K * C₀ ^ 2 * Δ ≤ Fintype.card V) :
    ∃ μ, IsDiffuseSeed (rHost lab (P.biUnion triEdges)) cdrF (2 * C₀) μ := by
  set L := P.biUnion triEdges with hL
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := Nat.cast_pos.mpr hV
  have hC0 : 0 < C₀ := by linarith
  set indP : Finset V → ℝ := fun T => if T ∈ P then 1 else 0 with hindP
  -- the complete seed covers every edge once
  have hM0 : ∀ e : E0 V, Minc lab μ₀ e = 1 := by
    intro e
    have he : e.1 ∈ (cHost lab).G.edgeSet := by
      show e.1 ∈ (⊤ : SimpleGraph V).edgeSet
      rw [SimpleGraph.edgeSet_top]; exact e.2
    have := hμ₀.2 e.1 he
    simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
    convert this using 2
    ext T; simp only [mem_filter]
  have hμ₀b : ∀ T ∈ tri lab, |μ₀ T| ≤ C₀ / n := by
    intro T hT
    obtain ⟨h1, h2⟩ := hμ₀.1 T (mem_tri.mp hT)
    rw [abs_of_nonneg (le_trans (by positivity) h1)]
    exact h2
  -- the deficit
  set d0 := Minc lab (bm L μ₀ - indP) with hd0
  have hd0ell : ell lab d0 = 0 := ell_M _
  have hd0L : ∀ e : E0 V, e.1 ∈ L → d0 e = 0 := by
    intro e he
    simp only [hd0, map_sub, Pi.sub_apply]
    rw [Minc_bm_of_mem L μ₀ e he, hM0, Minc_indP P hP hPd e, if_pos he]; ring
  have hd0G : ∀ e : E0 V, e.1 ∉ L → d0 e = Minc lab (bm L μ₀) e := by
    intro e he
    simp only [hd0, map_sub, Pi.sub_apply]
    rw [Minc_indP P hP hPd e, if_neg he, sub_zero]
  have hd0n : ‖d0‖ ≤ 2 * Δ * (C₀ / n) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hd0L e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs, hd0G e he]
      exact bad_sum_le L hdeg μ₀ (by positivity) hμ₀b e he
  -- the subspace and the operator
  let W0 : Submodule ℝ (E0 V → ℝ) :=
    { carrier := {x | ell lab x = 0 ∧ ∀ e : E0 V, e.1 ∈ L → x e = 0}
      add_mem' := fun {x y} hx hy => ⟨by rw [map_add, hx.1, hy.1, add_zero],
        fun e he => by simp [hx.2 e he, hy.2 e he]⟩
      zero_mem' := ⟨map_zero _, fun e _ => rfl⟩
      smul_mem' := fun r x hx => ⟨by rw [map_smul, hx.1, smul_zero],
        fun e he => by simp [hx.2 e he]⟩ }
  let R : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := Minc lab ∘ₗ bm L ∘ₗ B.Φ
  have hRL : ∀ x ∈ W0, ∀ e : E0 V, e.1 ∈ L → R x e = 0 := by
    intro x hx e he
    show Minc lab (bm L (B.Φ x)) e = 0
    rw [Minc_bm_of_mem L _ e he, B.exact x hx.1]
    exact hx.2 e he
  have hW : ∀ x ∈ W0, R x ∈ W0 := fun x hx => ⟨ell_M _, hRL x hx⟩
  have hΔR : (8 * K * C₀ ^ 2 * Δ : ℝ) ≤ n := by simp only [hn]; exact_mod_cast hΔ
  have h4 : 4 * K * Δ ≤ n := by
    have h1 : (1 : ℝ) ≤ C₀ ^ 2 := by nlinarith
    have h5 : (0 : ℝ) ≤ K * Δ := by positivity
    have h2 : K * Δ ≤ K * Δ * C₀ ^ 2 := le_mul_of_one_le_right h5 h1
    nlinarith
  have hR : ∀ x ∈ W0, ‖R x‖ ≤ ‖x‖ / 2 := by
    intro x hx
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hRL x hx e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs]
      have hb := bad_sum_le (lab := lab) L hdeg (B.Φ x) (r := K / n * ‖x‖) (by positivity)
        (fun T _ => B.bound x hx.1 T) e he
      calc |R x e| = |Minc lab (bm L (B.Φ x)) e| := rfl
        _ ≤ 2 * Δ * (K / n * ‖x‖) := hb
        _ = (4 * K * Δ / n) * (‖x‖ / 2) := by ring
        _ ≤ 1 * (‖x‖ / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one hn0]; exact h4
        _ = ‖x‖ / 2 := one_mul _
  obtain ⟨x, hxW, hxe, hxn⟩ := solve_contraction W0 R hW hR (d := d0) ⟨hd0ell, hd0L⟩
  have hΦx : ∀ T, |B.Φ x T| ≤ 1 / (2 * C₀ * n) := by
    intro T
    have hb := B.bound x hxW.1 T
    have h2 : ‖x‖ ≤ 2 * (2 * Δ * (C₀ / n)) := hxn.trans (by linarith)
    have : K / n * ‖x‖ ≤ K / n * (2 * (2 * Δ * (C₀ / n))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    refine hb.trans (this.trans ?_)
    rw [show K / n * (2 * (2 * Δ * (C₀ / n))) = (8 * K * C₀ ^ 2 * Δ) / (2 * C₀ * n * n) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hΔR (by positivity : (0 : ℝ) ≤ 2 * C₀ * n)
    linarith [this, show (1 : ℝ) * (2 * C₀ * n * n) = n * (2 * C₀ * n) by ring]
  -- the seed
  refine ⟨gm L (μ₀ + B.Φ x), fun T hT => ?_, fun e he => ?_⟩
  · obtain ⟨hTt, hD⟩ := (allowed_rHost_iff L).mp hT
    obtain ⟨h1, h2⟩ := hμ₀.1 T (mem_tri.mp hTt)
    have hv : gm L (μ₀ + B.Φ x) T = μ₀ T + B.Φ x T := by
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk, if_pos hD, Pi.add_apply]
    rw [hv]
    obtain ⟨hp, hp'⟩ := abs_le.mp (hΦx T)
    have e1 : 1 / (2 * C₀ * n) = 1 / (C₀ * n) - 1 / (2 * C₀ * n) := by field_simp; ring
    have e2 : 1 / (2 * C₀ * n) ≤ C₀ / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      have h2C : (1 : ℝ) ≤ 2 * C₀ * C₀ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2C hn0.le]
    rw [← hn] at h1 h2 ⊢
    constructor
    · rw [show 1 / (2 * C₀ * n) = 1 / ((2 * C₀) * n) by ring] at e1 hp; linarith
    · have : 2 * C₀ / n = C₀ / n + C₀ / n := by ring
      linarith
  · -- edge sums
    have hnd : ¬ e.IsDiag := by
      induction e using Sym2.ind with
      | _ u v => rw [Sym2.mk_isDiag_iff]; exact (rG_adj.mp he).2
    have heL : e ∉ L := by
      induction e using Sym2.ind with
      | _ u v => exact (rG_adj.mp he).1
    set e' : E0 V := ⟨e, hnd⟩
    have hkey : Minc lab (gm L (μ₀ + B.Φ x)) e' = 1 := by
      have hg : ∀ c, Minc lab (gm L c) e' = Minc lab c e' - Minc lab (bm L c) e' := by
        intro c
        have := congrArg (fun c => Minc lab c e') (gm_add_bm L c)
        simp only [map_add, Pi.add_apply] at this
        linarith
      rw [map_add, map_add, Pi.add_apply, hg, hg, hM0]
      have hx1 : Minc lab (B.Φ x) e' = x e' := by rw [B.exact x hxW.1]
      have hx2 : x e' - R x e' = d0 e' := by rw [← hxe]; rfl
      have hx3 : R x e' = Minc lab (bm L (B.Φ x)) e' := rfl
      rw [hx1, ← hx3, hx2, hd0G e' heL]
      ring
    rw [← hkey]
    simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
    apply sum_subset
    · intro T hT
      simp only [mem_filter] at hT ⊢
      exact ⟨((allowed_rHost_iff L).mp ((mem_allowed_rHost L).mp hT.1)).1, hT.2⟩
    · intro T hT hTn
      simp only [mem_filter] at hT hTn
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk]
      rw [if_neg]
      intro hD
      exact hTn ⟨(mem_allowed_rHost L).mpr ((allowed_rHost_iff L).mpr ⟨hT.1, hD⟩), hT.2⟩

end Reduction

end CDRBicolour.Absorption
