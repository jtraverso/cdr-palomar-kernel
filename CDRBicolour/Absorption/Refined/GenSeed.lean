/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.GenResidual
public import CDRBicolour.Absorption.ResidualSeed

/-!
# Residual H1 from a bounded right inverse: any labels, approximate base seed

The argument of `residual_seed_of_bri` with the label type, the allowed family `F` and the
weight `w` of the functional `ℓ_w(d) = Σ_e w(e) d(e)` abstracted (`w` must vanish on every allowed
triangle), and with an **approximate** seed of the complete host: `μ₀` has the right size on the
allowed triangles and covers every edge up to an error `η`.

`gen_residual_seed`: with a bounded right inverse `Φ` of the incidence operator on `ker ℓ_w`
(constant `K`), `ℓ_w(𝟏) = 0`, a packing `P` of allowed triangles whose leave has degree `≤ Δ`, and
`8 K C₀² Δ + 4 K C₀ η n ≤ n`, the residual host has an exact diffuse seed with constant `2 C₀`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Refined

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

section Gen

variable {V I : Type*} [Fintype V] [DecidableEq V] (lab : V → I) (F : Set (Multiset I))
  (w : Sym2 V → ℝ)

/-- The complete host with labels `lab`. -/
abbrev cHostG : Host V I := ⟨⊤, lab⟩

/-- Allowed triangles of the complete host. -/
abbrev triG : Finset (Finset V) := allowed (cHostG lab) F

/-- Incidence operator. -/
def MincG : (Finset V → ℝ) →ₗ[ℝ] (E0 V → ℝ) where
  toFun c e := ∑ T ∈ (triG lab F).filter (fun T => e.1 ∈ triEdges T), c T
  map_add' c c' := by ext e; simp [sum_add_distrib]
  map_smul' r c := by ext e; simp [mul_sum]

/-- The functional `ℓ_w`. -/
def ellG' : (E0 V → ℝ) →ₗ[ℝ] ℝ where
  toFun d := ∑ e, w e.1 * d e
  map_add' d d' := by simp [mul_add, sum_add_distrib]
  map_smul' r d := by simp [mul_sum, mul_left_comm]

/-- A bounded right inverse of the incidence operator on `ker ℓ_w`. -/
structure BRIG (K : ℝ) where
  Φ : (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ)
  exact : ∀ d, ellG' w d = 0 → MincG lab F (Φ d) = d
  bound : ∀ d, ellG' w d = 0 → ∀ T, |Φ d T| ≤ K / Fintype.card V * ‖d‖

end Gen

section GenReduction

variable {V I : Type*} [Fintype V] [DecidableEq V] {lab : V → I} {F : Set (Multiset I)}
  {w : Sym2 V → ℝ} (L : Finset (Sym2 V))

theorem gell_M (hw : ∀ T ∈ triG lab F, ∑ f ∈ triEdges T, w f = 0) (c : Finset V → ℝ) :
    ellG' w (MincG lab F c) = 0 := by
  simp only [ellG', MincG, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_eq_zero fun T hT => ?_
  have : ∀ e : E0 V, (if e.1 ∈ triEdges T then w e.1 * c T else 0) =
      (if e.1 ∈ triEdges T then w e.1 else 0) * c T := by
    intro e; split_ifs <;> simp
  simp_rw [this, ← sum_mul]
  rw [sum_E0 w (triEdges T) (triEdges_nondiag T), hw T hT, zero_mul]

theorem gMinc_bm_apply (c : Finset V → ℝ) (e : E0 V) :
    MincG lab F (bm L c) e = ∑ T ∈ (triG lab F).filter (fun T => e.1 ∈ triEdges T),
      (if Disjoint (triEdges T) L then 0 else c T) := rfl

theorem gMinc_bm_of_mem (c : Finset V → ℝ) (e : E0 V) (he : e.1 ∈ L) :
    MincG lab F (bm L c) e = MincG lab F c e := by
  rw [gMinc_bm_apply]
  refine sum_congr rfl fun T hT => ?_
  rw [if_neg (not_disjoint_of_mem L (mem_filter.mp hT).2 he)]

theorem gmem_tri {T : Finset V} : T ∈ triG lab F ↔ IsAllowed (cHostG lab) F T := by
  classical
  unfold triG allowed; simp

theorem gbad_card {u v : V} (huv : u ≠ v) (hL : s(u, v) ∉ L) :
    #((triG lab F).filter fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L) ≤
      degL L u + degL L v := by
  have hsub : ((triG lab F).filter fun T => s(u, v) ∈ triEdges T ∧
      ¬ Disjoint (triEdges T) L) ⊆ (nbL L u ∪ nbL L v).image fun w => ({u, v, w} : Finset V) := by
    intro T hT
    obtain ⟨hTt, he, hbad⟩ := mem_filter.mp hT
    have hA : IsAllowed (cHostG lab) F T := gmem_tri.mp hTt
    have huvT : u ∈ T ∧ v ∈ T := by
      simpa [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, huv] using he
    obtain ⟨x, hxu, hxv, rfl⟩ := third_vertex hA.1 huv huvT.1 huvT.2
    rw [triEdges_triple huv hxu.symm hxv.symm] at hbad
    rw [not_disjoint_iff] at hbad
    obtain ⟨f, hf, hfL⟩ := hbad
    simp only [mem_insert, mem_singleton] at hf
    refine mem_image.mpr ⟨x, ?_, rfl⟩
    rcases hf with rfl | rfl | rfl
    · exact absurd hfL hL
    · exact mem_union_left _ (by simp [nbL, Sym2.eq_swap, hfL])
    · exact mem_union_right _ (by simp [nbL, Sym2.eq_swap, hfL])
  calc _ ≤ #((nbL L u ∪ nbL L v).image fun w => ({u, v, w} : Finset V)) := card_le_card hsub
    _ ≤ #(nbL L u ∪ nbL L v) := card_image_le
    _ ≤ #(nbL L u) + #(nbL L v) := card_union_le _ _
    _ = degL L u + degL L v := rfl

theorem gMinc_indP (P : Finset (Finset V)) (hP : ∀ T ∈ P, T ∈ triG lab F)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) (e : E0 V) :
    MincG lab F (fun T => if T ∈ P then 1 else 0) e =
      if e.1 ∈ P.biUnion triEdges then 1 else 0 := by
  simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
  have hset : (triG lab F).filter (fun T => e.1 ∈ triEdges T) ∩ P =
      P.filter fun T => e.1 ∈ triEdges T := by
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

theorem gbad_sum_le {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (c : Finset V → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hc : ∀ T ∈ triG lab F, |c T| ≤ r) (e : E0 V) (he : e.1 ∉ L) :
    |MincG lab F (bm L c) e| ≤ 2 * Δ * r := by
  rw [gMinc_bm_apply]
  have : ∀ T, (if Disjoint (triEdges T) L then (0 : ℝ) else c T) =
      if ¬ Disjoint (triEdges T) L then c T else 0 := fun T => by split_ifs <;> rfl
  simp_rw [this]
  rw [← sum_filter, filter_filter]
  rcases e with ⟨e, hed⟩
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := by simpa using hed
  have hcard := gbad_card (lab := lab) (F := F) L huv he
  have hc2 : (#((triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧
      ¬ Disjoint (triEdges T) L)) : ℝ) ≤ 2 * Δ := by
    have h1 := hdeg u; have h2 := hdeg v
    have : #((triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧
        ¬ Disjoint (triEdges T) L)) ≤ 2 * Δ := by omega
    exact_mod_cast this
  calc |∑ T ∈ (triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L), c T|
      ≤ ∑ T ∈ (triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L),
          |c T| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ (triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L),
          r := sum_le_sum fun T hT => hc T (mem_filter.mp hT).1
    _ = #((triG lab F).filter (fun T => s(u, v) ∈ triEdges T ∧ ¬ Disjoint (triEdges T) L)) * r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * Δ * r := mul_le_mul_of_nonneg_right hc2 hr

theorem gmem_allowed {T : Finset V} :
    T ∈ allowed (gHost lab L) F ↔ IsAllowed (gHost lab L) F T := by
  classical
  unfold allowed; simp

theorem gallowed_iff {T : Finset V} :
    IsAllowed (gHost lab L) F T ↔ T ∈ triG lab F ∧ Disjoint (triEdges T) L := by
  constructor
  · intro hT
    refine ⟨gmem_tri.mpr ⟨hT.1, fun x _ y _ hxy => hxy, hT.2.2⟩, ?_⟩
    rw [disjoint_left]
    intro f hf hfL
    induction f using Sym2.ind with
    | _ x y =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hf
    have := hT.2.1 x hf.1.1 y hf.1.2 hf.2
    rw [rG_adj] at this
    exact this.1 hfL
  · rintro ⟨hT, hD⟩
    have hA : IsAllowed (cHostG lab) F T := gmem_tri.mp hT
    refine ⟨hA.1, fun x hx y hy hxy => ?_, hA.2.2⟩
    rw [rG_adj]
    refine ⟨fun hL => disjoint_left.mp hD ?_ hL, hxy⟩
    simp [triEdges, mem_filter, hx, hy, hxy]

/-- **Residual H1 from a bounded right inverse and an approximate complete seed**, with the form
of the seed: `μ = gm L (μ₀ + ψ)` and `|ψ| ≤ (K/n)·2(2Δ C₀/n + η)`. -/
theorem gen_residual_seed' (hw : ∀ T ∈ triG lab F, ∑ f ∈ triEdges T, w f = 0)
    {K C₀ η : ℝ} (hK : 0 ≤ K) (hC₀ : 1 ≤ C₀) (hη : 0 ≤ η) (B : BRIG lab F w K)
    (hell1 : ellG' w (fun _ => 1) = 0) {μ₀ : Finset V → ℝ}
    (hμ₀ : ∀ T ∈ triG lab F, 1 / (C₀ * Fintype.card V) ≤ μ₀ T ∧ μ₀ T ≤ C₀ / Fintype.card V)
    (hdef : ∀ e : E0 V, |MincG lab F μ₀ e - 1| ≤ η)
    (indP : Finset V → ℝ) (hρ : ∀ e : E0 V, MincG lab F indP e = if e.1 ∈ L then 1 else 0)
    {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hV : 0 < Fintype.card V)
    (hΔ : 8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * Fintype.card V ≤ Fintype.card V) :
    ∃ μ ψ : Finset V → ℝ, IsDiffuseSeed (gHost lab L) F (2 * C₀) μ ∧ μ = gm L (μ₀ + ψ) ∧
      ∀ T, |ψ T| ≤ K / Fintype.card V * (2 * (2 * Δ * (C₀ / Fintype.card V) + η)) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := Nat.cast_pos.mpr hV
  have hC0 : 0 < C₀ := by linarith
  have hμ₀b : ∀ T ∈ triG lab F, |μ₀ T| ≤ C₀ / n := by
    intro T hT
    obtain ⟨h1, h2⟩ := hμ₀ T hT
    rw [abs_of_nonneg (le_trans (by positivity) h1)]
    exact h2
  -- the deficit
  set d0 : E0 V → ℝ := MincG lab F (bm L μ₀ - indP) + ((fun _ => 1) - MincG lab F μ₀) with hd0
  have hd0ell : ellG' w d0 = 0 := by
    rw [hd0]; simp only [map_add, map_sub, gell_M hw, hell1]; ring
  have hd0L : ∀ e : E0 V, e.1 ∈ L → d0 e = 0 := by
    intro e he
    simp only [hd0, map_sub, Pi.add_apply, Pi.sub_apply]
    rw [gMinc_bm_of_mem L μ₀ e he, hρ e, if_pos he]; ring
  have hd0G : ∀ e : E0 V, e.1 ∉ L →
      d0 e = MincG lab F (bm L μ₀) e + (1 - MincG lab F μ₀ e) := by
    intro e he
    simp only [hd0, map_sub, Pi.add_apply, Pi.sub_apply]
    rw [hρ e, if_neg he, sub_zero]
  have hd0n : ‖d0‖ ≤ 2 * Δ * (C₀ / n) + η := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hd0L e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs, hd0G e he]
      have h1 := gbad_sum_le L hdeg μ₀ (by positivity) hμ₀b e he
      have h2 := hdef e
      rw [abs_sub_comm] at h2
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- the subspace and the operator
  let W0 : Submodule ℝ (E0 V → ℝ) :=
    { carrier := {x | ellG' w x = 0 ∧ ∀ e : E0 V, e.1 ∈ L → x e = 0}
      add_mem' := fun {x y} hx hy => ⟨by rw [map_add, hx.1, hy.1, add_zero],
        fun e he => by simp [hx.2 e he, hy.2 e he]⟩
      zero_mem' := ⟨map_zero _, fun e _ => rfl⟩
      smul_mem' := fun r x hx => ⟨by rw [map_smul, hx.1, smul_zero],
        fun e he => by simp [hx.2 e he]⟩ }
  let R : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := MincG lab F ∘ₗ bm L ∘ₗ B.Φ
  have hRL : ∀ x ∈ W0, ∀ e : E0 V, e.1 ∈ L → R x e = 0 := by
    intro x hx e he
    show MincG lab F (bm L (B.Φ x)) e = 0
    rw [gMinc_bm_of_mem L _ e he, B.exact x hx.1]
    exact hx.2 e he
  have hW : ∀ x ∈ W0, R x ∈ W0 := fun x hx => ⟨gell_M hw _, hRL x hx⟩
  have hΔR : (8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * n : ℝ) ≤ n := by
    simp only [hn]; exact_mod_cast hΔ
  have hKΔ : 0 ≤ K * Δ := by positivity
  have hKη : 0 ≤ K * C₀ * η * n := by positivity
  have h4 : 4 * K * Δ ≤ n := by
    have h1 : (1 : ℝ) ≤ C₀ ^ 2 := by nlinarith
    have h2 : K * Δ ≤ K * Δ * C₀ ^ 2 := le_mul_of_one_le_right hKΔ h1
    nlinarith
  have hR : ∀ x ∈ W0, ‖R x‖ ≤ ‖x‖ / 2 := by
    intro x hx
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
    by_cases he : e.1 ∈ L
    · rw [hRL x hx e he, norm_zero]; positivity
    · rw [Real.norm_eq_abs]
      have hb := gbad_sum_le (lab := lab) (F := F) L hdeg (B.Φ x) (r := K / n * ‖x‖)
        (by positivity) (fun T _ => B.bound x hx.1 T) e he
      calc |R x e| = |MincG lab F (bm L (B.Φ x)) e| := rfl
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
    have h2 : ‖x‖ ≤ 2 * (2 * Δ * (C₀ / n) + η) := hxn.trans (by linarith)
    have : K / n * ‖x‖ ≤ K / n * (2 * (2 * Δ * (C₀ / n) + η)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    refine hb.trans (this.trans ?_)
    rw [show K / n * (2 * (2 * Δ * (C₀ / n) + η)) =
        (8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * n) / (2 * C₀ * n * n) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hΔR (by positivity : (0 : ℝ) ≤ 2 * C₀ * n)
    linarith [this, show (1 : ℝ) * (2 * C₀ * n * n) = n * (2 * C₀ * n) by ring]
  -- the seed
  refine ⟨gm L (μ₀ + B.Φ x), B.Φ x, ⟨fun T hT => ?_, fun e he => ?_⟩, rfl, fun T => ?_⟩
  · obtain ⟨hTt, hD⟩ := (gallowed_iff L).mp hT
    obtain ⟨h1, h2⟩ := hμ₀ T hTt
    have hv : gm L (μ₀ + B.Φ x) T = μ₀ T + B.Φ x T := by
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk, if_pos hD, Pi.add_apply]
    rw [hv]
    obtain ⟨hp, hp'⟩ := abs_le.mp (hΦx T)
    have e1 : 1 / (2 * C₀ * n) = 1 / (C₀ * n) - 1 / (2 * C₀ * n) := by field_simp; ring
    have e2 : 1 / (2 * C₀ * n) ≤ C₀ / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      have h2C : (1 : ℝ) ≤ 2 * C₀ * C₀ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2C hn0.le]
    constructor
    · rw [show 1 / (2 * C₀ * n) = 1 / ((2 * C₀) * n) by ring] at e1 hp; linarith
    · have : 2 * C₀ / n = C₀ / n + C₀ / n := by ring
      linarith
  · have hnd : ¬ e.IsDiag := by
      induction e using Sym2.ind with
      | _ u v => rw [Sym2.mk_isDiag_iff]; exact (rG_adj.mp he).2
    have heL : e ∉ L := by
      induction e using Sym2.ind with
      | _ u v => exact (rG_adj.mp he).1
    set e' : E0 V := ⟨e, hnd⟩
    have hkey : MincG lab F (gm L (μ₀ + B.Φ x)) e' = 1 := by
      have hg : ∀ c, MincG lab F (gm L c) e' = MincG lab F c e' - MincG lab F (bm L c) e' := by
        intro c
        have := congrArg (fun c => MincG lab F c e') (gm_add_bm L c)
        simp only [map_add, Pi.add_apply] at this
        linarith
      rw [map_add, map_add, Pi.add_apply, hg, hg]
      have hx1 : MincG lab F (B.Φ x) e' = x e' := by rw [B.exact x hxW.1]
      have hx2 : x e' - R x e' = d0 e' := by rw [← hxe]; rfl
      have hx3 : R x e' = MincG lab F (bm L (B.Φ x)) e' := rfl
      rw [hx1, ← hx3, hx2, hd0G e' heL]
      ring
    rw [← hkey]
    simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
    apply sum_subset
    · intro T hT
      simp only [mem_filter] at hT ⊢
      exact ⟨((gallowed_iff L).mp ((gmem_allowed L).mp hT.1)).1, hT.2⟩
    · intro T hT hTn
      simp only [mem_filter] at hT hTn
      simp only [gm, LinearMap.coe_mk, AddHom.coe_mk]
      rw [if_neg]
      intro hD
      exact hTn ⟨(gmem_allowed L).mpr ((gallowed_iff L).mpr ⟨hT.1, hD⟩), hT.2⟩
  · exact (B.bound x hxW.1 T).trans
      (mul_le_mul_of_nonneg_left (hxn.trans (by linarith)) (by positivity))

/-- **Residual H1 from a bounded right inverse and an approximate complete seed.** -/
theorem gen_residual_seed (hw : ∀ T ∈ triG lab F, ∑ f ∈ triEdges T, w f = 0)
    {K C₀ η : ℝ} (hK : 0 ≤ K) (hC₀ : 1 ≤ C₀) (hη : 0 ≤ η) (B : BRIG lab F w K)
    (hell1 : ellG' w (fun _ => 1) = 0) {μ₀ : Finset V → ℝ}
    (hμ₀ : ∀ T ∈ triG lab F, 1 / (C₀ * Fintype.card V) ≤ μ₀ T ∧ μ₀ T ≤ C₀ / Fintype.card V)
    (hdef : ∀ e : E0 V, |MincG lab F μ₀ e - 1| ≤ η)
    (indP : Finset V → ℝ) (hρ : ∀ e : E0 V, MincG lab F indP e = if e.1 ∈ L then 1 else 0)
    {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hV : 0 < Fintype.card V)
    (hΔ : 8 * K * C₀ ^ 2 * Δ + 4 * K * C₀ * η * Fintype.card V ≤ Fintype.card V) :
    ∃ μ, IsDiffuseSeed (gHost lab L) F (2 * C₀) μ := by
  obtain ⟨μ, -, hμ, -, -⟩ :=
    gen_residual_seed' L hw hK hC₀ hη B hell1 hμ₀ hdef indP hρ hdeg hV hΔ
  exact ⟨μ, hμ⟩

end GenReduction

end CDRBicolour.Absorption.Refined