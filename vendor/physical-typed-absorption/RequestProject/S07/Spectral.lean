/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V24 / S07 §1: degree-weighted Cheeger inequality and two-sided contraction

Finite graph `H` on a finite type `V`. All objects are explicit finite sums over `V`:

* `aw v w ∈ {0,1}` adjacency weight, `dg v = Σ_w aw v w` (= `H.degree v`),
* `ip f g = Σ_v dg v * f v * g v` (the degree-weighted inner product, i.e. `L²(π)` up to
  the factor `vol V`),
* `Pop` the random-walk operator `(Pop f) v = (Σ_w aw v w f w) / dg v`,
* `energy f = Σ_v Σ_w aw v w (f v - f w)^2` (ordered pairs, i.e. twice the Dirichlet form),
* `bdry S = Σ_{v ∈ S} Σ_{w ∉ S} aw v w` (number of cut edges).

Results:

* `coarea_ineq` (discrete co-area, by peeling the minimum level): if every set of volume at most
  half has `κ vol S ≤ bdry S`, then `2κ Σ dg h ≤ Σ Σ aw |h v - h w|` for every `h ≥ 0` whose
  support has volume at most half.
* `exists_weighted_median`.
* `poincare` (Cheeger with a WEIGHTED median): `ip f 1 = 0 → κ² ip f f ≤ energy f`.
* `contraction`: if moreover `σ = ±1` is a proper 2-colouring, then on
  `W = {f : ip f 1 = 0, ip f σ = 0}` the operator `Pop` maps `W` to itself and
  `ip (Pop f) (Pop f) ≤ (1 - κ²/2)² ip f f`. Both exact directions `1` and `σ`
  (eigenvalues `+1` and `-1`) are removed and handled separately.

No geometric input is used here.
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- adjacency weight -/
noncomputable def aw (v w : V) : ℝ := if H.Adj v w then 1 else 0

/-- degree as a real number -/
noncomputable def dg (v : V) : ℝ := ∑ w, aw H v w

/-- degree-weighted inner product -/
noncomputable def ip (f g : V → ℝ) : ℝ := ∑ v, dg H v * f v * g v

/-- volume of a vertex set -/
noncomputable def vol (S : Finset V) : ℝ := ∑ v ∈ S, dg H v

/-- number of cut edges (real) -/
noncomputable def bdry [DecidableEq V] (S : Finset V) : ℝ := ∑ v ∈ S, ∑ w ∈ univ \ S, aw H v w

/-- Dirichlet energy over ordered pairs -/
noncomputable def energy (f : V → ℝ) : ℝ := ∑ v, ∑ w, aw H v w * (f v - f w) ^ 2

/-- signless energy over ordered pairs -/
noncomputable def energyP (f : V → ℝ) : ℝ := ∑ v, ∑ w, aw H v w * (f v + f w) ^ 2

/-- the random-walk operator `D⁻¹ A` -/
noncomputable def Pop : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f v := (∑ w, aw H v w * f w) / dg H v
  map_add' f g := by
    ext v; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    ext v; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_div_assoc', Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro w _; ring

variable {H}

omit [Fintype V] in
lemma aw_nonneg (v w : V) : 0 ≤ aw H v w := by unfold aw; split_ifs <;> norm_num

omit [Fintype V] in
lemma aw_le_one (v w : V) : aw H v w ≤ 1 := by unfold aw; split_ifs <;> norm_num

omit [Fintype V] in
lemma aw_symm (v w : V) : aw H v w = aw H w v := by
  unfold aw; simp only [H.adj_comm]

omit [Fintype V] in
lemma aw_sq (v w : V) : aw H v w ^ 2 = aw H v w := by unfold aw; split_ifs <;> norm_num

omit [Fintype V] in
lemma aw_self (v : V) : aw H v v = 0 := by unfold aw; simp

lemma dg_nonneg (v : V) : 0 ≤ dg H v := Finset.sum_nonneg fun w _ => aw_nonneg v w

lemma dg_eq_degree (v : V) : dg H v = H.degree v := by
  unfold dg aw
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

lemma Pop_apply (f : V → ℝ) (v : V) : Pop H f v = (∑ w, aw H v w * f w) / dg H v := rfl

lemma vol_nonneg (S : Finset V) : 0 ≤ vol H S := Finset.sum_nonneg fun v _ => dg_nonneg v

lemma vol_mono {S T : Finset V} (h : S ⊆ T) : vol H S ≤ vol H T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun v _ _ => dg_nonneg v

lemma vol_compl [DecidableEq V] (S : Finset V) : vol H (univ \ S) = vol H univ - vol H S := by
  unfold vol
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]

/-! ### Bilinearity of `ip` -/

lemma ip_comm (f g : V → ℝ) : ip H f g = ip H g f := by
  unfold ip; apply Finset.sum_congr rfl; intro v _; ring

lemma ip_add_left (f g h : V → ℝ) : ip H (f + g) h = ip H f h + ip H g h := by
  unfold ip; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro v _
  simp only [Pi.add_apply]; ring

lemma ip_add_right (f g h : V → ℝ) : ip H h (f + g) = ip H h f + ip H h g := by
  rw [ip_comm, ip_add_left, ip_comm f, ip_comm g]

lemma ip_sub_left (f g h : V → ℝ) : ip H (f - g) h = ip H f h - ip H g h := by
  unfold ip; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro v _
  simp only [Pi.sub_apply]; ring

lemma ip_sub_right (f g h : V → ℝ) : ip H h (f - g) = ip H h f - ip H h g := by
  rw [ip_comm, ip_sub_left, ip_comm f, ip_comm g]

lemma ip_smul_left (r : ℝ) (f g : V → ℝ) : ip H (r • f) g = r * ip H f g := by
  unfold ip; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma ip_smul_right (r : ℝ) (f g : V → ℝ) : ip H g (r • f) = r * ip H g f := by
  rw [ip_comm, ip_smul_left, ip_comm]

lemma ip_self_nonneg (f : V → ℝ) : 0 ≤ ip H f f := by
  unfold ip; apply Finset.sum_nonneg; intro v _
  have := dg_nonneg (H := H) v
  have : 0 ≤ f v * f v := mul_self_nonneg _
  nlinarith

/-- `ip f (Pop g)` is the adjacency form (requires positive degrees). -/
lemma ip_Pop (hdg : ∀ v, 0 < dg H v) (f g : V → ℝ) :
    ip H f (Pop H g) = ∑ v, ∑ w, aw H v w * f v * g w := by
  unfold ip; apply Finset.sum_congr rfl; intro v _
  rw [Pop_apply]
  have hv := (hdg v).ne'
  rw [show dg H v * f v * ((∑ w, aw H v w * g w) / dg H v) = f v * ∑ w, aw H v w * g w by
    field_simp]
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring

lemma adj_form_symm (f g : V → ℝ) :
    ∑ v, ∑ w, aw H v w * f v * g w = ∑ v, ∑ w, aw H v w * g v * f w := by
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl
  intro w _; rw [aw_symm]; ring

lemma ip_Pop_symm (hdg : ∀ v, 0 < dg H v) (f g : V → ℝ) :
    ip H f (Pop H g) = ip H g (Pop H f) := by
  rw [ip_Pop hdg, ip_Pop hdg, adj_form_symm]

/-- double sum of `aw * F v` is the degree-weighted sum -/
lemma sum_aw_left (F : V → ℝ) : ∑ v, ∑ w, aw H v w * F v = ∑ v, dg H v * F v := by
  apply Finset.sum_congr rfl; intro v _; rw [dg, Finset.sum_mul]

lemma sum_aw_right (F : V → ℝ) : ∑ v, ∑ w, aw H v w * F w = ∑ v, dg H v * F v := by
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro w _; rw [dg, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro v _; rw [aw_symm]

lemma energy_eq (hdg : ∀ v, 0 < dg H v) (f : V → ℝ) :
    energy H f = 2 * (ip H f f - ip H f (Pop H f)) := by
  rw [ip_Pop hdg]
  have h1 := sum_aw_left (H := H) (fun v => f v ^ 2)
  have h2 := sum_aw_right (H := H) (fun v => f v ^ 2)
  have : energy H f = ∑ v, ∑ w, aw H v w * f v ^ 2 + ∑ v, ∑ w, aw H v w * f w ^ 2
      - 2 * ∑ v, ∑ w, aw H v w * f v * f w := by
    unfold energy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro v _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro w _; ring
  have e : ∑ v, dg H v * f v * f v = ∑ v, dg H v * f v ^ 2 := by
    apply Finset.sum_congr rfl; intro v _; ring
  rw [this, h1, h2]; unfold ip; rw [e]; ring

lemma energyP_eq (hdg : ∀ v, 0 < dg H v) (f : V → ℝ) :
    energyP H f = 2 * (ip H f f + ip H f (Pop H f)) := by
  rw [ip_Pop hdg]
  have h1 := sum_aw_left (H := H) (fun v => f v ^ 2)
  have h2 := sum_aw_right (H := H) (fun v => f v ^ 2)
  have : energyP H f = ∑ v, ∑ w, aw H v w * f v ^ 2 + ∑ v, ∑ w, aw H v w * f w ^ 2
      + 2 * ∑ v, ∑ w, aw H v w * f v * f w := by
    unfold energyP
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _; ring
  have e : ∑ v, dg H v * f v * f v = ∑ v, dg H v * f v ^ 2 := by
    apply Finset.sum_congr rfl; intro v _; ring
  rw [this, h1, h2]; unfold ip; rw [e]; ring

lemma energy_nonneg (f : V → ℝ) : 0 ≤ energy H f := by
  unfold energy; apply Finset.sum_nonneg; intro v _; apply Finset.sum_nonneg; intro w _
  exact mul_nonneg (aw_nonneg v w) (sq_nonneg _)

end S07V24
