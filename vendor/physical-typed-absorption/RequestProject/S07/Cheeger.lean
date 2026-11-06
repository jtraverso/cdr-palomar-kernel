/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.Spectral

@[expose] public section

/-!
# V24 / S07 §1: co-area, weighted median, Poincaré and two-sided contraction

See `RequestProject/S07/Spectral.lean` for the definitions. The argument is the one of S07 §1
(= S03 §7 with a degree-weighted median): conductance `κ` (in volume form) gives
`energy f ≥ κ² ip f f` for `ip f 1 = 0`, i.e. normalized gap `g = κ²/2`.
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- indicator of a finset as a real function -/
noncomputable def ind (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

lemma cut_sum_eq (S : Finset V) :
    ∑ v, ∑ w, aw H v w * |ind S v - ind S w| = 2 * bdry H S := by
  have key : ∀ v w, aw H v w * |ind S v - ind S w| =
      aw H v w * (ind S v * (1 - ind S w)) + aw H w v * (ind S w * (1 - ind S v)) := by
    intro v w; rw [aw_symm w v]; unfold ind; split_ifs <;> norm_num
  have hb : ∑ v, ∑ w, aw H v w * (ind S v * (1 - ind S w)) = bdry H S := by
    unfold bdry
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · apply Finset.sum_congr rfl; intro v hv
      rw [← Finset.sum_subset (Finset.subset_univ (univ \ S))]
      · apply Finset.sum_congr rfl; intro w hw
        simp only [Finset.mem_sdiff] at hw
        unfold ind; simp [hv, hw.2]
      · intro w _ hw
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hw
        unfold ind; simp [hw]
    · intro v _ hv
      apply Finset.sum_eq_zero; intro w _; unfold ind; simp [hv]
  simp_rw [key, Finset.sum_add_distrib]
  rw [hb, Finset.sum_comm (f := fun v w => aw H w v * (ind S w * (1 - ind S v))), hb]; ring

lemma sum_dg_ind (S : Finset V) : ∑ v, dg H v * ind S v = vol H S := by
  unfold ind vol
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- discrete co-area inequality, proved by peeling the minimal positive level. -/
theorem coarea_ineq {κ : ℝ}
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S) :
    ∀ h : V → ℝ, (∀ v, 0 ≤ h v) → 2 * vol H (univ.filter fun v => 0 < h v) ≤ vol H univ →
      2 * κ * ∑ v, dg H v * h v ≤ ∑ v, ∑ w, aw H v w * |h v - h w| := by
  suffices H' : ∀ k : ℕ, ∀ h : V → ℝ, (univ.filter fun v => 0 < h v).card = k →
      (∀ v, 0 ≤ h v) → 2 * vol H (univ.filter fun v => 0 < h v) ≤ vol H univ →
      2 * κ * ∑ v, dg H v * h v ≤ ∑ v, ∑ w, aw H v w * |h v - h w| by
    intro h h0 hs; exact H' _ h rfl h0 hs
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro h hk h0 hs
  set S := univ.filter fun v => 0 < h v with hSdef
  have hout : ∀ v, v ∉ S → h v = 0 := by
    intro v hv; simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    exact le_antisymm hv (h0 v)
  rcases S.eq_empty_or_nonempty with hS | hS
  · have : ∀ v, h v = 0 := fun v => hout v (by simp [hS])
    simp only [this, mul_zero, Finset.sum_const_zero, sub_self, abs_zero]; rfl
  set μ := S.inf' hS h with hμ
  obtain ⟨v₀, hv₀S, hv₀⟩ := Finset.exists_mem_eq_inf' hS h
  have hμle : ∀ v ∈ S, μ ≤ h v := fun v hv => Finset.inf'_le h hv
  have hpos : ∀ v ∈ S, 0 < h v := by
    intro v hv; simpa [hSdef] using hv
  have hμpos : 0 < μ := by rw [← hμ] at hv₀; rw [hv₀]; exact hpos v₀ hv₀S
  set h' : V → ℝ := fun v => if v ∈ S then h v - μ else 0 with hh'
  have h'0 : ∀ v, 0 ≤ h' v := by
    intro v; simp only [hh']; split_ifs with hv
    · linarith [hμle v hv]
    · exact le_refl _
  have hsupp' : (univ.filter fun v => 0 < h' v) ⊆ S.erase v₀ := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hh'] at hv
    split_ifs at hv with hvS
    · rw [Finset.mem_erase]; refine ⟨?_, hvS⟩
      rintro rfl; rw [← hμ] at hv₀; linarith
    · exact absurd hv (lt_irrefl 0)
  have hcard : (univ.filter fun v => 0 < h' v).card < k := by
    rw [← hk]
    exact lt_of_le_of_lt (Finset.card_le_card hsupp') (Finset.card_erase_lt_of_mem hv₀S)
  have hs' : 2 * vol H (univ.filter fun v => 0 < h' v) ≤ vol H univ := by
    have := vol_mono (H := H) (hsupp'.trans (Finset.erase_subset _ _))
    linarith
  have IH := ih _ hcard h' rfl h'0 hs'
  have hpt : ∀ v w, |h v - h w| = μ * |ind S v - ind S w| + |h' v - h' w| := by
    intro v w
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · simp only [hh', ind, hv, hw, if_true, sub_self, abs_zero, mul_zero, zero_add]
      congr 1; ring
    · simp only [hh', ind, hv, hw, if_true, if_false, sub_zero, hout w hw,
        abs_of_pos (hpos v hv), abs_of_nonneg (show (0:ℝ) ≤ h v - μ by linarith [hμle v hv]),
        abs_one]; ring
    · simp only [hh', ind, hv, hw, if_true, if_false, zero_sub, hout v hv, abs_neg, abs_one,
        abs_of_pos (hpos w hw), abs_of_nonneg (show (0:ℝ) ≤ h w - μ by linarith [hμle w hw])]
      ring
    · simp only [hh', ind, hv, hw, if_false, sub_self, abs_zero, mul_zero, zero_add,
        hout v hv, hout w hw]
  have hpt2 : ∀ v, h v = μ * ind S v + h' v := by
    intro v; by_cases hv : v ∈ S
    · simp only [hh', ind, hv, if_true]; ring
    · simp only [hh', ind, hv, if_false, hout v hv]; ring
  have hsum : ∑ v, dg H v * h v = μ * vol H S + ∑ v, dg H v * h' v := by
    rw [← sum_dg_ind, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _; rw [hpt2 v]; ring
  have hcut := cut_sum_eq (H := H) S
  have hS2 := hexp S hs
  have hrhs : ∑ v, ∑ w, aw H v w * |h v - h w| =
      μ * ∑ v, ∑ w, aw H v w * |ind S v - ind S w| + ∑ v, ∑ w, aw H v w * |h' v - h' w| := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro v _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro w _
    rw [hpt v w]; ring
  rw [hsum, hrhs, hcut]
  nlinarith [mul_le_mul_of_nonneg_left hS2 hμpos.le]

/-- existence of a degree-weighted median -/
theorem exists_weighted_median (f : V → ℝ) : ∃ m : ℝ,
    2 * vol H (univ.filter fun v => m < f v) ≤ vol H univ ∧
    2 * vol H (univ.filter fun v => f v < m) ≤ vol H univ := by
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨0, ?_, ?_⟩ <;> simp [vol, Finset.univ_eq_empty]
  set T := univ.filter fun v => 2 * vol H (univ.filter fun w => f v < f w) ≤ vol H univ
    with hTdef
  have hT : T.Nonempty := by
    obtain ⟨v, -, hv⟩ := Finset.exists_max_image univ f univ_nonempty
    refine ⟨v, ?_⟩
    simp only [hTdef, mem_filter, mem_univ, true_and]
    have : (univ.filter fun w => f v < f w) = ∅ := by
      ext w; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
      exact hv w (mem_univ _)
    rw [this]; simp only [vol, Finset.sum_empty, mul_zero]; exact vol_nonneg _
  obtain ⟨v₀, hv₀T, hmin⟩ := Finset.exists_min_image T f hT
  refine ⟨f v₀, (mem_filter.1 hv₀T).2, ?_⟩
  by_contra hlt; push_neg at hlt
  set L := univ.filter fun w => f w < f v₀ with hLdef
  have hL : L.Nonempty := by
    by_contra hL; rw [Finset.not_nonempty_iff_eq_empty] at hL; rw [hL] at hlt
    simp only [vol, Finset.sum_empty, mul_zero] at hlt
    linarith [Finset.sum_nonneg fun v (_ : v ∈ univ) => dg_nonneg (H := H) v]
  obtain ⟨w₀, hw₀L, hwmax⟩ := Finset.exists_max_image L f hL
  have hw : f w₀ < f v₀ := (mem_filter.1 hw₀L).2
  have heq : (univ.filter fun w => f w₀ < f w) = univ \ L := by
    ext u; simp only [hLdef, mem_filter, mem_univ, true_and, mem_sdiff, not_lt]
    constructor
    · intro h; by_contra h'; push_neg at h'
      have := hwmax u (by simp [hLdef, h']); linarith
    · intro h; linarith
  have hw₀T : w₀ ∈ T := by
    simp only [hTdef, mem_filter, mem_univ, true_and]; rw [heq, vol_compl]; linarith
  have := hmin w₀ hw₀T; linarith

omit [DecidableEq V] in
/-- Cauchy–Schwarz for double sums -/
lemma double_sum_cs (F G : V → V → ℝ) :
    (∑ v, ∑ w, F v w * G v w) ^ 2 ≤ (∑ v, ∑ w, F v w ^ 2) * (∑ v, ∑ w, G v w ^ 2) := by
  have e : ∀ K : V → V → ℝ, ∑ v, ∑ w, K v w = ∑ p ∈ univ ×ˢ univ, K p.1 p.2 := by
    intro K; rw [Finset.sum_product]
  rw [e (fun v w => F v w * G v w), e (fun v w => F v w ^ 2), e (fun v w => G v w ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq V] in
lemma energyP_le (h : V → ℝ) : energyP H h ≤ 4 * ip H h h := by
  have h1 := sum_aw_left (H := H) (fun v => h v ^ 2)
  have h2 := sum_aw_right (H := H) (fun v => h v ^ 2)
  have : energyP H h ≤ ∑ v, ∑ w, (2 * (aw H v w * h v ^ 2) + 2 * (aw H v w * h w ^ 2)) := by
    unfold energyP; apply Finset.sum_le_sum; intro v _; apply Finset.sum_le_sum; intro w _
    have := aw_nonneg (H := H) v w
    nlinarith [sq_nonneg (h v - h w), mul_nonneg this (sq_nonneg (h v - h w))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  rw [h1, h2] at this
  have e : ip H h h = ∑ v, dg H v * h v ^ 2 := by
    unfold ip; apply Finset.sum_congr rfl; intro v _; ring
  rw [e]; linarith

/-- the Cheeger step for one signed part -/
theorem energy_ge_of_half {κ : ℝ} (hκ : 0 ≤ κ)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (h : V → ℝ) (h0 : ∀ v, 0 ≤ h v)
    (hs : 2 * vol H (univ.filter fun v => 0 < h v) ≤ vol H univ) :
    κ ^ 2 * ip H h h ≤ energy H h := by
  have hfil : (univ.filter fun v => 0 < (fun v => h v ^ 2) v) =
      univ.filter fun v => 0 < h v := by
    apply Finset.filter_congr; intro v _
    constructor
    · intro hv; rcases (h0 v).lt_or_eq with h' | h'
      · exact h'
      · simp [← h'] at hv
    · intro hv; exact pow_pos hv 2
  have hc := coarea_ineq hexp (fun v => h v ^ 2) (fun v => sq_nonneg _) (by rw [hfil]; exact hs)
  have hip : ∑ v, dg H v * (fun v => h v ^ 2) v = ip H h h := by
    unfold ip; apply Finset.sum_congr rfl; intro v _; ring
  rw [hip] at hc
  set X := ∑ v, ∑ w, aw H v w * |(fun v => h v ^ 2) v - (fun v => h v ^ 2) w|
  have hX : X = ∑ v, ∑ w, (aw H v w * |h v - h w|) * (aw H v w * |h v + h w|) := by
    apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _
    have : h v ^ 2 - h w ^ 2 = (h v - h w) * (h v + h w) := by ring
    simp only [this, abs_mul]
    have ha := aw_sq (H := H) v w
    rw [show aw H v w * |h v - h w| * (aw H v w * |h v + h w|) =
      aw H v w ^ 2 * (|h v - h w| * |h v + h w|) by ring, ha]
  have hCS := double_sum_cs (fun v w => aw H v w * |h v - h w|)
    (fun v w => aw H v w * |h v + h w|)
  have e1 : ∑ v, ∑ w, (aw H v w * |h v - h w|) ^ 2 = energy H h := by
    unfold energy; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _
    rw [mul_pow, aw_sq, sq_abs]
  have e2 : ∑ v, ∑ w, (aw H v w * |h v + h w|) ^ 2 = energyP H h := by
    unfold energyP; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _
    rw [mul_pow, aw_sq, sq_abs]
  rw [← hX, e1, e2] at hCS
  have hP := energyP_le (H := H) h
  have hip0 := ip_self_nonneg (H := H) h
  have hE0 := energy_nonneg (H := H) h
  have hsq : (2 * κ * ip H h h) ^ 2 ≤ X ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hc
  rcases hip0.lt_or_eq with hpos | hzero
  · have : 4 * (κ ^ 2 * ip H h h) * ip H h h ≤ 4 * energy H h * ip H h h := by
      nlinarith [mul_le_mul_of_nonneg_left hP hE0]
    nlinarith
  · rw [← hzero]; simpa using hE0

/-- **Poincaré inequality from edge expansion (Cheeger with a weighted median).** -/
theorem poincare {κ : ℝ} (hκ : 0 ≤ κ)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (f : V → ℝ) (hf : ip H f (fun _ => 1) = 0) :
    κ ^ 2 * ip H f f ≤ energy H f := by
  obtain ⟨m, hm1, hm2⟩ := exists_weighted_median (H := H) f
  set fp : V → ℝ := fun v => max (f v - m) 0
  set fm : V → ℝ := fun v => max (m - f v) 0
  have sp : (univ.filter fun v => 0 < fp v) = univ.filter fun v => m < f v := by
    apply Finset.filter_congr; intro v _; simp [fp]
  have sm : (univ.filter fun v => 0 < fm v) = univ.filter fun v => f v < m := by
    apply Finset.filter_congr; intro v _; simp [fm]
  have e1 := energy_ge_of_half hκ hexp fp (fun v => le_max_right _ _) (by rw [sp]; exact hm1)
  have e2 := energy_ge_of_half hκ hexp fm (fun v => le_max_right _ _) (by rw [sm]; exact hm2)
  have hsplit : energy H fp + energy H fm ≤ energy H f := by
    unfold energy; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro v _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro w _
    have ha := aw_nonneg (H := H) v w
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ ha
    simp only [fp, fm]
    rcases le_total (f v) m with h1 | h1 <;> rcases le_total (f w) m with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, h1, h2] <;> nlinarith
  have hip : ip H f f ≤ ip H fp fp + ip H fm fm := by
    have hsum : ∑ v, dg H v * f v = 0 := by
      rw [← hf]; unfold ip; apply Finset.sum_congr rfl; intro v _; ring
    have : ip H fp fp + ip H fm fm =
        ip H f f - 2 * m * (∑ v, dg H v * f v) + m ^ 2 * ∑ v, dg H v := by
      unfold ip; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      simp only [fp, fm]
      rcases le_total (f v) m with h1 | h1 <;>
      simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, h1] <;> ring
    rw [this, hsum]
    have := Finset.sum_nonneg fun v (_ : v ∈ univ) => dg_nonneg (H := H) v
    nlinarith [sq_nonneg m]
  have hk2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  nlinarith [mul_le_mul_of_nonneg_left hip hk2]

/-! ### Two-sided contraction off the exact directions `1` and `σ` -/

/-- the invariant subspace orthogonal to both exact directions -/
def InW (σ : V → ℝ) (f : V → ℝ) : Prop := ip H f (fun _ => 1) = 0 ∧ ip H f σ = 0

omit [DecidableEq V] in
lemma Pop_one (hdg : ∀ v, 0 < dg H v) : Pop H (fun _ => (1 : ℝ)) = fun _ => 1 := by
  ext v; rw [Pop_apply]; simp only [mul_one]; exact div_self (hdg v).ne'

omit [DecidableEq V] in
lemma Pop_sigma (hdg : ∀ v, 0 < dg H v) (σ : V → ℝ)
    (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) : Pop H σ = -σ := by
  ext v; rw [Pop_apply]
  have : ∑ w, aw H v w * σ w = ∑ w, aw H v w * (-σ v) := by
    apply Finset.sum_congr rfl; intro w _; unfold aw; split_ifs with h
    · rw [hσadj v w h]
    · simp
  rw [this, ← Finset.sum_mul, ← dg]; simp only [Pi.neg_apply]; field_simp [(hdg v).ne']

omit [DecidableEq V] in
lemma energy_sigma (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1)
    (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) (f : V → ℝ) :
    energy H (fun v => σ v * f v) = energyP H f := by
  unfold energy energyP; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl
  intro w _; unfold aw; split_ifs with h
  · dsimp only; rw [hσadj v w h]; have := hσ v; nlinarith [this]
  · simp

omit [DecidableEq V] in
lemma ip_sigma_sq (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) (f : V → ℝ) :
    ip H (fun v => σ v * f v) (fun v => σ v * f v) = ip H f f := by
  unfold ip; apply Finset.sum_congr rfl; intro v _; have := hσ v
  calc dg H v * (σ v * f v) * (σ v * f v) = dg H v * f v * f v * σ v ^ 2 := by ring
    _ = _ := by rw [this, mul_one]

omit [DecidableEq V] in
lemma ip_sigma_one (σ : V → ℝ) (f : V → ℝ) :
    ip H (fun v => σ v * f v) (fun _ => 1) = ip H f σ := by
  unfold ip; apply Finset.sum_congr rfl; intro v _; ring

/-- `|⟨f, P f⟩| ≤ (1 - κ²/2) ⟨f, f⟩` on `W`. -/
theorem quad_bound (hdg : ∀ v, 0 < dg H v) {κ : ℝ} (hκ : 0 ≤ κ)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) (hσadj : ∀ v w, H.Adj v w → σ w = -σ v)
    (f : V → ℝ) (hf : InW (H := H) σ f) :
    |ip H f (Pop H f)| ≤ (1 - κ ^ 2 / 2) * ip H f f := by
  have p1 := poincare hκ hexp f hf.1
  have p2 := poincare hκ hexp (fun v => σ v * f v) (by rw [ip_sigma_one]; exact hf.2)
  rw [energy_eq hdg] at p1
  rw [energy_sigma σ hσ hσadj, energyP_eq hdg, ip_sigma_sq σ hσ] at p2
  rw [abs_le]; constructor <;> nlinarith

omit [DecidableEq V] in
theorem Pop_mem_W (hdg : ∀ v, 0 < dg H v) (σ : V → ℝ)
    (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) (f : V → ℝ) (hf : InW (H := H) σ f) :
    InW (H := H) σ (Pop H f) := by
  constructor
  · rw [ip_comm, ip_Pop_symm hdg, Pop_one hdg]; exact hf.1
  · rw [ip_comm, ip_Pop_symm hdg, Pop_sigma hdg σ hσadj]
    have : ip H f (-σ) = -ip H f σ := by
      unfold ip; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro v _
      simp only [Pi.neg_apply]; ring
    rw [this, hf.2, neg_zero]

omit [DecidableEq V] in
lemma InW_add (σ : V → ℝ) {f g : V → ℝ} (hf : InW (H := H) σ f) (hg : InW (H := H) σ g) :
    InW (H := H) σ (f + g) :=
  ⟨by rw [ip_add_left, hf.1, hg.1, add_zero], by rw [ip_add_left, hf.2, hg.2, add_zero]⟩

omit [DecidableEq V] in
lemma InW_sub (σ : V → ℝ) {f g : V → ℝ} (hf : InW (H := H) σ f) (hg : InW (H := H) σ g) :
    InW (H := H) σ (f - g) :=
  ⟨by rw [ip_sub_left, hf.1, hg.1, sub_zero], by rw [ip_sub_left, hf.2, hg.2, sub_zero]⟩

omit [DecidableEq V] in
lemma InW_smul (σ : V → ℝ) (r : ℝ) {f : V → ℝ} (hf : InW (H := H) σ f) :
    InW (H := H) σ (r • f) :=
  ⟨by rw [ip_smul_left, hf.1, mul_zero], by rw [ip_smul_left, hf.2, mul_zero]⟩

/-- **Two-sided contraction**: `‖P f‖² ≤ (1 - κ²/2)² ‖f‖²` on `W` (polarization). -/
theorem contraction (hdg : ∀ v, 0 < dg H v) {κ : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ ^ 2 < 2)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) (hσadj : ∀ v w, H.Adj v w → σ w = -σ v)
    (f : V → ℝ) (hf : InW (H := H) σ f) :
    ip H (Pop H f) (Pop H f) ≤ (1 - κ ^ 2 / 2) ^ 2 * ip H f f := by
  set l := 1 - κ ^ 2 / 2 with hl
  have hlpos : 0 < l := by rw [hl]; linarith
  set h := Pop H f with hhdef
  have hh := Pop_mem_W hdg σ hσadj f hf
  have hu1 := InW_add σ (InW_smul σ l hf) hh
  have hu2 := InW_sub σ (InW_smul σ l hf) hh
  have q1 := (abs_le.1 (quad_bound hdg hκ hexp σ hσ hσadj _ hu1)).2
  have q2 := (abs_le.1 (quad_bound hdg hκ hexp σ hσ hσadj _ hu2)).1
  have hb : ip H f (Pop H h) = ip H h h := by rw [ip_Pop_symm hdg]
  have hc : ip H h f = ip H f h := ip_comm _ _
  simp only [map_add, map_sub, map_smul, ip_add_left, ip_add_right, ip_sub_left, ip_sub_right,
    ip_smul_left, ip_smul_right, ← hhdef, hb, hc] at q1 q2
  rw [← hl] at q1 q2
  have key : 2 * l * ip H h h ≤ 2 * l * (l ^ 2 * ip H f f) := by linarith
  exact le_of_mul_le_mul_left key (by linarith)

/-- iterated contraction -/
theorem iter_contraction (hdg : ∀ v, 0 < dg H v) {κ : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ ^ 2 < 2)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) :
    ∀ k : ℕ, ∀ f : V → ℝ, InW (H := H) σ f →
      InW (H := H) σ ((Pop H ^ k) f) ∧
      ip H ((Pop H ^ k) f) ((Pop H ^ k) f) ≤ ((1 - κ ^ 2 / 2) ^ 2) ^ k * ip H f f := by
  intro k
  induction k with
  | zero => intro f hf; simp only [pow_zero, Module.End.one_apply, one_mul]; exact ⟨hf, le_rfl⟩
  | succ k ih =>
    intro f hf
    have e : (Pop H ^ (k + 1)) f = (Pop H ^ k) (Pop H f) := by
      rw [pow_succ, Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := ih (Pop H f) (Pop_mem_W hdg σ hσadj f hf)
    refine ⟨e ▸ h1, ?_⟩
    rw [e]
    have hc := contraction hdg hκ hκ2 hexp σ hσ hσadj f hf
    have hpow : 0 ≤ ((1 - κ ^ 2 / 2) ^ 2) ^ k := by positivity
    calc _ ≤ ((1 - κ ^ 2 / 2) ^ 2) ^ k * ip H (Pop H f) (Pop H f) := h2
      _ ≤ ((1 - κ ^ 2 / 2) ^ 2) ^ k * ((1 - κ ^ 2 / 2) ^ 2 * ip H f f) :=
          mul_le_mul_of_nonneg_left hc hpow
      _ = _ := by ring

end S07V24
