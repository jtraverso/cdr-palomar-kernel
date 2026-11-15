/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.BRIk

/-!
# A bounded right inverse for the `k`-class bicolour host (part 2: gluing)

Fix a hub class `o`. The triples are the 3-sets of classes containing `o` (`Trip o`); each has an
increasing enumeration `sig o τ : Fin 3 → Fin k` and a three-class sub-host.

For `d ∈ ker ℓ`:
* `G0 τ d` gives each edge `e` the share `d e / N(e)` if `τ` contains `o` and the labels of `e`
  (`N(e)` is the number of such triples), so `Σ_τ G0 τ d = d` (`sum_G0`);
* `z0` is the uniform weight on the monochromatic edges of class `o`, which lie in every
  sub-host, with `ℓ z0 = -2`; `Gt τ d = G0 τ d + (ℓ(G0 τ d)/2) z0` has `ℓ = 0`, and
  `Σ_τ Gt τ d = d + (ℓ d / 2) z0 = d`;
* `PhiK = Σ_τ push ∘ Φ_τ ∘ restr ∘ Gt τ`, with `Φ_τ` a three-class bounded right inverse.

`briK`: if every class has at least `m ≥ max(512, 64 R³)` points and `n ≤ R m`, the `k`-class
host has a bounded right inverse (`BRIG`, functional `ℓ = wlk`) with constant
`#Trip · 400 R⁵ · R · (1 + 4R²)`, independent of `n`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The label set of an edge. -/
def lset (lab : V → Fin k) (e : Sym2 V) : Finset (Fin k) :=
  Sym2.lift ⟨fun u v => {lab u, lab v}, fun u v => pair_comm _ _⟩ e

theorem lset_mk (lab : V → Fin k) (u v : V) : lset lab s(u, v) = {lab u, lab v} := rfl

theorem card_lset_le (lab : V → Fin k) (e : Sym2 V) : #(lset lab e) ≤ 2 := by
  induction e using Sym2.ind with
  | _ u v => rw [lset_mk]; exact card_le_two

section Glue

variable (lab : V → Fin k) (o : Fin k)

/-- Triples of classes containing the hub `o`. -/
def Trip : Finset (Finset (Fin k)) := univ.filter (fun τ => τ.card = 3 ∧ o ∈ τ)

theorem mem_Trip {τ : Finset (Fin k)} (h : τ ∈ Trip o) : τ.card = 3 ∧ o ∈ τ := by
  simpa [Trip] using h

/-- Increasing enumeration of a triple. -/
def sig (τ : Finset (Fin k)) : Fin 3 → Fin k :=
  if h : τ.card = 3 then fun i => τ.orderEmbOfFin h i else fun _ => o

theorem sig_inj {τ : Finset (Fin k)} (h : τ.card = 3) : Function.Injective (sig o τ) := by
  unfold sig; rw [dif_pos h]; exact (τ.orderEmbOfFin h).injective

theorem mem_iff_sig {τ : Finset (Fin k)} (h : τ.card = 3) (x : Fin k) :
    x ∈ τ ↔ ∃ i, sig o τ i = x := by
  unfold sig; rw [dif_pos h]
  have hr := range_orderEmbOfFin τ h
  constructor
  · intro hx
    have : x ∈ Set.range (τ.orderEmbOfFin h) := by rw [hr]; exact hx
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    have : (τ.orderEmbOfFin h i) ∈ Set.range (τ.orderEmbOfFin h) := ⟨i, rfl⟩
    rw [hr] at this
    exact this

/-- Number of triples covering an edge. -/
def Ncov (e : Sym2 V) : ℕ := #((Trip o).filter (fun τ => insert o (lset lab e) ⊆ τ))

theorem Ncov_pos (hk : 3 ≤ k) (e : Sym2 V) : 0 < Ncov lab o e := by
  have hc : #(insert o (lset lab e)) ≤ 3 :=
    (card_insert_le _ _).trans (by have := card_lset_le lab e; omega)
  obtain ⟨t, h1, -, h3⟩ := exists_subsuperset_card_eq (subset_univ (insert o (lset lab e))) hc
    (by rw [card_univ, Fintype.card_fin]; exact hk)
  apply card_pos.2
  exact ⟨t, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, h3, h1 (mem_insert_self _ _)⟩, h1⟩⟩

/-- The share of a triple. -/
def G0 (τ : Finset (Fin k)) : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) where
  toFun d e := if insert o (lset lab e.1) ⊆ τ then d e / Ncov lab o e.1 else 0
  map_add' d d' := by ext e; simp only [Pi.add_apply]; split_ifs <;> simp [add_div]
  map_smul' r d := by ext e; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp [mul_div_assoc]

theorem sum_G0 (hk : 3 ≤ k) (d : E0 V → ℝ) : ∑ τ ∈ Trip o, G0 lab o τ d = d := by
  ext e
  rw [Finset.sum_apply]
  simp only [G0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hN : (0 : ℝ) < Ncov lab o e.1 := by exact_mod_cast Ncov_pos lab o hk e.1
  change (Ncov lab o e.1 : ℝ) * (d e / Ncov lab o e.1) = d e
  field_simp

/-- Number of monochromatic edges of class `o`. -/
def M0 : ℕ := #(univ.filter (fun e : E0 V => lset lab e.1 = {o}))

/-- Uniform weight on the monochromatic edges of class `o`. -/
def z0 : E0 V → ℝ := fun e => if lset lab e.1 = {o} then 1 / (M0 lab o : ℝ) else 0

/-- The corrected share: `ℓ` vanishes. -/
def Gt (τ : Finset (Fin k)) : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) :=
  G0 lab o τ + ((1 / 2 : ℝ) • (ellG' (wlk lab) ∘ₗ G0 lab o τ)).smulRight (z0 lab o)

theorem Gt_apply (τ : Finset (Fin k)) (d : E0 V → ℝ) :
    Gt lab o τ d = G0 lab o τ d + ((1 / 2 : ℝ) * ellG' (wlk lab) (G0 lab o τ d)) • z0 lab o := by
  simp [Gt, LinearMap.smulRight_apply]

theorem wlk_of_lset {e : Sym2 V} (h : lset lab e = {o}) : wlk lab e = -2 := by
  induction e using Sym2.ind with
  | _ u v =>
  rw [lset_mk] at h
  have hu : lab u = o := mem_singleton.1 (h ▸ mem_insert_self _ _)
  have hv : lab v = o := mem_singleton.1 (h ▸ mem_insert_of_mem (mem_singleton_self _))
  simp [wlk, hu, hv]

theorem ellG'_z0 (hM : 0 < M0 lab o) : ellG' (wlk lab) (z0 lab o) = -2 := by
  simp only [ellG', LinearMap.coe_mk, AddHom.coe_mk, z0, mul_ite, mul_zero]
  rw [← sum_filter]
  have hval : ∀ e ∈ univ.filter (fun e : E0 V => lset lab e.1 = {o}),
      wlk lab e.1 * (1 / (M0 lab o : ℝ)) = -2 * (1 / (M0 lab o : ℝ)) := fun e he => by
    rw [wlk_of_lset lab o (mem_filter.1 he).2]
  rw [sum_congr rfl hval, sum_const, nsmul_eq_mul]
  have hM' : (0 : ℝ) < M0 lab o := by exact_mod_cast hM
  change (M0 lab o : ℝ) * (-2 * (1 / (M0 lab o : ℝ))) = -2
  field_simp

theorem ellG'_Gt (hM : 0 < M0 lab o) (τ : Finset (Fin k)) (d : E0 V → ℝ) :
    ellG' (wlk lab) (Gt lab o τ d) = 0 := by
  rw [Gt_apply, map_add, map_smul, ellG'_z0 lab o hM, smul_eq_mul]; ring

theorem supp_Gt {τ : Finset (Fin k)} (ho : o ∈ τ) (d : E0 V → ℝ) {e : E0 V}
    (he : Gt lab o τ d e ≠ 0) : lset lab e.1 ⊆ τ := by
  rw [Gt_apply] at he
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, G0, LinearMap.coe_mk, AddHom.coe_mk,
    z0] at he
  by_cases h1 : insert o (lset lab e.1) ⊆ τ
  · exact (subset_insert _ _).trans h1
  by_cases h2 : lset lab e.1 = {o}
  · rw [h2]; exact singleton_subset_iff.2 ho
  · simp [h1, h2] at he

/-- An edge whose labels lie in a triple is an edge of the sub-host. -/
theorem exists_emap {τ : Finset (Fin k)} (hτ : τ.card = 3) (e : E0 V) (h : lset lab e.1 ⊆ τ) :
    ∃ e' : E0 (Sub lab (sig o τ)), emap lab (sig o τ) e' = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
  have hu : ∃ i, sig o τ i = lab u :=
    (mem_iff_sig o hτ _).1 (h (by rw [lset_mk]; exact mem_insert_self _ _))
  have hv : ∃ i, sig o τ i = lab v :=
    (mem_iff_sig o hτ _).1 (h (by rw [lset_mk]; exact mem_insert_of_mem (mem_singleton_self _)))
  have huv : u ≠ v := fun h' => he (by rw [h']; exact Sym2.mk_isDiag_iff.2 rfl)
  refine ⟨⟨s(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩, ?_⟩
  · rw [Sym2.mk_isDiag_iff]; intro h'; exact huv (congrArg Subtype.val h')
  · apply Subtype.ext; simp [emap]

/-! ### Norms -/

theorem norm_G0_le (hk : 3 ≤ k) (τ : Finset (Fin k)) (d : E0 V → ℝ) : ‖G0 lab o τ d‖ ≤ ‖d‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg d)).2 fun e => ?_
  simp only [G0, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
  have hN : (1 : ℝ) ≤ Ncov lab o e.1 := by exact_mod_cast Ncov_pos lab o hk e.1
  split_ifs
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < (Ncov lab o e.1 : ℝ) by linarith)]
    calc |d e| / Ncov lab o e.1 ≤ |d e| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) one_pos hN
      _ = |d e| := div_one _
      _ ≤ ‖d‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e
  · simp

theorem card_E0_le_sq : (Fintype.card (E0 V) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h : Fintype.card (E0 V) = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag
  have h2 : (Fintype.card V).choose 2 ≤ Fintype.card V * Fintype.card V := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  rw [h, sq]; exact_mod_cast h2

theorem abs_ellG'_le (g : E0 V → ℝ) :
    |ellG' (wlk lab) g| ≤ 2 * (Fintype.card V : ℝ) ^ 2 * ‖g‖ := by
  simp only [ellG', LinearMap.coe_mk, AddHom.coe_mk]
  have hw : ∀ e : Sym2 V, |wlk lab e| ≤ 2 := by
    intro e
    induction e using Sym2.ind with
    | _ u v => simp only [wlk, Sym2.lift_mk]; split_ifs <;> norm_num
  calc |∑ e, wlk lab e.1 * g e| ≤ ∑ e, |wlk lab e.1 * g e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e : E0 V, 2 * ‖g‖ := sum_le_sum fun e _ => by
        rw [abs_mul]
        exact mul_le_mul (hw e.1) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm g e)
          (abs_nonneg _) zero_le_two
    _ = Fintype.card (E0 V) * (2 * ‖g‖) := by rw [sum_const, nsmul_eq_mul, card_univ]
    _ ≤ (Fintype.card V : ℝ) ^ 2 * (2 * ‖g‖) :=
        mul_le_mul_of_nonneg_right card_E0_le_sq (by positivity)
    _ = 2 * (Fintype.card V : ℝ) ^ 2 * ‖g‖ := by ring

theorem norm_z0_le (hM : 0 < M0 lab o) : ‖z0 lab o‖ ≤ 1 / (M0 lab o : ℝ) := by
  have hM' : (0 : ℝ) < M0 lab o := by exact_mod_cast hM
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun e => ?_
  simp only [z0, Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_pos (by positivity)]
  · simp only [abs_zero]; positivity

/-- At least `C(c_o, 2)` monochromatic edges in class `o`. -/
theorem choose_le_M0 : (ksz lab o).choose 2 ≤ M0 lab o := by
  let W := {v : V // lab v = o}
  have hW : Fintype.card W = ksz lab o := by
    simp only [W, ksz]; exact Fintype.card_subtype _
  let F : E0 W → {e : E0 V // lset lab e.1 = {o}} := fun e =>
    ⟨⟨Sym2.map Subtype.val e.1, by rw [Sym2.isDiag_map Subtype.val_injective]; exact e.2⟩, by
      obtain ⟨e, -⟩ := e
      induction e using Sym2.ind with
      | _ a b =>
      show lset lab (Sym2.map Subtype.val s(a, b)) = {o}
      rw [Sym2.map_mk, lset_mk, a.2, b.2]
      simp⟩
  have hF : Function.Injective F := by
    intro e e' h
    apply Subtype.ext
    exact Sym2.map.injective Subtype.val_injective
      (congrArg (fun x : {e : E0 V // lset lab e.1 = {o}} => x.1.1) h)
  have h1 := Fintype.card_le_of_injective F hF
  have h2 : Fintype.card (E0 W) = (Fintype.card W).choose 2 := Sym2.card_subtype_not_diag
  have h3 : Fintype.card {e : E0 V // lset lab e.1 = {o}} = M0 lab o := by
    unfold M0; exact Fintype.card_subtype _
  rw [h2, hW, h3] at h1
  exact h1

/-! ### The glued inverse -/

variable {K₃ : ℝ}

/-- The glued inverse. -/
def PhiK (B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) K₃) :
    (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ) :=
  ∑ τ : {τ // τ ∈ Trip o},
    push lab (sig o τ.1) ∘ₗ (B τ).Φ ∘ₗ restr lab (sig o τ.1) ∘ₗ Gt lab o τ.1

theorem PhiK_apply (B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) K₃)
    (d : E0 V → ℝ) :
    PhiK lab o B d = ∑ τ : {τ // τ ∈ Trip o},
      push lab (sig o τ.1) ((B τ).Φ (restr lab (sig o τ.1) (Gt lab o τ.1 d))) := by
  simp [PhiK, LinearMap.sum_apply]

theorem MincG_piece (hM : 0 < M0 lab o)
    (B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) K₃) (τ : {τ // τ ∈ Trip o})
    (d : E0 V → ℝ) (e : E0 V) :
    MincG lab (bicF k) (push lab (sig o τ.1) ((B τ).Φ (restr lab (sig o τ.1) (Gt lab o τ.1 d)))) e =
      Gt lab o τ.1 d e := by
  obtain ⟨h3, ho⟩ := mem_Trip o τ.2
  have hinj := sig_inj o h3
  have hsupp : ∀ e, Gt lab o τ.1 d e ≠ 0 → ∃ e', emap lab (sig o τ.1) e' = e :=
    fun e he => exists_emap lab o h3 e (supp_Gt lab o ho d he)
  have hell : ell (subLab lab (sig o τ.1)) (restr lab (sig o τ.1) (Gt lab o τ.1 d)) = 0 := by
    rw [ell_restr hinj _ hsupp]; exact ellG'_Gt lab o hM τ.1 d
  by_cases hin : ∃ e', emap lab (sig o τ.1) e' = e
  · obtain ⟨e', rfl⟩ := hin
    rw [MincG_push_emap hinj, (B τ).exact _ hell]
    rfl
  · push Not at hin
    rw [MincG_push_out _ e hin]
    by_contra hne
    obtain ⟨e', he'⟩ := hsupp e (fun h0 => hne h0.symm)
    exact hin e' he'

/-- **Exactness.** -/
theorem MincG_PhiK (hk : 3 ≤ k) (hM : 0 < M0 lab o)
    (B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) K₃) (d : E0 V → ℝ)
    (hd : ellG' (wlk lab) d = 0) : MincG lab (bicF k) (PhiK lab o B d) = d := by
  ext e
  rw [PhiK_apply, map_sum, Finset.sum_apply]
  simp_rw [MincG_piece lab o hM B _ d e]
  have hG : ∀ τ : {τ // τ ∈ Trip o}, Gt lab o τ.1 d e =
      G0 lab o τ.1 d e + (1 / 2 : ℝ) * ellG' (wlk lab) (G0 lab o τ.1 d) * z0 lab o e := by
    intro τ; rw [Gt_apply]; simp [mul_assoc]
  simp_rw [hG]
  rw [sum_add_distrib, ← sum_mul, ← mul_sum, ← map_sum]
  have h1 : ∑ τ : {τ // τ ∈ Trip o}, G0 lab o τ.1 d = d := by
    rw [Finset.sum_coe_sort (Trip o) (fun τ => G0 lab o τ d)]; exact sum_G0 lab o hk d
  have h2 : ∑ τ : {τ // τ ∈ Trip o}, G0 lab o τ.1 d e = d e := by
    rw [← Finset.sum_apply, h1]
  rw [h1, h2, hd]; ring

theorem norm_Gt_le (hk : 3 ≤ k) (hM : 0 < M0 lab o) (τ : Finset (Fin k)) (d : E0 V → ℝ) :
    ‖Gt lab o τ d‖ ≤ (1 + (Fintype.card V : ℝ) ^ 2 / M0 lab o) * ‖d‖ := by
  have hM' : (0 : ℝ) < M0 lab o := by exact_mod_cast hM
  rw [Gt_apply]
  have hg := norm_G0_le lab o hk τ d
  have hl := abs_ellG'_le lab (G0 lab o τ d)
  have hz := norm_z0_le lab o hM
  calc ‖G0 lab o τ d + ((1 / 2 : ℝ) * ellG' (wlk lab) (G0 lab o τ d)) • z0 lab o‖
      ≤ ‖G0 lab o τ d‖ + ‖((1 / 2 : ℝ) * ellG' (wlk lab) (G0 lab o τ d)) • z0 lab o‖ :=
        norm_add_le _ _
    _ = ‖G0 lab o τ d‖ + |(1 / 2 : ℝ) * ellG' (wlk lab) (G0 lab o τ d)| * ‖z0 lab o‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖d‖ + ((Fintype.card V : ℝ) ^ 2 * ‖d‖) * (1 / (M0 lab o : ℝ)) := by
        apply add_le_add hg
        apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card V : ℝ) ^ 2)
        linarith
    _ = (1 + (Fintype.card V : ℝ) ^ 2 / M0 lab o) * ‖d‖ := by field_simp

/-- **Boundedness.** -/
theorem abs_PhiK_le (hk : 3 ≤ k) (hM : 0 < M0 lab o) {m : ℕ} {R : ℝ} (hK₃ : 0 ≤ K₃)
    (hm : ∀ X, m ≤ ksz lab X) (hm1 : 1 ≤ m) (hR : 0 < R)
    (hbal : (Fintype.card V : ℝ) ≤ R * m)
    (hMR : (Fintype.card V : ℝ) ^ 2 / M0 lab o ≤ 4 * R ^ 2)
    (B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) K₃) (d : E0 V → ℝ)
    (T : Finset V) :
    |PhiK lab o B d T| ≤ (#(Trip o) : ℝ) * (K₃ * R * (1 + 4 * R ^ 2)) /
      Fintype.card V * ‖d‖ := by
  have hnpos : (0 : ℝ) < Fintype.card V := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hcV : (ksz lab o : ℝ) ≤ Fintype.card V := by
      have : ksz lab o ≤ Fintype.card V := by
        unfold ksz; exact (card_filter_le _ _).trans_eq card_univ
      exact_mod_cast this
    have : (m : ℝ) ≤ ksz lab o := by exact_mod_cast hm o
    linarith
  set n : ℝ := (Fintype.card V : ℝ)
  have hpiece : ∀ τ : {τ // τ ∈ Trip o},
      |push lab (sig o τ.1) ((B τ).Φ (restr lab (sig o τ.1) (Gt lab o τ.1 d))) T| ≤
        K₃ * R * (1 + 4 * R ^ 2) / n * ‖d‖ := by
    intro τ
    obtain ⟨h3, ho⟩ := mem_Trip o τ.2
    have hinj := sig_inj o h3
    set x := restr lab (sig o τ.1) (Gt lab o τ.1 d)
    have hsupp : ∀ e, Gt lab o τ.1 d e ≠ 0 → ∃ e', emap lab (sig o τ.1) e' = e :=
      fun e he => exists_emap lab o h3 e (supp_Gt lab o ho d he)
    have hell : ell (subLab lab (sig o τ.1)) x = 0 := by
      rw [ell_restr hinj _ hsupp]; exact ellG'_Gt lab o hM τ.1 d
    -- the sub-host has at least `m` points
    have hsub : (m : ℝ) ≤ Fintype.card (Sub lab (sig o τ.1)) := by
      have h1 : csz (subLab lab (sig o τ.1)) 0 = ksz lab (sig o τ.1 0) := csz_subLab hinj 0
      have h2 : csz (subLab lab (sig o τ.1)) 0 ≤ Fintype.card (Sub lab (sig o τ.1)) := by
        unfold csz; exact (card_filter_le _ _).trans_eq card_univ
      have : m ≤ Fintype.card (Sub lab (sig o τ.1)) := (hm _).trans (h1 ▸ h2)
      exact_mod_cast this
    have hsubpos : (0 : ℝ) < Fintype.card (Sub lab (sig o τ.1)) :=
      lt_of_lt_of_le (by exact_mod_cast hm1) hsub
    have hx : ‖x‖ ≤ (1 + 4 * R ^ 2) * ‖d‖ := by
      calc ‖x‖ ≤ ‖Gt lab o τ.1 d‖ := norm_restr_le _
        _ ≤ (1 + n ^ 2 / M0 lab o) * ‖d‖ := norm_Gt_le lab o hk hM τ.1 d
        _ ≤ (1 + 4 * R ^ 2) * ‖d‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith
    have hK : K₃ / Fintype.card (Sub lab (sig o τ.1)) ≤ K₃ * R / n := by
      rw [div_le_div_iff₀ hsubpos hnpos]
      have : n ≤ R * Fintype.card (Sub lab (sig o τ.1)) := by
        calc n ≤ R * m := hbal
          _ ≤ R * Fintype.card (Sub lab (sig o τ.1)) := mul_le_mul_of_nonneg_left hsub hR.le
      nlinarith
    have hbd : ∀ T', |(B τ).Φ x T'| ≤ K₃ / Fintype.card (Sub lab (sig o τ.1)) * ‖x‖ :=
      fun T' => (B τ).bound x hell T'
    calc |push lab (sig o τ.1) ((B τ).Φ x) T|
        ≤ K₃ / Fintype.card (Sub lab (sig o τ.1)) * ‖x‖ :=
          abs_push_le _ (by positivity) hbd T
      _ ≤ K₃ * R / n * ((1 + 4 * R ^ 2) * ‖d‖) :=
          mul_le_mul hK hx (norm_nonneg _) (by positivity)
      _ = K₃ * R * (1 + 4 * R ^ 2) / n * ‖d‖ := by ring
  rw [PhiK_apply, Finset.sum_apply]
  calc |∑ τ : {τ // τ ∈ Trip o},
        push lab (sig o τ.1) ((B τ).Φ (restr lab (sig o τ.1) (Gt lab o τ.1 d))) T|
      ≤ ∑ τ : {τ // τ ∈ Trip o},
        |push lab (sig o τ.1) ((B τ).Φ (restr lab (sig o τ.1) (Gt lab o τ.1 d))) T| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _τ : {τ // τ ∈ Trip o}, K₃ * R * (1 + 4 * R ^ 2) / n * ‖d‖ :=
        sum_le_sum fun τ _ => hpiece τ
    _ = (#(Trip o) : ℝ) * (K₃ * R * (1 + 4 * R ^ 2) / n * ‖d‖) := by
        rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe]
    _ = (#(Trip o) : ℝ) * (K₃ * R * (1 + 4 * R ^ 2)) / n * ‖d‖ := by ring

end Glue

/-- **A bounded right inverse for the `k`-class bicolour host.** Every class has at least
`m ≥ max(512, 64 R³)` points and `n ≤ R m`. -/
theorem briK (lab : V → Fin k) (hk : 3 ≤ k) (o : Fin k) {m : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hm : ∀ X, m ≤ ksz lab X) (h512 : 512 ≤ m) (hmR : 64 * R ^ 3 ≤ m)
    (hbal : (Fintype.card V : ℝ) ≤ R * m) :
    Nonempty (BRIG lab (bicF k) (wlk lab)
      ((#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)))) := by
  -- the three-class inverses
  have hB : ∀ τ : {τ // τ ∈ Trip o}, Nonempty (BRI (subLab lab (sig o τ.1)) (400 * R ^ 5)) := by
    intro τ
    obtain ⟨h3, -⟩ := mem_Trip o τ.2
    have hinj := sig_inj o h3
    refine bri_of_ratio hR (fun i => ?_) h512 hmR ?_
    · rw [csz_subLab hinj]; exact hm _
    · have : Fintype.card (Sub lab (sig o τ.1)) ≤ Fintype.card V := Fintype.card_subtype_le _
      have : (Fintype.card (Sub lab (sig o τ.1)) : ℝ) ≤ Fintype.card V := by exact_mod_cast this
      linarith
  let B : ∀ τ : {τ // τ ∈ Trip o}, BRI (subLab lab (sig o τ.1)) (400 * R ^ 5) :=
    fun τ => Classical.choice (hB τ)
  -- the monochromatic edges of class `o`
  have hmR' : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hchoose : ((m.choose 2 : ℕ) : ℝ) ≤ M0 lab o := by
    have := (Nat.choose_le_choose 2 (hm o)).trans (choose_le_M0 lab o)
    exact_mod_cast this
  rw [Nat.cast_choose_two] at hchoose
  have hM0R : (m : ℝ) ^ 2 / 4 ≤ M0 lab o := by nlinarith
  have hM : 0 < M0 lab o := by
    have : (0 : ℝ) < M0 lab o := lt_of_lt_of_le (by positivity) hM0R
    exact_mod_cast this
  have hMR : (Fintype.card V : ℝ) ^ 2 / M0 lab o ≤ 4 * R ^ 2 := by
    have hM' : (0 : ℝ) < M0 lab o := by exact_mod_cast hM
    rw [div_le_iff₀ hM']
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have h2 : (Fintype.card V : ℝ) ^ 2 ≤ R ^ 2 * (m : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hn0 hbal 2; rwa [mul_pow] at this
    have := mul_le_mul_of_nonneg_left hM0R (by positivity : (0 : ℝ) ≤ 4 * R ^ 2)
    nlinarith
  refine ⟨⟨PhiK lab o B, fun d hd => MincG_PhiK lab o hk hM B d hd, fun d hd T => ?_⟩⟩
  have := abs_PhiK_le lab o hk hM (by positivity) hm (by omega) (by linarith) hbal hMR B d T
  calc |PhiK lab o B d T| ≤ (#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)) /
      Fintype.card V * ‖d‖ := this

end CDRBicolour.KBicolor
