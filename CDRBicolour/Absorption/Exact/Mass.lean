/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.GenSeed
public import CDRBicolour.Absorption.SeedCounts
public import CDRBicolour.Absorption.BRIFinal

/-!
# Residual seeds with a prescribed `AAC` mass (item 3, exact spectrum)

* `seed_convex`: diffuse seeds with the same constant form a convex set;
* `mass_residual`: if `μ = gm L (μ₀ + ψ)` with `|ψ| ≤ r`, its `AAC` mass on the residual host
  differs from the mass of `μ₀` on the complete host by at most `n³ r + n² Δ · C₀/n`;
* `residual_seed_mass`: from the count seeds `wtN τ` (`cdr_H1_counts`) and the bounded inverse,
  a residual seed (constant `2 C₀`) whose `AAC` mass is `τ` up to `(4K + 1) C₀ Δ n`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Exact

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined

/-- Convexity of diffuse seeds. -/
theorem seed_convex {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {μ₁ μ₂ : Finset V → ℝ} (h₁ : IsDiffuseSeed H F C μ₁) (h₂ : IsDiffuseSeed H F C μ₂) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsDiffuseSeed H F C (fun T => (1 - θ) * μ₁ T + θ * μ₂ T) := by
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · obtain ⟨a1, b1⟩ := h₁.1 T hT
    obtain ⟨a2, b2⟩ := h₂.1 T hT
    constructor <;> nlinarith
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, h₁.2 e he, h₂.2 e he]; ring

variable {a b c : ℕ}

/-- The AAC weight. -/
def wAAC (a b c : ℕ) (Q : Finset (Fin (a + b + c))) : ℝ :=
  if Q.val.map (col3 a b c) = aac then 1 else 0

theorem allowed_cdr_eq : allowed (cdrHost a b c) cdrF = tri (col3 a b c) := by
  ext T
  rw [mem_tri]
  classical
  unfold allowed
  simp only [mem_filter, mem_univ, true_and]
  exact Iff.rfl

theorem allowed_res_eq (L : Finset (Sym2 (Fin (a + b + c)))) :
    allowed (rHost (col3 a b c) L) cdrF =
      (tri (col3 a b c)).filter fun T => Disjoint (triEdges T) L := by
  ext T
  rw [mem_allowed_rHost, allowed_rHost_iff, mem_filter]

theorem card_tri_le : (#(tri (col3 a b c)) : ℝ) ≤ ((a + b + c : ℕ) : ℝ) ^ 3 := by
  have hsub : tri (col3 a b c) ⊆ (univ : Finset (Fin (a + b + c))).powersetCard 3 := by
    intro T hT
    rw [mem_powersetCard]
    exact ⟨subset_univ _, (mem_tri.mp hT).1⟩
  have h1 := card_le_card hsub
  rw [card_powersetCard, card_univ, Fintype.card_fin] at h1
  have h2 := h1.trans (Nat.choose_le_pow _ _)
  exact_mod_cast h2

theorem card_bad_le (L : Finset (Sym2 (Fin (a + b + c)))) {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) :
    (#((tri (col3 a b c)).filter fun T => ¬ Disjoint (triEdges T) L) : ℝ) ≤
      ((a + b + c : ℕ) : ℝ) ^ 2 * Δ := by
  have hsub : ((tri (col3 a b c)).filter fun T => ¬ Disjoint (triEdges T) L) ⊆
      (univ : Finset (Fin (a + b + c))).biUnion fun v => (nbL L v).biUnion fun w =>
        (univ : Finset (Fin (a + b + c))).image fun x => ({v, w, x} : Finset (Fin (a + b + c))) := by
    intro T hT
    obtain ⟨hTt, hbad⟩ := mem_filter.mp hT
    obtain ⟨e, he, heL⟩ := not_disjoint_iff.mp hbad
    induction e using Sym2.ind with
    | _ v w =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
    obtain ⟨⟨hv, hw⟩, hvw⟩ := he
    obtain ⟨x, -, -, hTx⟩ := third_vertex (mem_tri.mp hTt).1 hvw hv hw
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    refine ⟨v, w, ?_, x, hTx.symm⟩
    simp only [nbL, mem_filter, mem_univ, true_and]
    rwa [Sym2.eq_swap]
  have hc := card_le_card hsub
  have h2 : #((univ : Finset (Fin (a + b + c))).biUnion fun v => (nbL L v).biUnion fun w =>
      (univ : Finset (Fin (a + b + c))).image fun x => ({v, w, x} : Finset (Fin (a + b + c)))) ≤ (a + b + c) * (Δ * (a + b + c)) := by
    calc _ ≤ ∑ v : Fin (a + b + c), #((nbL L v).biUnion fun w =>
          (univ : Finset (Fin (a + b + c))).image fun x => ({v, w, x} : Finset (Fin (a + b + c)))) := card_biUnion_le
      _ ≤ ∑ _v : Fin (a + b + c), Δ * (a + b + c) := by
          gcongr with v
          calc _ ≤ ∑ w ∈ nbL L v, #((univ : Finset (Fin (a + b + c))).image
                fun x => ({v, w, x} : Finset (Fin (a + b + c)))) := card_biUnion_le
            _ ≤ ∑ _w ∈ nbL L v, (a + b + c) := by
                gcongr with w; exact card_image_le.trans (by simp)
            _ = #(nbL L v) * (a + b + c) := by rw [sum_const, smul_eq_mul]
            _ ≤ Δ * (a + b + c) := Nat.mul_le_mul_right _ (by have := hdeg v; unfold degL at this; exact this)
      _ = (a + b + c) * (Δ * (a + b + c)) := by simp [sum_const, card_univ]
  have : (#((tri (col3 a b c)).filter fun T => ¬ Disjoint (triEdges T) L) : ℝ) ≤
      ((((a + b + c) * (Δ * (a + b + c)) : ℕ)) : ℝ) := by exact_mod_cast hc.trans h2
  have e : ((((a + b + c) * (Δ * (a + b + c)) : ℕ)) : ℝ) = ((a + b + c : ℕ) : ℝ) ^ 2 * Δ := by
    push_cast; ring
  linarith

/-- **Mass of a residual seed.** -/
theorem mass_residual (L : Finset (Sym2 (Fin (a + b + c)))) {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ)
    {μ₀ ψ : Finset (Fin (a + b + c)) → ℝ} {r C₀ : ℝ} (hψ : ∀ T, |ψ T| ≤ r)
    (hμ₀ : ∀ T ∈ tri (col3 a b c), |μ₀ T| ≤ C₀ / ((a + b + c : ℕ) : ℝ)) (hC₀ : 0 ≤ C₀) :
    |∑ Q ∈ allowed (rHost (col3 a b c) L) cdrF, gm L (μ₀ + ψ) Q * wAAC a b c Q -
        ∑ Q ∈ allowed (cdrHost a b c) cdrF, μ₀ Q * wAAC a b c Q| ≤
      ((a + b + c : ℕ) : ℝ) ^ 3 * r + ((a + b + c : ℕ) : ℝ) ^ 2 * Δ * (C₀ / ((a + b + c : ℕ) : ℝ)) := by
  have hr : 0 ≤ r := (abs_nonneg _).trans (hψ ∅)
  have hw : ∀ Q, 0 ≤ wAAC a b c Q ∧ wAAC a b c Q ≤ 1 := fun Q => by
    unfold wAAC; split_ifs <;> norm_num
  rw [allowed_res_eq, allowed_cdr_eq]
  set S := tri (col3 a b c)
  have hsplit : ∑ Q ∈ S, μ₀ Q * wAAC a b c Q =
      ∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), μ₀ Q * wAAC a b c Q +
        ∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * wAAC a b c Q :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hgood : ∀ Q ∈ S.filter (fun T => Disjoint (triEdges T) L),
      gm L (μ₀ + ψ) Q * wAAC a b c Q = μ₀ Q * wAAC a b c Q + ψ Q * wAAC a b c Q := by
    intro Q hQ
    simp only [gm, LinearMap.coe_mk, AddHom.coe_mk, if_pos (mem_filter.mp hQ).2, Pi.add_apply]
    ring
  rw [sum_congr rfl hgood, sum_add_distrib, hsplit]
  have e : ∀ x y z : ℝ, x + y - (x + z) = y - z := fun _ _ _ => by ring
  rw [e]
  have h1 : |∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), ψ Q * wAAC a b c Q| ≤
      ((a + b + c : ℕ) : ℝ) ^ 3 * r := by
    calc _ ≤ ∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), |ψ Q * wAAC a b c Q| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Q ∈ S.filter (fun T => Disjoint (triEdges T) L), r := by
          gcongr with Q
          rw [abs_mul, abs_of_nonneg (hw Q).1]
          nlinarith [hψ Q, (hw Q).2, abs_nonneg (ψ Q)]
      _ = #(S.filter fun T => Disjoint (triEdges T) L) * r := by rw [sum_const, nsmul_eq_mul]
      _ ≤ #S * r := by gcongr; exact filter_subset _ _
      _ ≤ _ := by gcongr; exact card_tri_le
  have h2 : |∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * wAAC a b c Q| ≤
      ((a + b + c : ℕ) : ℝ) ^ 2 * Δ * (C₀ / ((a + b + c : ℕ) : ℝ)) := by
    calc _ ≤ ∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), |μ₀ Q * wAAC a b c Q| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L),
            C₀ / ((a + b + c : ℕ) : ℝ) := by
          gcongr with Q hQ
          rw [abs_mul, abs_of_nonneg (hw Q).1]
          have := hμ₀ Q (mem_filter.mp hQ).1
          nlinarith [(hw Q).2, abs_nonneg (μ₀ Q)]
      _ = #(S.filter fun T => ¬ Disjoint (triEdges T) L) * (C₀ / ((a + b + c : ℕ) : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact card_bad_le L hdeg
  calc _ ≤ |∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), ψ Q * wAAC a b c Q| +
        |∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * wAAC a b c Q| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

end CDRBicolour.Absorption.Exact
