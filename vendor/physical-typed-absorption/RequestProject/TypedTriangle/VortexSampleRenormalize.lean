/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RawProfileDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Quantitative bookkeeping when an exceptional set is removed from a
sampled core. The sampling density must be renormalized before the reference
constructor is applied to the surviving core. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

open S07V48

theorem profile_bound_after_renormalization (q τ E x : ℝ)
    (hq : 0 < q) (hτ : 0 ≤ τ) (hτq : 4 * τ ≤ q) (hE : 0 ≤ E)
    (hprofile : |x / q - 1| ≤ E) :
    |x / (q - 2 * τ) - 1| ≤ 2 * E + 4 * τ / q := by
  have hq' : 0 < q - 2 * τ := by linarith
  have hratio : q / (q - 2 * τ) ≤ 2 :=
    (div_le_iff₀ hq').2 (by linarith)
  have hshift : 2 * τ / (q - 2 * τ) ≤ 4 * τ / q := by
    apply (div_le_div_iff₀ hq' hq).2
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτq)]
  have hid : x / (q - 2 * τ) - 1 =
      (q / (q - 2 * τ)) * (x / q - 1) + 2 * τ / (q - 2 * τ) := by
    field_simp
    ring
  rw [hid]
  calc
    |q / (q - 2 * τ) * (x / q - 1) + 2 * τ / (q - 2 * τ)|
        ≤ |q / (q - 2 * τ) * (x / q - 1)| + |2 * τ / (q - 2 * τ)| := abs_add_le _ _
    _ = q / (q - 2 * τ) * |x / q - 1| + 2 * τ / (q - 2 * τ) := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hq.le hq'.le),
        abs_of_nonneg (div_nonneg (by positivity) hq'.le)]
    _ ≤ 2 * E + 4 * τ / q := by
      have hscale := mul_le_mul_of_nonneg_left hprofile
        (div_nonneg hq.le hq'.le)
      nlinarith [hscale, hratio, hshift]

#print axioms profile_bound_after_renormalization

theorem sampled_profile_after_trim_and_renormalization {V I : Type*}
    [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (W A : Finset V) (u v : V)
    (b q τ e δ : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (hτ : 0 ≤ τ) (hτq : 4 * τ ≤ q) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hn : 0 < (Fintype.card V : ℝ))
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b / Fintype.card V)
    (hraw : |sampW H.G H.lab F μ W u v / q - 1| ≤ e)
    (hbudget : A.card * (b / Fintype.card V) ≤ q * δ) :
    |sampW H.G H.lab F μ (W \ A) u v / (q - 2 * τ) - 1| ≤
      2 * (e + δ) + 4 * τ / q := by
  have htrim := RawReference.sampled_profile_after_vertex_deletion
    H F μ W A u v b q e δ hb hq hn hμ hraw hbudget
  exact profile_bound_after_renormalization q τ (e + δ)
    (sampW H.G H.lab F μ (W \ A) u v) hq hτ hτq (by linarith) htrim

#print axioms sampled_profile_after_trim_and_renormalization

theorem completion_pool_after_trim {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W A : Finset V)
    (q α τ : ℝ) (hα : 0 < α) (hτ : 0 ≤ τ)
    (hτpool : 4 * τ ≤ q * α)
    (hA : (A.card : ℝ) ≤ τ * Fintype.card V)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤
        ((commonNbrs H k u v) ∩ W).card) :
    ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (q - 2 * τ) * (α / 2) * Fintype.card V / 2 ≤
        ((commonNbrs H k u v) ∩ (W \ A)).card := by
  intro u v huv k hk
  let S := commonNbrs H k u v
  have heq : S ∩ (W \ A) = (S ∩ W) \ A := by
    ext x
    simp only [mem_inter, mem_sdiff]
    tauto
  have hcard : (S ∩ W).card ≤ (S ∩ (W \ A)).card + A.card := by
    rw [heq]
    exact Finset.card_le_card_sdiff_add_card
  have hcardR : ((S ∩ W).card : ℝ) ≤
      ((S ∩ (W \ A)).card : ℝ) + A.card := by exact_mod_cast hcard
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hτn := mul_le_mul_of_nonneg_right hτpool hn
  have hτan : 0 ≤ τ * α * (Fintype.card V : ℝ) := by positivity
  have hp := hpool u v huv k hk
  change q * α * Fintype.card V / 2 ≤ ((S ∩ W).card : ℝ) at hp
  nlinarith only [hp, hcardR, hA, hτn, hτan]

#print axioms completion_pool_after_trim

end TypedTriangle.Vortex
