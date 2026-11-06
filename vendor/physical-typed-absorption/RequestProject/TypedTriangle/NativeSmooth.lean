/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeRealification
public import RequestProject.S10K.KernelAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Native S10 (1.2) on one prepared induced core. The core retains the original
common-neighbour and hinge conditions, with parameter α/2. Both the integer
congestion provider and the smoothing kernel are constructed, rather than assumed.
No positive catalogue, sparse exactification or decomposition theorem is asserted. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.NativeSmooth
open S10V22

def coeff (α : ℝ) (h : ℕ) (K : ℝ) : ℝ :=
  6 * (1 / α) + 3 * K / 2 *
    (14 * (3 * (12 * S10V23.Kc α h) ^ 2 + (12 * S10V23.Kc α h) ^ 3 / 3) +
      36 * (1 / α) ^ 2)

lemma coeff_pos {α K : ℝ} (h : ℕ) (hα : 0 < α) (hK : 0 ≤ K) :
    0 < coeff α h K := by
  unfold coeff
  have := S10V23.one_le_Kc α h
  positivity

/-- Restricting a smooth certificate to the actual physical triangles preserves
its boundary and coefficient bound. Nonnegativity of the demand bound is explicit. -/
lemma supported_certificate {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I)) {x : Sym2 V → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (w : Finset V → ℝ)
    (hw : realOp (triMat (allowedTri H.G H.lab F)) w = x)
    (hb : ∀ S, |w S| ≤ B) :
    ∃ z : Finset V → ℝ,
      (∀ S, z S ≠ 0 → IsAllowed H F S) ∧
      realOp (triMat (allowedTri H.G H.lab F)) z = x ∧ ∀ S, |z S| ≤ B := by
  refine ⟨restrictTri (allowedTri H.G H.lab F) w, ?_, ?_, ?_⟩
  · intro S hS
    exact mem_allowedTri.mp (by
      by_contra hn
      exact hS (by simp [restrictTri, hn]))
  · rw [realOp_restrictTri, hw]
  · intro S
    by_cases hS : S ∈ allowedTri H.G H.lab F
    · simpa [restrictTri, hS] using hb S
    · simpa [restrictTri, hS] using hB

/-- Uniform smooth physical certificates from H3--H4 on a core chosen before
the demand. Constants precede the host; no certificate or kernel provider is an
input. The image is the actual real physical image, not its integer saturation. -/
theorem smooth_inverse_with_geometry_of_H3H4 (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ Kinf : ℝ, 0 < Kinf ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
          ∀ (x : Sym2 (Survivors A) → ℝ),
            x ∈ realImage (triMat (allowedTri (restrictedHost H A).G
              (restrictedHost H A).lab F)) →
            ∀ xmax : ℝ, 0 ≤ xmax → (∀ e, |x e| ≤ xmax) →
            ∃ w : Finset (Survivors A) → ℝ,
              (∀ S, w S ≠ 0 → IsAllowed (restrictedHost H A) F S) ∧
              realOp (triMat (allowedTri (restrictedHost H A).G
                (restrictedHost H A).lab F)) w = x ∧
              ∀ S, |w S| ≤ Kinf * xmax / (Fintype.card (Survivors A) : ℝ) := by
  obtain ⟨K, hK, nNative, hnative⟩ := native_congestion_with_geometry_of_H3H4 α h hα
  let γ : ℝ := α / 2
  let nKernel : ℕ := ⌈S10V23.Proc.nZero γ h⌉₊
  have hcoeff : 0 < coeff γ h K := coeff_pos h (by dsimp [γ]; positivity) hK.le
  refine ⟨coeff γ h K, hcoeff,
    max nNative (4 * nKernel + 1), ?_⟩
  intro V I _ H F hn hH3 hH4
  classical
  obtain ⟨A, hA, hA3, hA4, hcert⟩ := hnative H F ((le_max_left _ _).trans hn) hH3 hH4
  letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
  let Hc := restrictedHost H A
  have hcCard : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hnlarge : 4 * nKernel + 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnlargeR : (4 : ℝ) * nKernel + 1 ≤ Fintype.card V := by exact_mod_cast hnlarge
  have hcLarge : (nKernel : ℝ) ≤ Fintype.card (Survivors A) := by linarith
  have hnCore : S10V23.Proc.nZero γ h ≤ (Fintype.card (Survivors A) : ℝ) :=
    (Nat.le_ceil _).trans hcLarge
  have hp : IntCertProvider (triMat (allowedTri Hc.G Hc.lab F))
      (triTw (allowedTri Hc.G Hc.lab F)) edgeEw K (Fintype.card (Survivors A) : ℝ) :=
    NativeReal.provider_of_native (V := Survivors A) (I := I) (G := Hc.G)
      (lab := Hc.lab) (F := F) (K := K) hcert
  refine ⟨A, hA, hA3, hA4, ?_⟩
  intro x hx xmax hxmax0 hxmax
  obtain ⟨w, hw, hb⟩ := S10V23.smooth_inverse_H3H4 hA3 hA4
    (by positivity) hh hnCore hK.le hp hx hxmax
  exact supported_certificate Hc F
    (div_nonneg (mul_nonneg hcoeff.le hxmax0) (Nat.cast_nonneg _)) w hw hb

end TypedTriangle.NativeSmooth
