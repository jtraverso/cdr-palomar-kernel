/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSmooth
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! S10 §6: positive exactification in the actual real physical image. The
geometric producer is separate from this finite linear-algebra application.
No assertion about sparse edge deletion or an integral decomposition is made. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.NativeSmooth
open S10V22
variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The supported smooth inverse contract used by positive exactification. -/
def Smooth (H : Host V I) (F : Set (Multiset I)) (K : ℝ) : Prop :=
  ∀ x : Sym2 V → ℝ, x ∈ realImage (triMat (allowedTri H.G H.lab F)) →
    ∀ ε : ℝ, 0 ≤ ε → (∀ e, |x e| ≤ ε) →
    ∃ w : Finset V → ℝ, (∀ S, w S ≠ 0 → IsAllowed H F S) ∧
      realOp (triMat (allowedTri H.G H.lab F)) w = x ∧
      ∀ S, |w S| ≤ K * ε / (Fintype.card V : ℝ)

/-- Target and approximate boundary lie in the same actual real image; the
smooth correction preserves support and the stipulated positive coefficient window. -/
theorem exactify_of_smooth (H : Host V I) (F : Set (Multiset I)) {K : ℝ}
    (hS : Smooth H F K) (μ : Finset V → ℝ) (b : Sym2 V → ℝ)
    (hb : b ∈ realImage (triMat (allowedTri H.G H.lab F)))
    (hμsupp : ∀ S, μ S ≠ 0 → IsAllowed H F S)
    {a₀ b₀ ε : ℝ} (hε : 0 ≤ ε)
    (hμ : ∀ S, IsAllowed H F S →
      a₀ / (Fintype.card V : ℝ) ≤ μ S ∧ μ S ≤ b₀ / (Fintype.card V : ℝ))
    (hdef : ∀ e, |(b - realOp (triMat (allowedTri H.G H.lab F)) μ) e| ≤ ε)
    (hbudget : K * ε ≤ a₀ / 2) :
    ∃ ψ : Finset V → ℝ, (∀ S, ψ S ≠ 0 → IsAllowed H F S) ∧
      realOp (triMat (allowedTri H.G H.lab F)) ψ = b ∧
      (∀ S, |ψ S - μ S| ≤ K * ε / (Fintype.card V : ℝ)) ∧
      ∀ S, IsAllowed H F S →
        a₀ / (2 * (Fintype.card V : ℝ)) ≤ ψ S ∧
        ψ S ≤ (b₀ + a₀ / 2) / (Fintype.card V : ℝ) := by
  let M := triMat (allowedTri H.G H.lab F)
  have hμimage : realOp M μ ∈ realImage M := ⟨μ, rfl⟩
  have hx : b - realOp M μ ∈ realImage M := (realImage M).sub_mem hb hμimage
  obtain ⟨w, hwS, hw, hwB⟩ := hS _ hx ε hε hdef
  refine ⟨μ + w, ?_, ?_, ?_, ?_⟩
  · intro S hS
    by_contra hn
    have hm : μ S = 0 := by by_contra hm; exact hn (hμsupp S hm)
    have hz : w S = 0 := by by_contra hz; exact hn (hwS S hz)
    exact hS (by simp [hm, hz])
  · change realOp M (μ + w) = b
    rw [map_add, hw]
    abel
  · intro S
    simpa using hwB S
  · intro S hS
    have hbounds := hμ S hS
    have hwabs := (abs_le.mp (hwB S))
    have hsmall : K * ε / (Fintype.card V : ℝ) ≤ a₀ / 2 / (Fintype.card V : ℝ) :=
      div_le_div_of_nonneg_right hbudget (Nat.cast_nonneg _)
    have hhalf : a₀ / 2 / (Fintype.card V : ℝ) =
        a₀ / (2 * (Fintype.card V : ℝ)) := by rw [div_div]
    have hlo : a₀ / (Fintype.card V : ℝ) =
        2 * (a₀ / (2 * (Fintype.card V : ℝ))) := by rw [← div_div]; ring
    have hhi : (b₀ + a₀ / 2) / (Fintype.card V : ℝ) =
        b₀ / (Fintype.card V : ℝ) + a₀ / 2 / (Fintype.card V : ℝ) := by rw [add_div]
    change a₀ / (2 * (Fintype.card V : ℝ)) ≤ μ S + w S ∧
      μ S + w S ≤ (b₀ + a₀ / 2) / (Fintype.card V : ℝ)
    constructor <;> linarith

/-- Positive exactification for every approximate seed and compatible target on
one host. It is distinct from integer divisibility or exact decomposition. -/
def Exactifies (H : Host V I) (F : Set (Multiset I)) (K : ℝ) : Prop :=
  ∀ (μ : Finset V → ℝ) (b : Sym2 V → ℝ),
    b ∈ realImage (triMat (allowedTri H.G H.lab F)) →
    (∀ S, μ S ≠ 0 → IsAllowed H F S) →
    ∀ a₀ b₀ ε : ℝ, 0 ≤ ε →
    (∀ S, IsAllowed H F S →
      a₀ / (Fintype.card V : ℝ) ≤ μ S ∧ μ S ≤ b₀ / (Fintype.card V : ℝ)) →
    (∀ e, |(b - realOp (triMat (allowedTri H.G H.lab F)) μ) e| ≤ ε) →
    K * ε ≤ a₀ / 2 →
    ∃ ψ : Finset V → ℝ, (∀ S, ψ S ≠ 0 → IsAllowed H F S) ∧
      realOp (triMat (allowedTri H.G H.lab F)) ψ = b ∧
      (∀ S, |ψ S - μ S| ≤ K * ε / (Fintype.card V : ℝ)) ∧
      ∀ S, IsAllowed H F S →
        a₀ / (2 * (Fintype.card V : ℝ)) ≤ ψ S ∧
        ψ S ≤ (b₀ + a₀ / 2) / (Fintype.card V : ℝ)

/-- Constants and the common core are produced from the original geometry.
The approximate weights and physical target are chosen only afterwards; no
smooth-inverse provider is assumed in this global application. -/
theorem exactification_core_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
          Exactifies (restrictedHost H A) F K := by
  obtain ⟨K, hK, n₀, hcore⟩ := smooth_inverse_with_geometry_of_H3H4 α h hα hh
  refine ⟨K, hK, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨A, hA, hA3, hA4, hs⟩ := hcore H F hn hH3 hH4
  letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
  refine ⟨A, hA, hA3, hA4, ?_⟩
  intro μ b hb hμsupp a₀ b₀ ε hε hμ hdef hbudget
  exact exactify_of_smooth (restrictedHost H A) F hs μ b hb hμsupp hε hμ hdef hbudget

end TypedTriangle.NativeSmooth
