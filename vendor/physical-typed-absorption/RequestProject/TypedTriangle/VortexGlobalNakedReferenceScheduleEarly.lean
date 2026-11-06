/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalNakedReferenceSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- The future-core density precedes all route and reference tolerances.
This lets the inner rate be chosen from this same density before the
reference cap is set to a multiple of that inner rate. -/
theorem exists_global_naked_reference_schedule_early {I : Type}
    (F : Set (Multiset I)) (a b α C : ℝ) (h L : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h)
    : ∃ ρFuture : ℝ, 0 < ρFuture ∧
      ∀ cap ηCap ηGlobal : ℝ, 0 < cap → 0 < ηCap → 0 < ηGlobal →
    ∃ nGeometry : ℕ, ∃ K ηMax ηHole ηRef εRef γ : ℝ → ℝ,
    ∃ Nbase Ns nPaid nRef : ℝ → ℕ,
      (∀ x, 0 < x →
        0 < K x ∧ 0 < ηMax x ∧ 1 ≤ K x * ηMax x ∧
        PaidReferenceCap α h (ηMax x) nGeometry ∧
        PaidSmoothAt α x (K x) (ηMax x) h (Nbase x) (Ns x) (nPaid x) ∧
        ηHole x = 1 / (128 * C * C * K x) ∧
        0 < ηHole x ∧ ηHole x ≤ ηMax x ∧
        K x * (8 * C * ηHole x) = 1 / (16 * C) ∧
        0 < ηRef x ∧ ηRef x ≤ ηCap ∧ ηRef x ≤ ηMax x / 4 ∧
        ηRef x ≤ ηHole x / 4 ∧ 512 * C * C * K x * ηRef x ≤ 1 ∧
        0 < εRef x ∧ 0 < γ x ∧
        NakedReferenceAt F a b α ρFuture (ηRef x) (εRef x) (γ x) h (nRef x)) ∧
      ∃ β : ℕ → ℝ,
        (∀ j, 0 ≤ β j) ∧
        (∀ j ≤ L, 0 < β j ∧ β j ≤ cap) ∧
        (∀ j < L, β j ≤ β (j + 1) / 2) ∧
        (∀ j k, j < k → k ≤ L →
          β j ≤ min (1 / (2 * C * K (β k))) (εRef (β k)) /
            (16 * b * (L + 1))) ∧
        (∀ r ≤ L,
          K (β r) * (2 * b * (∑ j ∈ range r, β j)) ≤ 1 / (16 * C) ∧
          2 * b * (∑ j ∈ range r, β j) ≤ εRef (β r) / 8) ∧
        (∑ j ∈ range (L + 1), β j) ≤ ηGlobal / 2 ∧
        ∃ N : ℕ, nGeometry ≤ N ∧
          (∀ j : Fin (L + 1),
            max (max (max (Nbase (β j)) (Ns (β j))) (nPaid (β j))) (nRef (β j)) ≤ N) := by
  obtain ⟨ρFuture, hρFuture, hReference⟩ :=
    RawReference.dense_reference_containing_sparse_edges F a b α h ha hab hα
  refine ⟨ρFuture, hρFuture, ?_⟩
  intro cap ηCap ηGlobal hcap hηCap hηGlobal
  obtain ⟨nGeometry, K, ηMax, Nbase, Ns, nPaid, hPaid, hSchedule⟩ :=
    exists_global_paid_radius_schedule α C b cap ηGlobal h L
      hα hh hC (ha.trans_le hab) hcap hηGlobal
  let ηHole : ℝ → ℝ := fun x => 1 / (128 * C * C * K x)
  let ηRef : ℝ → ℝ := fun x =>
    min ηCap (min (ηMax x / 4) (1 / (512 * C * C * K x)))
  have hRefPos : ∀ x, 0 < x → 0 < ηRef x := by
    intro x hx
    have hK : 0 < K x := (hPaid x hx).1
    have hη : 0 < ηMax x := (hPaid x hx).2.1
    exact lt_min hηCap (lt_min (by positivity) (by positivity))
  have hChoice : ∀ x : ℝ, ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n : ℕ,
      0 < x → NakedReferenceAt F a b α ρFuture (ηRef x) ε γ h n := by
    intro x
    by_cases hx : 0 < x
    · obtain ⟨ε, γ, hε, hγ, n, hMake⟩ := hReference (ηRef x) (hRefPos x hx)
      exact ⟨ε, γ, hε, hγ, n, fun _ => hMake⟩
    · exact ⟨1, 1, by norm_num, by norm_num, 0, fun hp => False.elim (hx hp)⟩
  choose εRef γ hεRef hγ nRef hMake using hChoice
  have hParameters : ∀ x, 0 < x →
      0 < K x ∧ 0 < ηMax x ∧ 1 ≤ K x * ηMax x ∧
      PaidReferenceCap α h (ηMax x) nGeometry ∧
      PaidSmoothAt α x (K x) (ηMax x) h (Nbase x) (Ns x) (nPaid x) ∧
      ηHole x = 1 / (128 * C * C * K x) ∧
      0 < ηHole x ∧ ηHole x ≤ ηMax x ∧
      K x * (8 * C * ηHole x) = 1 / (16 * C) ∧
      0 < ηRef x ∧ ηRef x ≤ ηCap ∧ ηRef x ≤ ηMax x / 4 ∧
      ηRef x ≤ ηHole x / 4 ∧ 512 * C * C * K x * ηRef x ≤ 1 ∧
      0 < εRef x ∧ 0 < γ x ∧
      NakedReferenceAt F a b α ρFuture (ηRef x) (εRef x) (γ x) h (nRef x) := by
    intro x hx
    obtain ⟨hK, hηMax, hDom, hCap, hSmooth⟩ := hPaid x hx
    obtain ⟨hHole, hHoleCap, hHoleBudget⟩ :=
      explicit_child_hole_window C (K x) (ηMax x) hC hK hηMax hDom
    have hRefCap : ηRef x ≤ ηCap := min_le_left _ _
    have hRefMax : ηRef x ≤ ηMax x / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hRefInv : ηRef x ≤ 1 / (512 * C * C * K x) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hRefHole : ηRef x ≤ ηHole x / 4 := by
      calc
        ηRef x ≤ 1 / (512 * C * C * K x) := hRefInv
        _ = ηHole x / 4 := by dsimp only [ηHole]; ring
    have hCoefficient : 0 < 512 * C * C * K x := by
      have hCpos : 0 < C := by linarith
      positivity
    have hRefBudget : 512 * C * C * K x * ηRef x ≤ 1 := by
      have hMul := (le_div_iff₀ hCoefficient).mp hRefInv
      nlinarith
    exact ⟨hK, hηMax, hDom, hCap, hSmooth, rfl, hHole, hHoleCap, hHoleBudget,
      hRefPos x hx, hRefCap, hRefMax, hRefHole, hRefBudget,
      hεRef x, hγ x, hMake x hx⟩
  obtain ⟨β, hβNonneg, hβCap, hStep, hCross, hPrior, hSum, Nold, hNgeom, hNold⟩ :=
    hSchedule εRef (fun x _ => hεRef x)
  let N : ℕ := max Nold ((univ : Finset (Fin (L + 1))).sup (fun j => nRef (β j)))
  refine ⟨nGeometry, K, ηMax, ηHole, ηRef, εRef, γ,
    Nbase, Ns, nPaid, nRef, hParameters, β, hβNonneg, hβCap, hStep, hCross,
    hPrior, hSum, N, hNgeom.trans (le_max_left _ _), ?_⟩
  intro j
  apply max_le
  · exact (hNold j).trans (le_max_left _ _)
  · exact (Finset.le_sup (f := fun i : Fin (L + 1) => nRef (β i)) (mem_univ j)).trans
      (le_max_right _ _)

#print axioms exists_global_naked_reference_schedule_early
end TypedTriangle.Vortex
