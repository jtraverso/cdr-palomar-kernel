/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidChildSmooth
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Choose the inverse constant on an actual edge-paid child before the
preparation radius is selected. Large radii are reduced to one half; this
only weakens the prepared-core deletion budget. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

theorem exists_paid_smooth_constant_function (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ K : ℝ → ℝ, (∀ β, 0 < β → 0 < K β) ∧
      ∀ β, 0 < β → ∃ η : ℝ, 0 < η ∧ ∃ Nbase Ns n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I)
          (F : Set (Multiset I)),
          n₀ ≤ Fintype.card V →
          Dispersal.PreparedCore H.G H.lab F α h (max Nbase Ns) β →
          CommonNbrCond H F α → HingeCond H F α h →
          ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
            (∀ v, SparseEdge.degIn B v ≤ d) →
            (d : ℝ) ≤ η * Fintype.card V →
            let J := subHost H (edges H \ B)
            CommonNbrCond J F (min (α / 2) (S07V49.hingeConstB α 1 h)) →
            HingeCond J F (min (α / 2) (S07V49.hingeConstB α 1 h))
              (2 * h - 3) →
            NativeSmooth.Smooth J F (K β) := by
  have hchoice : ∀ β : ℝ, ∃ k : ℝ, 0 < k ∧
      (0 < β → ∃ η : ℝ, 0 < η ∧ ∃ Nbase Ns n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I)
          (F : Set (Multiset I)),
          n₀ ≤ Fintype.card V →
          Dispersal.PreparedCore H.G H.lab F α h (max Nbase Ns) β →
          CommonNbrCond H F α → HingeCond H F α h →
          ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
            (∀ v, SparseEdge.degIn B v ≤ d) →
            (d : ℝ) ≤ η * Fintype.card V →
            let J := subHost H (edges H \ B)
            CommonNbrCond J F (min (α / 2) (S07V49.hingeConstB α 1 h)) →
            HingeCond J F (min (α / 2) (S07V49.hingeConstB α 1 h))
              (2 * h - 3) →
            NativeSmooth.Smooth J F k) := by
    intro β
    by_cases hβ : 0 < β
    · let β' := min β (1 / 2)
      have hβ' : 0 < β' := lt_min hβ (by norm_num)
      have hβ'half : β' ≤ 1 / 2 := min_le_right _ _
      obtain ⟨k, hk, η, hη, Nbase, Ns, n₀, hsm⟩ :=
        smooth_on_paid_prepared_child α β' h hα hβ' hβ'half hh
      refine ⟨k, hk, fun _ => ⟨η, hη, Nbase, Ns, n₀, ?_⟩⟩
      intro V I _ H F hn P h3 h4 B d hBE hDeg hSmall
      have hsub {Z : Finset V}
          (hz : (Z.card : ℝ) ≤ β' * Fintype.card V) :
          (Z.card : ℝ) ≤ β * Fintype.card V :=
        hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
      have P' : Dispersal.PreparedCore H.G H.lab F α h
          (max Nbase Ns) β' :=
        { h3 := fun Z hz => P.h3 Z (hsub hz)
          h4 := fun Z hz => P.h4 Z (hsub hz)
          order := fun Z hz => P.order Z (hsub hz)
          lattice_persist := fun Z hz y hy hvan =>
            P.lattice_persist Z (hsub hz) y hy hvan }
      exact hsm H F hn P' h3 h4 B d hBE hDeg hSmall
    · exact ⟨1, by norm_num, fun hp => False.elim (hβ hp)⟩
  choose K hK using hchoice
  exact ⟨K, (fun β hβ => (hK β).1), fun β hβ => (hK β).2 hβ⟩

#print axioms exists_paid_smooth_constant_function

end TypedTriangle.Vortex
