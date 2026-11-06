/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidSmoothParameters
public import RequestProject.TypedTriangle.VariablePreparedSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A compact, genuine-host interface for the inverse-constant schedule.
The child consumer is named separately, so the sampled window theorem does
not repeat its large nested type. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

def PaidSmoothAt (α β K η : ℝ) (h Nbase Ns nPaid : ℕ) : Prop :=
  ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
    nPaid ≤ Fintype.card V →
    Dispersal.PreparedCore H.G H.lab F α h (max Nbase Ns) β →
    CommonNbrCond H F α → HingeCond H F α h →
    ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
      (∀ v, SparseEdge.degIn B v ≤ d) →
      (d : ℝ) ≤ η * Fintype.card V →
      let J := subHost H (edges H \ B)
      CommonNbrCond J F (min (α / 2) (S07V49.hingeConstB α 1 h)) →
      HingeCond J F (min (α / 2) (S07V49.hingeConstB α 1 h))
        (2 * h - 3) →
      NativeSmooth.Smooth J F K

theorem scheduled_prepared_paid_parameter_core (α τ C q : ℝ) (h : ℕ)
    (hα : 0 < α) (hτ : 0 < τ) (hC : 1 ≤ C) (hq : 0 < q)
    (hh : 6 ≤ h) :
    ∃ (K : ℝ → ℝ) (L : ℕ) (β : ℕ → ℝ) (ξ : ℝ),
      ∃ (η : Fin (L + 1) → ℝ)
        (Nbase Ns nPaid : Fin (L + 1) → ℕ) (N n₀ : ℕ),
        0 < ξ ∧ (∀ j ≤ L, 0 < β j) ∧
        (∀ j k, j < k → k ≤ L →
          β j ≤ prepTolerance (K (β k)) C q /
            (16 * C * (L + 1))) ∧
        (∀ j : Fin (L + 1), 0 < η j ∧
          PaidSmoothAt (α / 4) (β j) (K (β j)) (η j) h
            (Nbase j) (Ns j) (nPaid j)) ∧
        (∀ j : Fin (L + 1),
          max (max (Nbase j) (Ns j)) (nPaid j) ≤ N) ∧
        ∀ {V I : Type} [Fintype V] (H : Host V I)
          (F : Set (Multiset I)),
          n₀ ≤ Fintype.card V →
          CommonNbrCond H F α → HingeCond H F α h →
          ∃ r ≤ L, ∃ A : Finset V,
            A.card ≤ TypedTriangle.priorBudget
              (fun j => ⌊β j * Fintype.card V⌋₊) r ∧
            (A.card : ℝ) ≤ τ * Fintype.card V ∧
            CommonNbrCond (restrictedHost H A) F (α / 2) ∧
            HingeCond (restrictedHost H A) F (α / 2) h ∧
            Dispersal.PreparedCore (restrictedHost H A).G
              (restrictedHost H A).lab F (α / 4) h N (β r) ∧
            K (β r) * (ξ + (A.card : ℝ) * C /
              (q * Fintype.card V)) ≤ 1 / (4 * C) := by
  have hα4 : 0 < α / 4 := by positivity
  obtain ⟨K, hKpos, hPaid⟩ :=
    exists_paid_smooth_constant_function (α / 4) h hα4 hh
  obtain ⟨L, β, ξ, hξ, hβ, hCross, hPrepared⟩ :=
    scheduled_prepared_core α τ C q h K hα hτ hC hq hKpos
  have hChoice : ∀ j : Fin (L + 1),
      ∃ ηj : ℝ, 0 < ηj ∧ ∃ Nb Nj Np : ℕ,
        PaidSmoothAt (α / 4) (β j) (K (β j)) ηj h Nb Nj Np := by
    intro j
    obtain ⟨ηj, hηj, Nb, Nj, Np, hspec⟩ :=
      hPaid (β j) (hβ j (Nat.le_of_lt_succ j.isLt))
    exact ⟨ηj, hηj, Nb, Nj, Np, hspec⟩
  choose η hη Nbase Ns nPaid hSpec using hChoice
  let N : ℕ := (univ : Finset (Fin (L + 1))).sup
    (fun j => max (max (Nbase j) (Ns j)) (nPaid j))
  obtain ⟨n₀, hPreparedN⟩ := hPrepared N
  exact ⟨K, L, β, ξ, η, Nbase, Ns, nPaid, N, n₀,
    hξ, hβ, hCross, (fun j => ⟨hη j, hSpec j⟩),
    (fun j => Finset.le_sup (f := fun i : Fin (L + 1) =>
      max (max (Nbase i) (Ns i)) (nPaid i)) (Finset.mem_univ j)),
    hPreparedN⟩

#print axioms scheduled_prepared_paid_parameter_core

end TypedTriangle.Vortex
