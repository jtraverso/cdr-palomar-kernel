/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V38.NativeAnnihilator
@[expose] public section

/-!
# V38 §3 — bounded matching potential on the native host (native corollary)

Two real edge functionals `λ₀, λ_H` on the native columns of the same host whose difference
vanishes on every actual local profile. Under the ORIGINAL H3 (`CommonNbrCond G lab F α`,
`α > 0`) and nothing else:

* `matching_potential` — there is a row potential `t : NRow → ℝ` with
  `natBᵀ t = λ_H − λ₀` on EVERY native column (anchor columns retained) and
  `|t_i| ≤ (3/(2α²) + 1) L` whenever `|λ_H e − λ₀ e| ≤ L` for all native `e`;
* `matching_potential_norm` — the same with `L = ‖λ_H − λ₀‖∞`;
* `matching_potential_bounded` — if `|λ₀ e|, |λ_H e| ≤ A`, then `|t_i| ≤ (3/(2α²)+1)·2A`.

The row span is NOT a hypothesis: it is `rowSpan_of_annihilates` (V38 §2); the bound is
V36 `native_gauge_alpha`.
-/

open Finset Classical

noncomputable section

namespace S07V38

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V36

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- **Bounded matching potential.** -/
theorem matching_potential {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (lam0 lamH : NCol G lab F → ℝ) {L : ℝ} (hL : 0 ≤ L) (hb : ∀ e, |lamH e - lam0 e| ≤ L)
    (hagree : ∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
      ∑ e : NCol G lab F, lamH e * (x e.1 : ℝ) = ∑ e : NCol G lab F, lam0 e * (x e.1 : ℝ)) :
    ∃ t : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t e = lamH e - lam0 e) ∧
      ∀ i, |t i| ≤ (3 / (2 * α ^ 2) + 1) * L := by
  obtain ⟨t0, ht0⟩ := rowSpan_of_annihilates (fun e => lamH e - lam0 e) (fun x hx => by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hagree x hx, sub_self])
  obtain ⟨t, h1, h2⟩ := native_gauge_alpha hα hH3 t0 L hL (fun e => by rw [ht0]; exact hb e)
  exact ⟨t, fun e => (h1 e).trans (ht0 e), h2⟩

/-- Matching potential with the sup norm `‖λ_H − λ₀‖∞` of the difference. -/
theorem matching_potential_norm {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (lam0 lamH : NCol G lab F → ℝ)
    (hagree : ∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
      ∑ e : NCol G lab F, lamH e * (x e.1 : ℝ) = ∑ e : NCol G lab F, lam0 e * (x e.1 : ℝ)) :
    ∃ t : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t e = lamH e - lam0 e) ∧
      ∀ i, |t i| ≤ (3 / (2 * α ^ 2) + 1) * ‖lamH - lam0‖ :=
  matching_potential hα hH3 lam0 lamH (norm_nonneg _) (fun e => by
    have := norm_le_pi_norm (lamH - lam0) e
    rwa [Pi.sub_apply, Real.norm_eq_abs] at this) hagree

/-- Matching potential for two functionals bounded by `A`: `|t_i| ≤ (3/(2α²)+1)·2A`. -/
theorem matching_potential_bounded {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (lam0 lamH : NCol G lab F → ℝ) {A : ℝ} (h0 : ∀ e, |lam0 e| ≤ A) (hH : ∀ e, |lamH e| ≤ A)
    (hagree : ∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
      ∑ e : NCol G lab F, lamH e * (x e.1 : ℝ) = ∑ e : NCol G lab F, lam0 e * (x e.1 : ℝ)) :
    ∃ t : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t e = lamH e - lam0 e) ∧
      ∀ i, |t i| ≤ (3 / (2 * α ^ 2) + 1) * (2 * A) := by
  by_cases hne : Nonempty (NCol G lab F)
  · obtain ⟨e0⟩ := hne
    have hA : 0 ≤ A := (abs_nonneg _).trans (h0 e0)
    exact matching_potential hα hH3 lam0 lamH (by linarith) (fun e =>
      (abs_sub _ _).trans (by linarith [h0 e, hH e])) hagree
  · -- no native columns: then there are no native rows either, and `t = 0` works
    rw [not_nonempty_iff] at hne
    refine ⟨0, fun e => isEmptyElim e, fun i => ?_⟩
    exfalso
    -- a native row has a native column at each member of its component
    obtain ⟨u, hu⟩ : i.1.2.Nonempty := by
      obtain ⟨a, -, ha⟩ := i.2.1
      exact ⟨a, ha ▸ mem_comp_self' _ _⟩
    exact isEmptyElim (⟨s(i.1.1, u), isNCol_root i hu⟩ : NCol G lab F)

end S07V38
