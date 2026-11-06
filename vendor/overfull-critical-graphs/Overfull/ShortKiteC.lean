/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ShortKiteB

/-!
# Short kites, part C: Case 1

If `x` and `y` miss the same colour `σ ∈ φ̄(a)`, the short kite is impossible. Either the core
argument works with `b`, or (after colouring `ab` by `β` and uncolouring `a cc`) with `cc`; if both
fail, `u`, `b`, `cc` are three ends of one `(β, γ)`-chain in `G − ab − ux − a cc`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace SKNF

variable {c : PEC G (Fin G.maxDegree)} {a b cc u x y : V} {β δ ζ γ σ : Fin G.maxDegree}

/-- The normal form with the roles of `b` and `cc` exchanged. -/
theorem swap_version (h : SKNF c a b cc u x y β δ ζ γ σ) :
    ∃ ψ : PEC G (Fin G.maxDegree), SKNF ψ a cc b u x y β ζ δ γ σ ∧
      (∀ ε, ψ.IsFree x ε ↔ c.IsFree x ε) ∧
      (∀ p q, ¬ ((p = b ∧ q = a) ∨ (p = a ∧ q = b)) → ¬ ((p = a ∧ q = cc) ∨ (p = cc ∧ q = a)) →
        ψ.col p q = c.col p q) ∧ ψ.col a b = some β ∧ ψ.col a cc = none := by
  have d6 := h.d6
  obtain ⟨ψ, hcm, hψba, hoff, hψa, hψcc, hψw⟩ := exists_shift h.cm.symm h.acc h.βb d6.bcc
  have off' : ∀ p q, p ≠ a → q ≠ a → ψ.col p q = c.col p q := fun p q hp hq =>
    hoff p q (by tauto) (by tauto)
  refine ⟨ψ, ⟨hcm.symm, d6.swap, h.dcc, h.du, h.db, hψcc, by rw [ψ.col_symm]; exact hψba,
    by rw [off' cc u d6.acc.symm d6.au.symm]; exact h.hcu, (hψa ζ).2 h.ζa,
    by rw [off' b u d6.ab.symm d6.au.symm]; exact h.hbu, (hψa δ).2 h.δa,
    by rw [off' u x d6.au.symm d6.ax.symm]; exact h.hux, Or.inl ((hψa γ).2 h.γa),
    by rw [off' u y d6.au.symm d6.ay.symm]; exact h.huy,
    (hψw y d6.by_.symm d6.ay.symm d6.ccy.symm σ).2 h.σy, (hψa σ).2 h.σa⟩,
    hψw x d6.bx.symm d6.ax.symm d6.ccx.symm, hoff, by rw [ψ.col_symm]; exact hψba,
    by rw [ψ.col_symm]; exact hcm.uncol⟩

/-- **Case 1.** `x` and `y` cannot miss the same colour `σ`. -/
theorem case1 (hG : IsClassTwo G) (h : SKNF c a b cc u x y β δ ζ γ σ) (hxσ : c.IsFree x σ) :
    False := by
  have d6 := h.d6
  by_cases hR : ((unsetEdge c u x).kempeGraph β γ).Reachable u b
  swap
  · exact h.case1_core hG hxσ hR
  obtain ⟨ψ, hψ, hψx, hoff, hψab, hψacc⟩ := h.swap_version
  by_cases hR' : ((unsetEdge ψ u x).kempeGraph β γ).Reachable u cc
  swap
  · exact hψ.case1_core hG ((hψx σ).2 hxσ) hR'
  -- the common graph `G₀`
  set φ₁ := unsetEdge c u x with hφ₁
  set φ₀ := unsetEdge φ₁ a cc with hφ₀
  have hφ₁acc : φ₁.col a cc = some β := by
    rw [hφ₁, unsetEdge_col_of_ne c (by have := d6.au; have := d6.ax; tauto)]; exact h.acc
  have hcol₀ : ∀ p q, ¬ ((p = a ∧ q = cc) ∨ (p = cc ∧ q = a)) → φ₀.col p q = φ₁.col p q :=
    fun p q hpq => unsetEdge_col_of_ne φ₁ hpq
  have hiso : ∀ q, ¬ (φ₀.kempeGraph β γ).Adj a q := by
    rintro q ⟨hne, hc⟩
    by_cases hq : q = cc
    · subst hq
      rw [hφ₀, unsetEdge_col_self] at hc
      rcases hc with hc | hc <;> cases hc
    rw [hcol₀ a q (by tauto), hφ₁, unsetEdge_col_of_ne c (by have := d6.au; have := d6.ax; tauto)]
      at hc
    rcases hc with hc | hc
    · exact hq (c.col_proper hc h.acc)
    · exact h.γa q hc
  have r1 : (φ₀.kempeGraph β γ).Reachable u b := by
    refine reach_of_pendant (a := a) (w := cc) (fun p q hpq => ?_) hiso d6.acc.symm d6.au.symm
      d6.ab.symm hR
    by_cases he : (p = a ∧ q = cc) ∨ (p = cc ∧ q = a)
    · right
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    · left
      obtain ⟨hne, hc⟩ := hpq
      exact ⟨hne, by rw [hcol₀ p q he]; exact hc⟩
  have r2 : (φ₀.kempeGraph β γ).Reachable u cc := by
    refine reach_of_pendant (a := a) (w := b) (fun p q hpq => ?_) hiso d6.ab.symm d6.au.symm
      d6.acc.symm hR'
    by_cases he : (p = a ∧ q = b) ∨ (p = b ∧ q = a)
    · right
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    left
    obtain ⟨hne, hc⟩ := hpq
    refine ⟨hne, ?_⟩
    by_cases hux : (p = u ∧ q = x) ∨ (p = x ∧ q = u)
    · exfalso
      have : (unsetEdge ψ u x).col p q = none := by
        rcases hux with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self ψ u x
        · rw [PEC.col_symm]; exact unsetEdge_col_self ψ u x
      rw [this] at hc
      rcases hc with hc | hc <;> cases hc
    rw [unsetEdge_col_of_ne ψ hux] at hc
    by_cases hacc : (p = a ∧ q = cc) ∨ (p = cc ∧ q = a)
    · exfalso
      have : ψ.col p q = none := by
        rcases hacc with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact hψacc
        · rw [ψ.col_symm]; exact hψacc
      rw [this] at hc
      rcases hc with hc | hc <;> cases hc
    rw [hoff p q (by tauto) hacc] at hc
    rw [hcol₀ p q hacc, hφ₁, unsetEdge_col_of_ne c hux]
    exact hc
  -- three ends
  have f0u : φ₀.IsFree u γ := (isFree_unsetEdge_of_ne φ₁ d6.au.symm d6.ccu.symm γ).2
    ((isFree_unsetEdge_left c d6.ux h.hux γ).2 (Or.inl rfl))
  have f0b : φ₀.IsFree b β := (isFree_unsetEdge_of_ne φ₁ d6.ab.symm d6.bcc β).2
    ((isFree_unsetEdge_of_ne c d6.bu d6.bx β).2 h.βb)
  have f0cc : φ₀.IsFree cc β := (isFree_unsetEdge_right φ₁ d6.acc hφ₁acc β).2 (Or.inl rfl)
  exact not_three_linked φ₀ d6.bu.symm d6.ccu.symm d6.bcc (Or.inr f0u) (Or.inl f0b)
    (Or.inl f0cc) r1 r2

end SKNF

end Overfull
