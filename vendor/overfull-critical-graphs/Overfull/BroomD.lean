/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.BroomB

/-!
# Brooms with two leaves, part D

`σ ≠ γ` when `x` misses `β` (copied from `ShortKiteD` without the vertex `c`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace BNF

variable {c : PEC G (Fin G.maxDegree)} {a b u x y : V} {β δ γ σ : Fin G.maxDegree}

/-- `σ ≠ γ` when `x` misses `β`: otherwise `(u; b, y, x)` is a multifan in `G − bu` with `b` and
`x` both missing `β`. -/
theorem σγ_of_xβ (hG : IsClassTwo G) (h : BNF c a b u x y β δ γ σ)
    (hxβ : c.IsFree x β) : σ ≠ γ := by
  intro e
  have d5 := h.d5
  obtain ⟨ψ, hcmψ, -, hoff, hψb, -, hψw⟩ := exists_shift h.cm h.hbu h.δa d5.au
  have off' : ∀ w, w ≠ a → w ≠ b → ψ.col u w = c.col u w := fun w hwa hwb =>
    hoff u w (by have := d5.au; tauto) (by have := d5.bu; tauto)
  let f : ℕ → V := fun i => if i = 0 then b else if i = 1 then y else x
  have hF : IsMultifan ψ u 3 f := by
    refine ⟨by omega, by simp only [f, if_true]; exact hcmψ.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact (c.col_adj h.hbu).symm
      · exact c.col_adj h.huy
      · exact c.col_adj h.hux
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
        simp only [f, if_true, if_false, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
          show (2 : ℕ) ≠ 1 by omega] at hij ⊢
      · exact absurd hij d5.by_
      · exact absurd hij d5.bx
      · exact absurd hij d5.by_.symm
      · exact absurd hij d5.xy.symm
      · exact absurd hij d5.bx.symm
      · exact absurd hij d5.xy
    · rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · refine ⟨0, by omega, β, ?_, ?_⟩
        · simp only [f, show (1 : ℕ) ≠ 0 by omega, if_false, if_true]
          rw [off' y d5.ay.symm d5.by_.symm]; exact h.huy
        · simp only [f, if_true]; exact (hψb β).2 h.βb
      · refine ⟨1, by omega, γ, ?_, ?_⟩
        · simp only [f, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, if_false]
          rw [off' x d5.ax.symm d5.bx.symm]; exact h.hux
        · simp only [f, show (1 : ℕ) ≠ 0 by omega, if_false, if_true]
          rw [← e]; exact (hψw y d5.ay.symm d5.by_.symm d5.uy.symm σ).2 h.σy
  obtain ⟨-, hA', -⟩ := multifan_elementary hG 3 ψ u f hcmψ hF
  exact hA' 0 (by omega) 2 (by omega) (by omega) β (by simpa [f] using (hψb β).2 h.βb)
    (by simpa [f] using (hψw x d5.ax.symm d5.bx.symm d5.ux.symm β).2 hxβ)

end BNF

end Overfull
