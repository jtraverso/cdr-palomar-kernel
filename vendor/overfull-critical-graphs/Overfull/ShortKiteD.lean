/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ShortKiteC

/-!
# Short kites, part D: the end of Case 2

In the normal form, if `x` misses `β` (the colour missing at `b`), the short kite is impossible:
swap the `a`–`b` chain `(γ, β)` (`γ = φ(ux)`), recolour `bu` by `γ`, colour `ab` by `δ` and uncolour
`ux`; then `(u; x, y)` is a multifan, and four Kempe swaps at `a` produce the `(δ, γ)`-chain
`u b a` ending at `a`, while `u` and `x` must be `(δ, γ)`-linked.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Linkage in a two-vertex multifan `(u; x, y)` of a colouring of `G − ux`. -/
theorem fan2_link (hG : IsClassTwo G) {d : PEC G (Fin G.maxDegree)} {u x y : V}
    (hcm : IsColMinus d u x) {β : Fin G.maxDegree} (huy : d.col u y = some β)
    (hxβ : d.IsFree x β) (hxy : x ≠ y) {θ η : Fin G.maxDegree} (hu : d.IsFree u θ)
    (hy : d.IsFree y η) : (d.kempeGraph θ η).Reachable u y := by
  have hF : IsMultifan d u 2 (fun i => if i = 0 then x else y) := by
    refine ⟨by omega, by simp only [if_true]; exact hcm.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact hcm.adj
      · exact d.col_adj huy
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using hxy)
      · exact absurd hij (by simpa using hxy.symm)
      · rfl
    · refine ⟨0, hi0, β, ?_, by simpa using hxβ⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact huy
  obtain ⟨-, -, hB⟩ := multifan_elementary hG 2 d u _ hcm hF
  simpa using hB 1 (by omega) θ η hu (by simpa using hy)

namespace SKNF

variable {c : PEC G (Fin G.maxDegree)} {a b cc u x y : V} {β δ ζ γ σ : Fin G.maxDegree}

/-- `σ ≠ γ` when `x` misses `β`: otherwise `(u; b, y, x)` is a multifan in `G − bu` with `b` and
`x` both missing `β`. -/
theorem σγ_of_xβ (hG : IsClassTwo G) (h : SKNF c a b cc u x y β δ ζ γ σ)
    (hxβ : c.IsFree x β) : σ ≠ γ := by
  intro e
  have d6 := h.d6
  obtain ⟨ψ, hcmψ, -, hoff, hψb, -, hψw⟩ := exists_shift h.cm h.hbu h.δa d6.au
  have off' : ∀ w, w ≠ a → w ≠ b → ψ.col u w = c.col u w := fun w hwa hwb =>
    hoff u w (by have := d6.au; tauto) (by have := d6.bu; tauto)
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
      · exact absurd hij d6.by_
      · exact absurd hij d6.bx
      · exact absurd hij d6.by_.symm
      · exact absurd hij d6.xy.symm
      · exact absurd hij d6.bx.symm
      · exact absurd hij d6.xy
    · rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · refine ⟨0, by omega, β, ?_, ?_⟩
        · simp only [f, show (1 : ℕ) ≠ 0 by omega, if_false, if_true]
          rw [off' y d6.ay.symm d6.by_.symm]; exact h.huy
        · simp only [f, if_true]; exact (hψb β).2 h.βb
      · refine ⟨1, by omega, γ, ?_, ?_⟩
        · simp only [f, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, if_false]
          rw [off' x d6.ax.symm d6.bx.symm]; exact h.hux
        · simp only [f, show (1 : ℕ) ≠ 0 by omega, if_false, if_true]
          rw [← e]; exact (hψw y d6.ay.symm d6.by_.symm d6.uy.symm σ).2 h.σy
  obtain ⟨-, hA', -⟩ := multifan_elementary hG 3 ψ u f hcmψ hF
  exact hA' 0 (by omega) 2 (by omega) (by omega) β (by simpa [f] using (hψb β).2 h.βb)
    (by simpa [f] using (hψw x d6.ax.symm d6.bx.symm d6.ux.symm β).2 hxβ)

end SKNF

end Overfull
