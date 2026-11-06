/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.BroomF

/-!
# Brooms with two leaves, part C: Case 1

If `x` and `y` both miss `σ`, the broom is impossible (Chen–Cao, proof of Theorem 1.1, Subcase A.1,
for two leaves). Either `case1_core` applies, or after uncolouring `ux` the `(β, γ)`-chain of `u`
reaches `b`. In that case uncolour `uy` instead: the `(β, γ)`-chain of `y` ends at `b`; swapping it
and colouring `ab` by `γ` gives a colouring of `G − uy` in which `(u; y, x)` is a multifan
(`φ(ux) = γ` is missing at `y`) with `σ` missing at both `x` and `y`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace BNF

variable {c : PEC G (Fin G.maxDegree)} {a b u x y : V} {β δ γ σ : Fin G.maxDegree}

set_option maxHeartbeats 1600000 in
/-- **Case 1.** `x` and `y` cannot miss the same colour `σ`. -/
theorem case1 (hG : IsClassTwo G) (h : BNF c a b u x y β δ γ σ) (hxσ : c.IsFree x σ) : False := by
  have d5 := h.d5
  by_cases hR : ((unsetEdge c u x).kempeGraph β γ).Reachable u b
  swap
  · exact h.case1_core hG hxσ hR
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hγβ := h.γβ
  have hγa := h.γa
  have hσβ : σ ≠ β := fun e => hdis σ h.σa (e ▸ h.βb)
  have hσγ : σ ≠ γ := fun e => hxσ u (by rw [c.col_symm, e]; exact h.hux)
  set φ₁ := unsetEdge c u x with hφ₁
  set φ₂ := unsetEdge φ₁ u y with hφ₂
  have c1uy : φ₁.col u y = some β := by
    rw [hφ₁, unsetEdge_col_of_ne c (not_pair (Or.inr d5.xy.symm) (Or.inl d5.ux))]; exact h.huy
  have f2uβ : φ₂.IsFree u β := (isFree_unsetEdge_left φ₁ d5.uy c1uy β).2 (Or.inl rfl)
  have f2uγ : φ₂.IsFree u γ := (isFree_unsetEdge_left φ₁ d5.uy c1uy γ).2
    (Or.inr ((isFree_unsetEdge_left c d5.ux h.hux γ).2 (Or.inl rfl)))
  -- the chain of `u` leaves through `uy`, so the chain of `y` in `G − ab − ux − uy` reaches `b`
  have hsub : ∀ p q, (φ₁.kempeGraph β γ).Adj p q →
      (φ₂.kempeGraph β γ).Adj p q ∨ s(p, q) = s(u, y) := by
    rintro p q ⟨hne, hc⟩
    by_cases e : (p = u ∧ q = y) ∨ (p = y ∧ q = u)
    · right
      rcases e with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
      exact Sym2.eq_swap
    · left; exact ⟨hne, by rw [hφ₂, unsetEdge_col_of_ne φ₁ e]; exact hc⟩
  have hyb : (φ₂.kempeGraph β γ).Reachable y b := by
    rcases reach_split hsub hR with r | r
    · exact absurd (eq_of_reachable_of_free_both φ₂ f2uβ f2uγ r) d5.bu
    · exact r
  set ψ := unsetEdge c u y with hψ
  have hyb' : (ψ.kempeGraph β γ).Reachable y b := by
    refine reachable_mono_of_agree (fun p q hpq => ?_) hyb
    by_cases e1 : (p = u ∧ q = y) ∨ (p = y ∧ q = u)
    · exfalso
      have : φ₂.col p q = none := by
        rcases e1 with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self φ₁ u y
        · rw [PEC.col_symm]; exact unsetEdge_col_self φ₁ u y
      rw [this] at hpq
      rcases hpq with e | e <;> cases e
    by_cases e2 : (p = u ∧ q = x) ∨ (p = x ∧ q = u)
    · exfalso
      have : φ₂.col p q = none := by
        rw [hφ₂, unsetEdge_col_of_ne φ₁ e1]
        rcases e2 with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self c u x
        · rw [PEC.col_symm]; exact unsetEdge_col_self c u x
      rw [this] at hpq
      rcases hpq with e | e <;> cases e
    rw [hψ, unsetEdge_col_of_ne c e1, hφ₂, unsetEdge_col_of_ne φ₁ e1, hφ₁,
      unsetEdge_col_of_ne c e2]
  -- facts in ψ
  have cψuy : c.col u y = some β := h.huy
  have ψyβ : ψ.IsFree y β := (isFree_unsetEdge_right c d5.uy cψuy β).2 (Or.inl rfl)
  have ψuβ : ψ.IsFree u β := (isFree_unsetEdge_left c d5.uy cψuy β).2 (Or.inl rfl)
  have ψbβ : ψ.IsFree b β := (isFree_unsetEdge_of_ne c d5.bu d5.by_ β).2 h.βb
  have ψaγ : ψ.IsFree a γ := (isFree_unsetEdge_of_ne c d5.au d5.ay γ).2 hγa
  have ψyσ : ψ.IsFree y σ := (isFree_unsetEdge_right c d5.uy cψuy σ).2 (Or.inr h.σy)
  have ψxσ : ψ.IsFree x σ := (isFree_unsetEdge_of_ne c d5.ux.symm d5.xy σ).2 hxσ
  have ψux : ψ.col u x = some γ := by
    rw [hψ, unsetEdge_col_of_ne c (not_pair (Or.inr d5.xy) (Or.inl d5.uy))]; exact h.hux
  have nu : ¬ (ψ.kempeGraph β γ).Reachable y u := fun r =>
    not_three_linked ψ d5.by_.symm d5.uy.symm d5.bu (Or.inl ψyβ) (Or.inl ψbβ) (Or.inl ψuβ) hyb' r
  have na : ¬ (ψ.kempeGraph β γ).Reachable y a := fun r =>
    not_three_linked ψ d5.by_.symm d5.ay.symm d5.ab.symm (Or.inl ψyβ) (Or.inl ψbβ) (Or.inr ψaγ)
      hyb' r
  -- swap the `(β, γ)`-chain of `y` and colour `ab` by `γ`
  set φ' := ψ.kempeSwap β γ y with hφ'
  have f'yγ : φ'.IsFree y γ := (kfree_flip₁ ψ (Reachable.refl y)).2 ψyβ
  have f'bγ : φ'.IsFree b γ := (kfree_flip₁ ψ hyb').2 ψbβ
  have f'aγ : φ'.IsFree a γ := (kfree_off ψ na γ).2 ψaγ
  have c'ux : φ'.col u x = some γ := kcol_keep ψ ψux (Or.inr nu)
  have f'yσ : φ'.IsFree y σ := (kfree_of_ne ψ hσβ hσγ).2 ψyσ
  have f'xσ : φ'.IsFree x σ := (kfree_of_ne ψ hσβ hσγ).2 ψxσ
  set φ'' := φ'.setEdge γ h.cm.adj f'aγ f'bγ with hφ''
  have off : ∀ p q, ¬ ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) → φ''.col p q = φ'.col p q :=
    fun p q e => setEdge_col_off φ' h.cm.adj f'aγ f'bγ e
  have hcm'' : IsColMinus φ'' u y := by
    refine ⟨c.col_adj h.huy, ?_, fun p q hpq hne => ?_⟩
    · rw [off u y (not_pair (Or.inl d5.au.symm) (Or.inl d5.bu.symm)), hφ']
      exact kempeSwap_col_none ψ β γ y (unsetEdge_col_self c u y)
    · by_cases e : (p = a ∧ q = b) ∨ (p = b ∧ q = a)
      · rw [hφ'', setEdge_col, updFun, if_pos e]; exact Option.some_ne_none _
      rw [off p q e, hφ']
      refine extends_kempeSwap ψ β γ y p q ?_
      have e' : ¬ ((p = u ∧ q = y) ∨ (p = y ∧ q = u)) := by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hne rfl
        · exact hne Sym2.eq_swap
      rw [hψ, unsetEdge_col_of_ne c e']
      refine h.cm.total p q hpq fun he => e ?_
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have c''ux : φ''.col u x = some γ := by
    rw [off u x (not_pair (Or.inl d5.au.symm) (Or.inl d5.bu.symm))]; exact c'ux
  have f''yγ : φ''.IsFree y γ :=
    (isFree_setEdge_of_ne φ' γ h.cm.adj f'aγ f'bγ d5.ay.symm d5.by_.symm γ).2 f'yγ
  have f''yσ : φ''.IsFree y σ :=
    (isFree_setEdge_of_ne φ' γ h.cm.adj f'aγ f'bγ d5.ay.symm d5.by_.symm σ).2 f'yσ
  have f''xσ : φ''.IsFree x σ :=
    (isFree_setEdge_of_ne φ' γ h.cm.adj f'aγ f'bγ d5.ax.symm d5.bx.symm σ).2 f'xσ
  -- the multifan `(u; y, x)`
  have hF : IsMultifan φ'' u 2 (fun i => if i = 0 then y else x) := by
    refine ⟨by omega, by simp only [if_true]; exact hcm''.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact hcm''.adj
      · exact c.col_adj h.hux
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using d5.xy.symm)
      · exact absurd hij (by simpa using d5.xy)
      · rfl
    · refine ⟨0, hi0, γ, ?_, by simpa using f''yγ⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact c''ux
  obtain ⟨-, hA', -⟩ := multifan_elementary hG 2 φ'' u _ hcm'' hF
  exact hA' 0 (by omega) 1 (by omega) (by omega) σ (by simpa using f''yσ) (by simpa using f''xσ)

end BNF

end Overfull
