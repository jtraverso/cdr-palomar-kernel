/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.BroomC

/-!
# Brooms with two leaves (Chen–Cao, Lemma 3.1)

`broomProp`: in a class-two graph, for `φ ∈ C^Δ(G − ab)` with `φ(bu) ∈ φ̄(a)` and `φ(ux), φ(uy)`
in `A = φ̄(a) ∪ φ̄(b)`, the vertices `x` and `y` cannot both miss a colour of `A`. This is Lemma 3.1
of Chen–Cao (arXiv:2512.07252), the case of Theorem 1.1 for a broom with two leaves, and the short
kite lemma of CCJS (Lemma 2.7) without its vertex `c` and without degree conditions.

The proof follows the short kite: `d(b) = d(u) = Δ` by CCJS Lemma 2.4 (a); Kempe changes reach the
normal form `BNF`; Case 1 (`BroomC`) and Case 2 (`BroomF`, `BroomE`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Chen–Cao Lemma 3.1 (brooms with two leaves). -/
def BroomProp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (c : PEC G (Fin G.maxDegree)) (a b u x y : V),
    [a, b, u, x, y].Nodup → IsColMinus c a b →
    (∃ δ, c.col b u = some δ ∧ c.IsFree a δ) → Good c a b u x → Good c a b u y →
    (∃ θ, InA c a b θ ∧ c.IsFree x θ) → (∃ θ, InA c a b θ ∧ c.IsFree y θ) → False

/-- From `y` missing `β`: make `φ(uy) = β` and conclude by Cases 1 and 2. -/
theorem broom_from_state (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u x y : V}
    {β : Fin G.maxDegree} (d5 : Distinct5 a b u x y) (db : G.degree b = G.maxDegree)
    (du : G.degree u = G.maxDegree) (cm : IsColMinus c a b) (βb : c.IsFree b β)
    (hbu : ∃ δ, c.col b u = some δ ∧ c.IsFree a δ)
    (gux : Good c a b u x) (guy : Good c a b u y) (hyβ : c.IsFree y β)
    (hx : ∃ τ, InA c a b τ ∧ c.IsFree x τ) : False := by
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  obtain ⟨δ, hbu, hδa⟩ := hbu
  obtain ⟨ω, hω, hωA⟩ := guy
  have hωβ : ω ≠ β := fun e => hyβ u (by rw [c.col_symm, hω, e])
  have hωa : c.IsFree a ω := hωA.resolve_right fun hb => hωβ (cm.b_only db βb hb)
  -- swap the `(β, ω)`-chain of `y`
  have hl := ksAB_link hG cm hωa βb
  have hny : ∀ {z}, (c.kempeGraph ω β).Reachable y z → ¬ (c.kempeGraph ω β).Reachable a z :=
    fun hz => ksAB_not_reach hG cm hωa βb (Or.inr hyβ) d5.ay.symm d5.by_.symm hz
  have hya : ¬ (c.kempeGraph ω β).Reachable y a := fun r => hny r (Reachable.refl a)
  have hyb : ¬ (c.kempeGraph ω β).Reachable y b := fun r => hny r hl
  set c' := c.kempeSwap ω β y with hc'
  have fa := kfree_off c hya
  have fb := kfree_off c hyb
  have hA : ∀ ε, InA c' a b ε ↔ InA c a b ε := fun ε => by unfold InA; rw [fa, fb]
  have hx' : ∃ τ, InA c' a b τ ∧ c'.IsFree x τ := by
    obtain ⟨τ, hτA, hxτ⟩ := hx
    by_cases hr : (c.kempeGraph ω β).Reachable y x
    · refine ⟨Equiv.swap ω β τ, (hA _).2 ?_, ?_⟩
      · by_cases h1 : τ = ω
        · subst h1; rw [Equiv.swap_apply_left]; exact Or.inr βb
        by_cases h2 : τ = β
        · subst h2; rw [Equiv.swap_apply_right]; exact Or.inl hωa
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hτA
      · rw [isFree_kempeSwap_of_reachable c ω β hr, Equiv.swap_apply_self]; exact hxτ
    · exact ⟨τ, (hA τ).2 hτA, (kfree_off c hr τ).2 hxτ⟩
  obtain ⟨γ, h⟩ := BNF.of_inv (cm.kempeSwap ω β y) d5 db du ((fb β).2 βb)
    (kcol_keep c hbu (Or.inr hyb)) ((fa δ).2 hδa)
    (good_kempeSwap y (Or.inl hωa) (Or.inr βb) hA gux)
    (by rw [c'.col_symm]; exact kcol_flip₁ c (by rw [c.col_symm]; exact hω) (Reachable.refl y))
    ((kfree_flip₂ c (Reachable.refl y)).2 hyβ) ((fa ω).2 hωa)
  -- dispatch on the colour of `A` missing at `x`
  obtain ⟨τ, hτA, hxτ⟩ := hx'
  by_cases h1 : τ = ω
  · rw [h1] at hxτ; exact h.case1 hG hxτ
  by_cases h2 : τ = β
  · rw [h2] at hxτ; exact h.case2_final hG hxτ
  exact h.case2 hG hxτ (h.free_a_of_inA hτA h2) h1


set_option maxHeartbeats 1600000 in
/-- **Chen–Cao Lemma 3.1 (brooms with two leaves).** -/
theorem broomProp (hG : IsClassTwo G) : BroomProp G := by
  intro c a b u x y hnd cm ⟨δ, hbu, hδa⟩ gux guy ⟨τx, hτxA, hxτ⟩ ⟨τy, hτyA, hyτ⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or, not_false_eq_true] at hnd
  obtain ⟨⟨ab, au, ax, ay⟩, ⟨bu, bx, by_⟩, ⟨ux, uy⟩, xy⟩ := hnd
  have d5 : Distinct5 a b u x y := ⟨ab, au, ax, ay, bu, bx, by_, ux, uy, xy⟩
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  obtain ⟨γx, hγx, hγxA⟩ := gux
  have hK : IsK4 c a b u x δ γx := ⟨cm, hbu, hγx, hδa, hγxA, au, ax, bx⟩
  have db : G.degree b = G.maxDegree := by
    by_contra hne
    exact hK.not_common_of_degree_b hG (lt_of_le_of_ne (G.degree_le_maxDegree b) hne) hτxA hxτ
  have du : G.degree u = G.maxDegree := by
    by_contra hne
    exact hK.not_common_of_degree_u hG (lt_of_le_of_ne (G.degree_le_maxDegree u) hne) hτxA hxτ
  obtain ⟨β, hβb⟩ := cm.exists_free_right
  have bonly : ∀ {θ}, c.IsFree b θ → θ = β := fun hθ => cm.b_only db hβb hθ
  -- make `y` miss the colour missing at `b`
  by_cases hτβ : τy = β
  · subst hτβ
    exact broom_from_state hG d5 db du cm hβb ⟨δ, hbu, hδa⟩ ⟨γx, hγx, hγxA⟩ guy hyτ
      ⟨τx, hτxA, hxτ⟩
  have hτa : c.IsFree a τy := hτyA.resolve_right fun hb => hτβ (bonly hb)
  set c₁ := c.kempeSwap τy β a with hc₁
  have hA1 := ksAB_inA hG cm hτa hβb
  have hbu1 : ∃ δ', c₁.col b u = some δ' ∧ c₁.IsFree a δ' := by
    by_cases hδτ : δ = τy
    · subst hδτ
      exact ⟨β, kcol_flip₁ c hbu (ksAB_link hG cm hδa hβb), ksAB_free_a hG cm hδa hβb⟩
    · have hδβ : δ ≠ β := fun e => hdis δ hδa (e ▸ hβb)
      exact ⟨δ, kcol_keep c hbu (Or.inl ⟨hδτ, hδβ⟩), (ksAB_free_a_of_ne hG cm hτa hβb hδτ hδβ).2 hδa⟩
  exact broom_from_state hG d5 db du (cm.kempeSwap τy β a) (ksAB_free_b hG cm hτa hβb) hbu1
    (good_kempeSwap a (Or.inl hτa) (Or.inr hβb) hA1 ⟨γx, hγx, hγxA⟩)
    (good_kempeSwap a (Or.inl hτa) (Or.inr hβb) hA1 guy)
    ((ksAB_free_other hG cm hτa hβb d5.ay.symm d5.by_.symm τy).2 hyτ)
    ⟨τx, (hA1 τx).2 hτxA, (ksAB_free_other hG cm hτa hβb d5.ax.symm d5.bx.symm τx).2 hxτ⟩

end Overfull
