/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ShortKiteF

/-!
# CCJS Lemma 2.7 (short kites)

`shortKiteProp`: in a class-two graph, `ShortKiteProp G` holds. The proof reduces a short kite to
the normal form `SKNF` (degrees of `b, u, cc` equal to `Δ` by CCJS Lemma 2.4 (a); then make `y`
miss the colour `β` missing at `b` and `φ(uy) = β`) and applies Cases 1 and 2.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- With `d(b) = Δ`, `b` misses exactly one colour. -/
theorem IsColMinus.b_only {c : PEC G (Fin G.maxDegree)} {a b : V} (cm : IsColMinus c a b)
    (db : G.degree b = G.maxDegree) {β θ : Fin G.maxDegree} (hβ : c.IsFree b β)
    (hθ : c.IsFree b θ) : θ = β := by
  have hm := cm.card_missing_end (Or.inr rfl)
  rw [db] at hm
  obtain ⟨μ, hμ⟩ := card_eq_one.1 (show #(missing c b) = 1 by omega)
  have e1 : θ ∈ missing c b := mem_missing.2 hθ
  have e2 : β ∈ missing c b := mem_missing.2 hβ
  rw [hμ, mem_singleton] at e1 e2
  rw [e1, e2]

/-- From `y` missing `β`: make `φ(uy) = β` and conclude by Cases 1 and 2. -/
theorem sk_from_state (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u x y : V}
    {β : Fin G.maxDegree} (d6 : Distinct6 a b cc u x y) (db : G.degree b = G.maxDegree)
    (du : G.degree u = G.maxDegree) (dcc : G.degree cc = G.maxDegree) (cm : IsColMinus c a b)
    (βb : c.IsFree b β) (acc : c.col a cc = some β)
    (hbu : ∃ δ, c.col b u = some δ ∧ c.IsFree a δ) (gcu : Good c a b cc u)
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
    fun hz => ksAB_not_reach hG cm hωa βb (Or.inr hyβ) d6.ay.symm d6.by_.symm hz
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
  obtain ⟨ζ, γ, h⟩ := SKNF.of_inv (cm.kempeSwap ω β y) d6 db du dcc ((fb β).2 βb)
    (kcol_keep c acc (Or.inr hya)) (kcol_keep c hbu (Or.inr hyb)) ((fa δ).2 hδa)
    (good_kempeSwap y (Or.inl hωa) (Or.inr βb) hA gcu)
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

/-- **CCJS Lemma 2.7 (short kites)** (Cao–Chen–Shan; general form used in CCJS). -/
theorem shortKiteProp (hG : IsClassTwo G) : ShortKiteProp G := by
  intro c a b cc u x y hnd cm ⟨δ, hbu, hδa⟩ gux ⟨β, hacc, hβb⟩ gcu guy ⟨τx, hτxA, hxτ⟩
    ⟨τy, hτyA, hyτ⟩ hdx hdy
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or, not_false_eq_true] at hnd
  obtain ⟨⟨ab, acc, au, ax, ay⟩, ⟨bcc, bu, bx, by_⟩, ⟨ccu, ccx, ccy⟩, ⟨ux, uy⟩, xy⟩ := hnd
  have d6 : Distinct6 a b cc u x y :=
    ⟨ab, acc, au, ax, ay, bcc, bu, bx, by_, ccu, ccx, ccy, ux, uy, xy⟩
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  obtain ⟨γx, hγx, hγxA⟩ := gux
  have hK : IsK4 c a b u x δ γx := ⟨cm, hbu, hγx, hδa, hγxA, au, ax, bx⟩
  have db : G.degree b = G.maxDegree := by
    by_contra hne
    exact hK.not_common_of_degree_b hG (lt_of_le_of_ne (G.degree_le_maxDegree b) hne) hτxA hxτ
  have du : G.degree u = G.maxDegree := by
    by_contra hne
    exact hK.not_common_of_degree_u hG (lt_of_le_of_ne (G.degree_le_maxDegree u) hne) hτxA hxτ
  have bonly : ∀ {θ}, c.IsFree b θ → θ = β := fun hθ => cm.b_only db hβb hθ
  -- `d(cc) = Δ`, via the Kierstead path `a cc u x` after moving the uncoloured edge to `a cc`
  have dcc : G.degree cc = G.maxDegree := by
    by_contra hne
    obtain ⟨ψ, hcmψ, -, hoff, hψa, hψcc, hψw⟩ := exists_shift cm.symm hacc hβb bcc
    have off' : ∀ p q, p ≠ a → q ≠ a → ψ.col p q = c.col p q := fun p q hp hq =>
      hoff p q (by tauto) (by tauto)
    obtain ⟨ζ, hζ, hζA⟩ := gcu
    have hζβ : ζ ≠ β := by
      rintro rfl
      exact au (c.col_proper (by rw [c.col_symm]; exact hacc) hζ)
    have hA' : ∀ {θ}, InA c a b θ → InA ψ a cc θ := by
      intro θ hθ
      rcases hθ with h | h
      · exact Or.inl ((hψa θ).2 h)
      · rw [bonly h]; exact Or.inr hψcc
    have hK' : IsK4 ψ a cc u x ζ γx :=
      ⟨hcmψ.symm, by rw [off' cc u d6.acc.symm d6.au.symm]; exact hζ,
        by rw [off' u x d6.au.symm d6.ax.symm]; exact hγx,
        (hψa ζ).2 (hζA.resolve_right fun hb => hζβ (bonly hb)), hA' hγxA, au, ax, ccx⟩
    exact hK'.not_common_of_degree_b hG (lt_of_le_of_ne (G.degree_le_maxDegree cc) hne)
      (hA' hτxA) ((hψw x d6.bx.symm d6.ax.symm d6.ccx.symm τx).2 hxτ)
  -- make `y` miss the colour missing at `b`
  by_cases hτβ : τy = β
  · subst hτβ
    exact sk_from_state hG d6 db du dcc cm hβb hacc ⟨δ, hbu, hδa⟩ gcu ⟨γx, hγx, hγxA⟩ guy hyτ
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
  exact sk_from_state hG d6 db du dcc (cm.kempeSwap τy β a) (ksAB_free_b hG cm hτa hβb)
    (kcol_flip₂ c hacc (Reachable.refl a)) hbu1
    (good_kempeSwap a (Or.inl hτa) (Or.inr hβb) hA1 gcu)
    (good_kempeSwap a (Or.inl hτa) (Or.inr hβb) hA1 ⟨γx, hγx, hγxA⟩)
    (good_kempeSwap a (Or.inl hτa) (Or.inr hβb) hA1 guy)
    ((ksAB_free_other hG cm hτa hβb d6.ay.symm d6.by_.symm τy).2 hyτ)
    ⟨τx, (hA1 τx).2 hτxA, (ksAB_free_other hG cm hτa hβb d6.ax.symm d6.bx.symm τx).2 hxτ⟩

end Overfull
