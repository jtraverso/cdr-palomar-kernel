/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Theorem12d

/-!
# Short kites, part A: the normal form and general tools

`SKNF c a b cc u x y β δ ζ γ σ` is the normal form of a short kite reached after the
normalisations of `NOTES_KITES.md`: `φ̄(b) = {β}`, `φ(a cc) = β`, `φ(bu) = δ ∈ φ̄(a)`,
`φ(cc u) = ζ ∈ φ̄(a)`, `φ(ux) = γ ∈ A`, `φ(uy) = β`, `y` misses `σ ∈ φ̄(a)`, and
`d(b) = d(u) = d(cc) = Δ`.

* `reach_of_pendant`: adding an edge at a vertex isolated in the smaller graph does not create
  new reachability between other vertices.
* `IsColMinus.extends_of`: a colouring extending a colouring of `G − ab` with `ab` uncoloured is
  again a colouring of `G − ab`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Pendant lemma.** If every edge of `H'` is an edge of `H` or the edge `aw`, and `a` is
isolated in `H`, then `H'`-reachability between vertices other than `a` is `H`-reachability. -/
theorem reach_of_pendant {H H' : SimpleGraph V} {a w : V}
    (hsub : ∀ p q, H'.Adj p q → H.Adj p q ∨ s(p, q) = s(a, w)) (hiso : ∀ q, ¬ H.Adj a q)
    (hwa : w ≠ a) {u z : V} (hua : u ≠ a) (hza : z ≠ a) (h : H'.Reachable u z) :
    H.Reachable u z := by
  have key : ∀ v, H'.Reachable u v → (v ≠ a → H.Reachable u v) ∧ (v = a → H.Reachable u w) := by
    intro v hv
    rw [reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact ⟨fun _ => Reachable.refl u, fun h => absurd h hua⟩
    | tail _ hadj ih =>
      rename_i p q _
      rcases hsub p q hadj with hpq | he
      · have hpa : p ≠ a := fun e => hiso q (e ▸ hpq)
        have hqa : q ≠ a := fun e => hiso p (e ▸ hpq.symm)
        exact ⟨fun _ => (ih.1 hpa).trans hpq.reachable, fun e => absurd e hqa⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨fun _ => ih.2 rfl, fun e => absurd e hwa⟩
        · exact ⟨fun e => absurd rfl e, fun _ => ih.1 hwa⟩
  exact (key z h).1 hza

/-- A colouring extending one of `G − ab`, with `ab` still uncoloured, is one of `G − ab`. -/
theorem IsColMinus.extends_of {k : ℕ} {c d : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b)
    (hext : Extends c d) (hun : d.col a b = none) : IsColMinus d a b :=
  ⟨hcm.adj, hun, fun p q hpq hne => hext p q (hcm.total p q hpq hne)⟩

theorem extends_unset_set {k : ℕ} {c : PEC G (Fin k)} {x y : V} {θ : Fin k} (hadj : G.Adj x y)
    (hx : (unsetEdge c x y).IsFree x θ) (hy : (unsetEdge c x y).IsFree y θ) :
    Extends c ((unsetEdge c x y).setEdge θ hadj hx hy) := by
  intro p q h
  rw [setEdge_col]
  unfold updFun
  split_ifs with hpq
  · exact Option.some_ne_none _
  · rw [unsetEdge_col_of_ne c hpq]; exact h

/-- Six distinct vertices. -/
structure Distinct6 (a b cc u x y : V) : Prop where
  ab : a ≠ b
  acc : a ≠ cc
  au : a ≠ u
  ax : a ≠ x
  ay : a ≠ y
  bcc : b ≠ cc
  bu : b ≠ u
  bx : b ≠ x
  by_ : b ≠ y
  ccu : cc ≠ u
  ccx : cc ≠ x
  ccy : cc ≠ y
  ux : u ≠ x
  uy : u ≠ y
  xy : x ≠ y

theorem Distinct6.swap {a b cc u x y : V} (h : Distinct6 a b cc u x y) :
    Distinct6 a cc b u x y :=
  ⟨h.acc, h.ab, h.au, h.ax, h.ay, h.bcc.symm, h.ccu, h.ccx, h.ccy, h.bu, h.bx, h.by_, h.ux, h.uy,
    h.xy⟩

/-- The normal form of a short kite. -/
structure SKNF (c : PEC G (Fin G.maxDegree)) (a b cc u x y : V) (β δ ζ γ σ : Fin G.maxDegree) :
    Prop where
  cm : IsColMinus c a b
  d6 : Distinct6 a b cc u x y
  db : G.degree b = G.maxDegree
  du : G.degree u = G.maxDegree
  dcc : G.degree cc = G.maxDegree
  βb : c.IsFree b β
  acc : c.col a cc = some β
  hbu : c.col b u = some δ
  δa : c.IsFree a δ
  hcu : c.col cc u = some ζ
  ζa : c.IsFree a ζ
  hux : c.col u x = some γ
  γA : InA c a b γ
  huy : c.col u y = some β
  σy : c.IsFree y σ
  σa : c.IsFree a σ

namespace SKNF

variable {c : PEC G (Fin G.maxDegree)} {a b cc u x y : V} {β δ ζ γ σ : Fin G.maxDegree}
  (h : SKNF c a b cc u x y β δ ζ γ σ)
include h

theorem full_of_deg {v : V} (hva : v ≠ a) (hvb : v ≠ b) (hv : G.degree v = G.maxDegree)
    (θ : Fin G.maxDegree) : ¬ c.IsFree v θ := fun hf => by
  have := h.cm.card_missing_other hva hvb
  have : 0 < #(missing c v) := card_pos.2 ⟨θ, mem_missing.2 hf⟩
  omega

theorem u_full (θ : Fin G.maxDegree) : ¬ c.IsFree u θ :=
  h.full_of_deg h.d6.au.symm h.d6.bu.symm h.du θ

theorem cc_full (θ : Fin G.maxDegree) : ¬ c.IsFree cc θ :=
  h.full_of_deg h.d6.acc.symm h.d6.bcc.symm h.dcc θ

theorem b_only {θ : Fin G.maxDegree} (hθ : c.IsFree b θ) : θ = β := by
  have hm := h.cm.card_missing_end (Or.inr rfl)
  rw [h.db] at hm
  have h1 : #(missing c b) = 1 := by omega
  obtain ⟨μ, hμ⟩ := card_eq_one.1 h1
  have e1 : θ ∈ missing c b := mem_missing.2 hθ
  have e2 : β ∈ missing c b := mem_missing.2 h.βb
  rw [hμ, mem_singleton] at e1 e2
  rw [e1, e2]

theorem free_a_of_inA {θ : Fin G.maxDegree} (hA : InA c a b θ) (hβ : θ ≠ β) : c.IsFree a θ :=
  hA.resolve_right fun hb => hβ (h.b_only hb)

theorem γβ : γ ≠ β := by
  rintro rfl
  exact h.d6.xy (c.col_proper h.hux h.huy)

theorem γa : c.IsFree a γ := h.free_a_of_inA h.γA h.γβ

end SKNF

end Overfull
