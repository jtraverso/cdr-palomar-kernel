/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.Bernoulli
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace S07V24

/-- Ignoring the coordinates outside a fixed set gives exactly the same
Bernoulli process as sampling on that set in the first place. -/
theorem bexp_inter {V : Type*} [DecidableEq V] (q : ℝ) (U S : Finset V)
    (f : Finset V → ℝ) :
    bexp q U (fun W => f (W ∩ S)) = bexp q (U ∩ S) f := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [empty_inter,bexp_empty]
  | @insert a U ha ih =>
    by_cases hS : a ∈ S
    · have hSet : insert a U ∩ S = insert a (U ∩ S) := by ext x; simp [hS]
      have ha' : a ∉ U ∩ S := fun h => ha (mem_inter.mp h).1
      have hFunction : (fun W => f (insert a W ∩ S)) =
          (fun W => f (insert a (W ∩ S))) := by
        funext W
        congr 1
        ext x
        simp [hS]
      rw [bexp_insert ha,hSet,bexp_insert ha',hFunction,ih f,
        ih (fun W => f (insert a W))]
    · have hSet : insert a U ∩ S = U ∩ S := by ext x; simp [hS]
      have hFunction : (fun W => f (insert a W ∩ S)) =
          (fun W => f (W ∩ S)) := by
        funext W
        congr 1
        ext x
        simp [hS]
      rw [bexp_insert ha,hSet,hFunction,ih f]
      ring

theorem bprob_inter {V : Type*} [DecidableEq V] (q : ℝ) (U S : Finset V)
    (E : Finset V → Prop) [DecidablePred E] :
    bprob q U (fun W => E (W ∩ S)) = bprob q (U ∩ S) E :=
  bexp_inter q U S (fun W => if E W then 1 else 0)

/-- Bernoulli sampling commutes with an injective relabelling, including
the actual inclusion of a surviving vertex subtype into its ambient host. -/
theorem bexp_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (q : ℝ) (U : Finset V) (e : V ↪ W) (f : Finset W → ℝ) :
    bexp q (U.map e) f = bexp q U (fun T => f (T.map e)) := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [map_empty,bexp_empty]
  | @insert a U ha ih =>
    have ha' : e a ∉ U.map e := by
      intro he
      obtain ⟨v,hv,heq⟩ := mem_map.mp he
      have hEq : v = a := e.injective heq
      exact ha (hEq ▸ hv)
    have hFunction : (fun T : Finset V => f (insert (e a) (T.map e))) =
        (fun T : Finset V => f ((insert a T).map e)) := by
      funext T
      rw [map_insert]
    rw [map_insert,bexp_insert ha',bexp_insert ha,ih f,
      ih (fun T => f (insert (e a) T)),hFunction]

theorem bprob_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (q : ℝ) (U : Finset V) (e : V ↪ W) (E : Finset W → Prop) [DecidablePred E] :
    bprob q (U.map e) E = bprob q U (fun T => E (T.map e)) :=
  bexp_map q U e (fun T => if E T then 1 else 0)

#print axioms bexp_inter
#print axioms bprob_inter
#print axioms bexp_map
#print axioms bprob_map
end S07V24
