/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.SimulCounters
public import RequestProject.Selectors.TypedLink

@[expose] public section

/-!
# The local single-root selector contract (S07 §5) — V21

`LocalSel V` is the data of one physical selector at a root `v`: its non-port vertices `W`
(abstract auxiliaries AND route internals), its base edges `P`, and a mode `mode S ⊆ P` for
each demand `S`.

`LocalSel.Valid G lab F v U Adm Z0 Bf A σ` is the single-root contract, with exact windows:
* every base edge `xy ∈ P` is an edge of the TYPED link `L_v` (so `{v,x,y}` is permitted),
  and avoids the forbidden edge set `Bf`;
* every vertex of a base edge is a port (`U`) or a non-port vertex (`W`);
* every `w ∈ W` is adjacent to `v` in `G` (radial wings exist), `W` avoids the deleted vertex
  window `Z0` and the ports `U`; `|W| ≤ A·|U|`;
* the base edges have maximum degree `≤ 60`;
* every admissible demand `S ⊆ U` has a mode: a matching `mode S ⊆ P` covering exactly
  `W ∪ S` (`SelBridge.IsMode`).

`LocalAvail ... ζw ρw` is the AVAILABILITY premise of one root: for every deleted vertex
window `Z0` with `|Z0| ≤ ζw` and every forbidden edge set `Bf` of maximum degree `≤ ρw`, a
valid local selector exists.  This is a statement about ONE root; it is supplied by the V20
typed PAR/BAL selectors in `SimulTypedInstance.lean` (from the robustness obligations,
whose derivation from H3/H4 is pending).
-/

namespace SelSimul

open Finset SelBridge SelTyped

/-- Data of a single-root physical selector. -/
structure LocalSel (V : Type*) where
  /-- non-port vertices (abstract auxiliaries and route internals) -/
  W : Finset V
  /-- base edges (bases of the mode triangles and residual tokens) -/
  P : Finset (Sym2 V)
  /-- the mode chosen for each demand -/
  mode : Finset V → Finset (Sym2 V)

variable {V I : Type*} [DecidableEq V]

/-- **The local single-root contract** with deleted vertex window `Z0` and forbidden edge
window `Bf`. -/
structure LocalSel.Valid (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U : Finset V) (Adm : Finset V → Prop) (Z0 : Finset V) (Bf : Finset (Sym2 V)) (A : ℕ)
    (σ : LocalSel V) : Prop where
  typed : ∀ f ∈ σ.P, ∃ x y, f = s(x, y) ∧ (typedLink G lab F v).Adj x y
  avoidB : Disjoint σ.P Bf
  supp : ∀ f ∈ σ.P, ∀ y ∈ f, y ∈ U ∨ y ∈ σ.W
  wing : ∀ w ∈ σ.W, G.Adj v w
  avoidZ : Disjoint σ.W Z0
  portFree : Disjoint σ.W U
  card_le : σ.W.card ≤ A * U.card
  deg_le : ∀ y, edeg σ.P y ≤ 60
  modes : ∀ S ⊆ U, Adm S → IsMode σ.P σ.W S (σ.mode S)

/-- **Availability premise of ONE root**, with exact windows. -/
def LocalAvail (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U : Finset V) (Adm : Finset V → Prop) (A ζw ρw : ℕ) : Prop :=
  ∀ (Z0 : Finset V) (Bf : Finset (Sym2 V)), Z0.card ≤ ζw → (∀ y, edeg Bf y ≤ ρw) →
    ∃ σ : LocalSel V, σ.Valid G lab F v U Adm Z0 Bf A

namespace LocalSel.Valid

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V} {U : Finset V}
  {Adm : Finset V → Prop} {Z0 Z0' : Finset V} {Bf Bf' : Finset (Sym2 V)} {A : ℕ}
  {σ : LocalSel V}

/-- Shrinking the windows preserves validity. -/
theorem mono (h : σ.Valid G lab F v U Adm Z0 Bf A) (hZ : Z0' ⊆ Z0) (hB : Bf' ⊆ Bf) :
    σ.Valid G lab F v U Adm Z0' Bf' A where
  typed := h.typed
  avoidB := h.avoidB.mono_right hB
  supp := h.supp
  wing := h.wing
  avoidZ := h.avoidZ.mono_right hZ
  portFree := h.portFree
  card_le := h.card_le
  deg_le := h.deg_le
  modes := h.modes

/-- Base edges lie in the ambient link of `v`. -/
theorem inLink (h : σ.Valid G lab F v U Adm Z0 Bf A) : InLink G v σ.P := by
  intro f hf
  obtain ⟨x, y, rfl, hxy⟩ := h.typed f hf
  have h' := typedLink_le_linkGraph G lab F v hxy
  refine ⟨h'.1, fun z hz => ?_⟩
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · exact h'.2.1
  · exact h'.2.2

/-- The root is not a vertex of any base edge. -/
theorem root_not_mem (h : σ.Valid G lab F v U Adm Z0 Bf A) {f : Sym2 V} (hf : f ∈ σ.P) :
    v ∉ f :=
  SelBridge.root_not_mem h.inLink hf

/-- Every mode base is a permitted triangle `{v, x, y}`. -/
theorem permitted (h : σ.Valid G lab F v U Adm Z0 Bf A) {f : Sym2 V} (hf : f ∈ σ.P) :
    ∃ x y, f = s(x, y) ∧ x ≠ y ∧ TypedTriangle.SparseEdge.IsAllowed G lab F {v, x, y} := by
  obtain ⟨x, y, rfl, hxy⟩ := h.typed f hf
  exact ⟨x, y, rfl, typedLink_adj_iff.mp hxy⟩

end LocalSel.Valid

/-- The empty selector is valid for an empty port set, for any admissibility predicate. -/
theorem valid_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (Adm : Finset V → Prop) (Z0 : Finset V) (Bf : Finset (Sym2 V)) (A : ℕ) :
    (⟨∅, ∅, fun _ => ∅⟩ : LocalSel V).Valid G lab F v ∅ Adm Z0 Bf A where
  typed := by simp
  avoidB := by simp
  supp := by simp
  wing := by simp
  avoidZ := by simp
  portFree := by simp
  card_le := by simp
  deg_le := by simp [edeg]
  modes := by
    intro S hS _
    rw [subset_empty] at hS
    subst hS
    refine ⟨subset_refl _, ?_, ?_⟩ <;> simp

/-- An empty port set is always available. -/
theorem localAvail_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (Adm : Finset V → Prop) (A ζw ρw : ℕ) : LocalAvail G lab F v ∅ Adm A ζw ρw :=
  fun Z0 Bf _ _ => ⟨_, valid_empty G lab F v Adm Z0 Bf A⟩

end SelSimul
