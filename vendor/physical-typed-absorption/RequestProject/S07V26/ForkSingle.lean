/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.DeleteLemmas

@[expose] public section

/-!
# V26 — a single physical fork and its two POSITIVE modes

For an edge `e = uv` with `u, v ∉ W`, a fork is `(u, v, w, a, b)` with `w, a, b ∈ W`, `a ≠ b`
and permitted triangles `{u,v,w}`, `{u,w,a}`, `{v,w,b}`.

* `B = {uw, vw}`, `Q = {ua, aw, wb, bv}`, `E = B ∪ Q` (`Fork.B`, `Fork.Q`, `Fork.E`).
* **basal mode** (`Fork.Valid.basal_mode`): `E` is exactly the disjoint union of `E(uwa)` and
  `E(vwb)`.
* **active mode** (`Fork.Valid.active_mode`): `B ∪ {uv} = E(uvw)` and `Q` is disjoint from it
  (free).
* the integer identity `1_Q - 1_{uv} = -1_{E(uvw)} + 1_{E(uwa)} + 1_{E(vwb)}`
  (`Fork.Valid.ind_identity`); it is a CONSEQUENCE of the two positive modes, not a signed
  cancellation of physical edges.
* `Q` (and `B`) has no edge with both ends outside `W` (`Fork.Valid.Q_meets_W`,
  `Fork.Valid.B_meets_W`).
* port replacement by EVEN link paths: `v – w – a` in `L_u`, `u – w – b` in `L_v`
  (`Fork.Valid.port_u`, `Fork.Valid.port_v`: same component and, if bipartite, same colour), and
  the new
  pair `a, b` at `w` is joined by the ODD path `a – u – v – b` in `L_w` (`Fork.Valid.port_w`: same
  component, opposite colours if bipartite).
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V25

variable {V I : Type*}

/-- a physical fork `(u, v, w, a, b)` for the root edge `uv` -/
structure Fork (V : Type*) where
  u : V
  v : V
  w : V
  a : V
  b : V

namespace Fork

variable (f : Fork V)

/-- the root edge `uv` -/
def root : Sym2 V := s(f.u, f.v)

/-- basal half `B = {uw, vw}` -/
def B : Finset (Sym2 V) := {s(f.u, f.w), s(f.v, f.w)}

/-- free half `Q = {ua, aw, wb, bv}` -/
def Q : Finset (Sym2 V) := {s(f.u, f.a), s(f.a, f.w), s(f.w, f.b), s(f.b, f.v)}

/-- all fork edges `E = B ∪ Q` -/
def E : Finset (Sym2 V) := f.B ∪ f.Q

/-- active triangle `{u, v, w}` -/
def T0 : Finset V := {f.u, f.v, f.w}
/-- basal triangle `{u, w, a}` -/
def T1 : Finset V := {f.u, f.w, f.a}
/-- basal triangle `{v, w, b}` -/
def T2 : Finset V := {f.v, f.w, f.b}

/-- validity of a fork over the core `W` -/
def Valid [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (W : Finset V) :
    Prop :=
  f.u ∉ W ∧ f.v ∉ W ∧ f.w ∈ W ∧ f.a ∈ W ∧ f.b ∈ W ∧ f.a ≠ f.b ∧
    IsAllowed G lab F f.T0 ∧ IsAllowed G lab F f.T1 ∧ IsAllowed G lab F f.T2

end Fork

variable [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

/-- the five vertices of a valid fork are pairwise distinct -/
lemma Fork.Valid.distinct {f : Fork V} (hf : f.Valid G lab F W) :
    f.u ≠ f.v ∧ f.u ≠ f.w ∧ f.u ≠ f.a ∧ f.u ≠ f.b ∧ f.v ≠ f.w ∧ f.v ≠ f.a ∧ f.v ≠ f.b ∧
      f.w ≠ f.a ∧ f.w ≠ f.b ∧ f.a ≠ f.b := by
  obtain ⟨hu, hv, hw, ha, hb, hab, h0, h1, h2⟩ := hf
  obtain ⟨huv, huw, hvw⟩ := distinct_of_card_three h0.1
  obtain ⟨-, hua, hwa⟩ := distinct_of_card_three h1.1
  obtain ⟨-, hvb, hwb⟩ := distinct_of_card_three h2.1
  refine ⟨huv, huw, hua, ?_, hvw, ?_, hvb, hwa, hwb, hab⟩
  · rintro h; exact hu (h ▸ hb)
  · rintro h; exact hv (h ▸ ha)

/-! ### Explicit edge sets -/

lemma Fork.Valid.triEdges_T0 {f : Fork V} (hf : f.Valid G lab F W) :
    triEdges f.T0 = {s(f.u, f.v), s(f.u, f.w), s(f.v, f.w)} := by
  obtain ⟨huv, huw, -, -, hvw, -⟩ := hf.distinct
  rw [Fork.T0, triEdges_triple huv huw hvw]; rfl

lemma Fork.Valid.triEdges_T1 {f : Fork V} (hf : f.Valid G lab F W) :
    triEdges f.T1 = {s(f.u, f.w), s(f.u, f.a), s(f.w, f.a)} := by
  obtain ⟨-, huw, hua, -, -, -, -, hwa, -⟩ := hf.distinct
  rw [Fork.T1, triEdges_triple huw hua hwa]; rfl

lemma Fork.Valid.triEdges_T2 {f : Fork V} (hf : f.Valid G lab F W) :
    triEdges f.T2 = {s(f.v, f.w), s(f.v, f.b), s(f.w, f.b)} := by
  obtain ⟨-, -, -, -, hvw, -, hvb, -, hwb, -⟩ := hf.distinct
  rw [Fork.T2, triEdges_triple hvw hvb hwb]; rfl

omit [Fintype V] in
/-- membership in the fork edge set -/
lemma Fork.mem_E {f : Fork V} {e : Sym2 V} :
    e ∈ f.E ↔ e = s(f.u, f.w) ∨ e = s(f.v, f.w) ∨ e = s(f.u, f.a) ∨ e = s(f.a, f.w) ∨
      e = s(f.w, f.b) ∨ e = s(f.b, f.v) := by
  simp only [Fork.E, Fork.B, Fork.Q, mem_union, mem_insert, mem_singleton]
  tauto

/-! ### The two positive modes -/

/-- **basal mode**: `E(uwa)` and `E(vwb)` are disjoint and their union is exactly `E = B ∪ Q`;
hence `{T1, T2}` is a permitted decomposition of the whole fork. -/
theorem Fork.Valid.basal_mode {f : Fork V} (hf : f.Valid G lab F W) :
    Disjoint (triEdges f.T1) (triEdges f.T2) ∧ triEdges f.T1 ∪ triEdges f.T2 = f.E ∧
      IsDecomposition G lab F f.E {f.T1, f.T2} := by
  obtain ⟨huv, huw, hua, hub, hvw, hva, hvb, hwa, hwb, hab⟩ := hf.distinct
  have hdisj : Disjoint (triEdges f.T1) (triEdges f.T2) := by
    rw [hf.triEdges_T1, hf.triEdges_T2, Finset.disjoint_left]
    intro e he he'
    simp only [mem_insert, mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h <;>
      simp only [Sym2.eq_iff] at h <;> tauto
  have hunion : triEdges f.T1 ∪ triEdges f.T2 = f.E := by
    rw [hf.triEdges_T1, hf.triEdges_T2]
    ext e
    rw [Fork.mem_E]
    simp only [mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ((h | h | h) | (h | h | h)) <;> subst h <;> simp [Sym2.eq_swap]
    · rintro (h | h | h | h | h | h) <;> subst h <;> simp [Sym2.eq_swap]
  refine ⟨hdisj, hunion, ?_, ?_, ?_⟩
  · intro T hT
    simp only [mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hf.2.2.2.2.2.2.2.1
    · exact hf.2.2.2.2.2.2.2.2
  · intro T hT T' hT' hne
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hT hT'
    rcases hT with rfl | rfl <;> rcases hT' with rfl | rfl
    · exact absurd rfl hne
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hne
  · rw [biUnion_insert, singleton_biUnion]; exact hunion

/-- **active mode**: `E(uvw) = B ∪ {uv}`; the root is not a fork edge and `B`, `Q` are
disjoint, so `Q` is left FREE; `{T0}` decomposes `B ∪ {uv}`. -/
theorem Fork.Valid.active_mode {f : Fork V} (hf : f.Valid G lab F W) :
    triEdges f.T0 = insert f.root f.B ∧ f.root ∉ f.E ∧ Disjoint f.B f.Q ∧
      IsDecomposition G lab F (insert f.root f.B) {f.T0} := by
  obtain ⟨huv, huw, hua, hub, hvw, hva, hvb, hwa, hwb, hab⟩ := hf.distinct
  have h0 : triEdges f.T0 = insert f.root f.B := by
    rw [hf.triEdges_T0]; rfl
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fork.mem_E]; simp only [Fork.root, Sym2.eq_iff]; tauto
  · rw [Fork.B, Fork.Q, Finset.disjoint_left]
    intro e he he'
    simp only [mem_insert, mem_singleton] at he he'
    rcases he with rfl | rfl <;> rcases he' with h | h | h | h <;>
      simp only [Sym2.eq_iff] at h <;> tauto
  · intro T hT; rw [mem_singleton] at hT; subst hT; exact hf.2.2.2.2.2.2.1
  · intro T hT T' hT' hne
    simp only [coe_singleton, Set.mem_singleton_iff] at hT hT'
    exact absurd (hT.trans hT'.symm) hne
  · rw [singleton_biUnion, h0]

/-- **integer identity** `1_Q - 1_{uv} = -1_{E(uvw)} + 1_{E(uwa)} + 1_{E(vwb)}`, derived from the
two positive modes (both are honest disjoint unions of physical edge sets). -/
theorem Fork.Valid.ind_identity {f : Fork V} (hf : f.Valid G lab F W) :
    ind f.Q - ind {f.root} =
      -ind (triEdges f.T0) + ind (triEdges f.T1) + ind (triEdges f.T2) := by
  obtain ⟨hdisj, hunion, -⟩ := hf.basal_mode
  obtain ⟨h0, hroot, hBQ, -⟩ := hf.active_mode
  have hrB : f.root ∉ f.B := fun h => hroot (mem_union_left _ h)
  have e1 : ind (triEdges f.T1) + ind (triEdges f.T2) = ind f.B + ind f.Q := by
    rw [← ind_union_of_disjoint hdisj, hunion, Fork.E, ind_union_of_disjoint hBQ]
  have e0 : ind (triEdges f.T0) = ind {f.root} + ind f.B := by
    rw [h0, ← ind_union_of_disjoint (disjoint_singleton_left.2 hrB)]; rfl
  rw [add_assoc, e1, e0]; abel

/-! ### Interfaces -/

/-- `Q` has no edge with both ends outside `W` -/
theorem Fork.Valid.Q_meets_W {f : Fork V} (hf : f.Valid G lab F W) :
    ∀ e ∈ f.Q, ∃ x ∈ e, x ∈ W := by
  obtain ⟨-, -, hw, ha, hb, -⟩ := hf
  intro e he
  simp only [Fork.Q, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨f.a, by simp, ha⟩
  · exact ⟨f.a, by simp, ha⟩
  · exact ⟨f.w, by simp, hw⟩
  · exact ⟨f.b, by simp, hb⟩

/-- `B` has no edge with both ends outside `W` -/
theorem Fork.Valid.B_meets_W {f : Fork V} (hf : f.Valid G lab F W) :
    ∀ e ∈ f.B, ∃ x ∈ e, x ∈ W := by
  obtain ⟨-, -, hw, -⟩ := hf
  intro e he
  simp only [Fork.B, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl <;> exact ⟨f.w, by simp, hw⟩

/-! ### Link adjacencies and port replacement -/

/-- the seven link adjacencies of a valid fork -/
theorem Fork.Valid.link_adjs {f : Fork V} (hf : f.Valid G lab F W) :
    (link G lab F f.u).Adj f.v f.w ∧ (link G lab F f.u).Adj f.w f.a ∧
    (link G lab F f.v).Adj f.u f.w ∧ (link G lab F f.v).Adj f.w f.b ∧
    (link G lab F f.w).Adj f.a f.u ∧ (link G lab F f.w).Adj f.u f.v ∧
    (link G lab F f.w).Adj f.v f.b := by
  obtain ⟨huv, huw, hua, hub, hvw, hva, hvb, hwa, hwb, hab⟩ := hf.distinct
  have h0 : IsAllowed G lab F {f.u, f.v, f.w} := hf.2.2.2.2.2.2.1
  have h1 : IsAllowed G lab F {f.u, f.w, f.a} := hf.2.2.2.2.2.2.2.1
  have h2 : IsAllowed G lab F {f.v, f.w, f.b} := hf.2.2.2.2.2.2.2.2
  refine ⟨⟨hvw, h0⟩, ⟨hwa, h1⟩, ⟨huw, ?_⟩, ⟨hwb, h2⟩, ⟨hua.symm, ?_⟩,
    ⟨huv, ?_⟩, ⟨hvb, ?_⟩⟩
  · rw [Finset.insert_comm]; exact h0
  · have : ({f.w, f.a, f.u} : Finset V) = {f.u, f.w, f.a} := by ext; simp; tauto
    rw [this]; exact h1
  · have : ({f.w, f.u, f.v} : Finset V) = {f.u, f.v, f.w} := by ext; simp; tauto
    rw [this]; exact h0
  · rw [Finset.insert_comm]; exact h2

/-- two-step (even) port replacement in a link: same component and, if bipartite, same colour -/
lemma port_even {x y m z : V} (h1 : (link G lab F x).Adj y m) (h2 : (link G lab F x).Adj m z) :
    comp G lab F x z = comp G lab F x y ∧
      (IsBip G lab F (x, comp G lab F x y) → colG G lab F x z = colG G lab F x y) := by
  have hm : m ∈ comp G lab F x y := mem_comp_iff.2 h1.reachable
  have hz : z ∈ comp G lab F x y := mem_comp_iff.2 (h1.reachable.trans h2.reachable)
  have hy : y ∈ comp G lab F x y := mem_comp_iff.2 (SimpleGraph.Reachable.refl _)
  refine ⟨comp_eq_of_mem hz, fun hb => ?_⟩
  have c1 := colG_proper hb hy hm h1
  have c2 := colG_proper hb hm hz h2
  revert c1 c2
  cases colG G lab F x y <;> cases colG G lab F x m <;> cases colG G lab F x z <;> simp

/-- **port replacement at `u`**: in `L_u`, port `v` is replaced by `a` along the even path
`v – w – a` -/
theorem Fork.Valid.port_u {f : Fork V} (hf : f.Valid G lab F W) :
    comp G lab F f.u f.a = comp G lab F f.u f.v ∧
      (IsBip G lab F (f.u, comp G lab F f.u f.v) →
        colG G lab F f.u f.a = colG G lab F f.u f.v) :=
  port_even hf.link_adjs.1 hf.link_adjs.2.1

/-- **port replacement at `v`**: in `L_v`, port `u` is replaced by `b` along `u – w – b` -/
theorem Fork.Valid.port_v {f : Fork V} (hf : f.Valid G lab F W) :
    comp G lab F f.v f.b = comp G lab F f.v f.u ∧
      (IsBip G lab F (f.v, comp G lab F f.v f.u) →
        colG G lab F f.v f.b = colG G lab F f.v f.u) :=
  port_even hf.link_adjs.2.2.1 hf.link_adjs.2.2.2.1

/-- **the new pair at `w`**: in `L_w`, `a` and `b` are joined by the odd path `a – u – v – b`:
same component, opposite colours if bipartite (a balanced pair of ports). -/
theorem Fork.Valid.port_w {f : Fork V} (hf : f.Valid G lab F W) :
    comp G lab F f.w f.b = comp G lab F f.w f.a ∧
      (IsBip G lab F (f.w, comp G lab F f.w f.a) →
        colG G lab F f.w f.b ≠ colG G lab F f.w f.a) := by
  obtain ⟨-, -, -, -, h1, h2, h3⟩ := hf.link_adjs
  have hb := port_even h1 h2
  have hb' : f.b ∈ comp G lab F f.w f.a :=
    mem_comp_iff.2 ((h1.reachable.trans h2.reachable).trans h3.reachable)
  have hv : f.v ∈ comp G lab F f.w f.a := mem_comp_iff.2 (h1.reachable.trans h2.reachable)
  refine ⟨comp_eq_of_mem hb', fun hbip => ?_⟩
  have c := colG_proper hbip hv hb' h3
  rw [← hb.2 hbip]; exact c.symm

end S07V26

end
