/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ComponentCount
public import RequestProject.S07V25.LinkRobust
public import RequestProject.S07V35.Discharge
@[expose] public section

/-!
# V36 — the native row matrix of an original host (definitions, shape, triangle balance)

Host `(G, lab, F)` exactly as in the original contract (`SparseEdgeDefs`); link, components,
activity and bipartiteness are the existing `ComponentRows.link`, `ComponentRows.comp`,
`ActiveCover.IsActiveRow`, `ComponentRows.IsBip`, and the chosen proper colouring is the
existing `ComponentRows.col`.

* `NRow` — rows: the pairs `(v, K)` with `K` an ACTIVE component of the link `L_v` that is
  BIPARTITE (finite subtype; no inactive or non-bipartite rows).
* `NCol` — columns: the host edges `e` lying in some allowed triangle (finite subtype).
* `entry (v, K) e` — zero unless `v ∈ e` and the other endpoint `u` of `e` lies in `K`; then
  `+1` / `-1` according to the chosen colour of `u`.
* `natB` — the native matrix `NRow → NCol → ℤ`.

Proved here:
* `natB_linkMatrix` — entries in `{-1,0,1}`, at most two nonzero rows per column (V35 shape);
* `eq_of_natB_root` — at a fixed endpoint at most one row is nonzero (one per endpoint);
* `natB_simpleCols` — no two distinct two-entry columns have the same support;
* `active_comp_disjoint` — distinct active components at a root are disjoint;
* `entry_triangle_sum` — every allowed triangle has zero row balance in every native row;
* `natB_lattice_kernel` — every vector of the physical lattice `SparseEdge.lattice G lab F`
  (integer combination of allowed triangles) is in the integer kernel of `natB`
  (forward implication only; no saturation claim).
-/

open Finset Classical

noncomputable section

namespace S07V36

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
  TypedTriangle.ComponentCount

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- Native rows: active bipartite components of links. -/
def IsNRow (j : Row V) : Prop := IsActiveRow G lab F j ∧ IsBip G lab F j

/-- The finite set of native rows. -/
abbrev NRow := {j : Row V // IsNRow G lab F j}

/-- Native columns: host edges contained in some allowed triangle. -/
def IsNCol (e : Sym2 V) : Prop := ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T

/-- The finite set of native columns. -/
abbrev NCol := {e : Sym2 V // IsNCol G lab F e}

/-- Native entry of row `j = (v, K)` on an unordered pair `e`: zero unless `v ∈ e` and the
other endpoint lies in `K`, then `±1` by the chosen colour of the other endpoint. -/
def entry (j : Row V) (e : Sym2 V) : ℤ :=
  if h : j.1 ∈ e then
    (if Sym2.Mem.other h ∈ j.2 then
      TypedTriangle.SignedCover.sgn (TypedTriangle.ComponentRows.col G lab F j (Sym2.Mem.other h)) else 0)
  else 0

/-- **The native matrix.** -/
def natB (j : NRow G lab F) (e : NCol G lab F) : ℤ := entry G lab F j.1 e.1

variable {G lab F}

/-! ### Elementary facts on links and components -/

omit [Fintype V] in
/-- Link adjacency at `v` only involves vertices different from `v`. -/
lemma link_adj_ne {v u w : V} (h : (link G lab F v).Adj u w) : v ≠ u ∧ v ≠ w ∧ u ≠ w :=
  distinct_of_card_three h.2.1

omit [Fintype V] in
lemma walk_ne_adj {v : V} : ∀ {x y : V}, (link G lab F v).Walk x y → x ≠ y →
    ∃ z, (link G lab F v).Adj x z := by
  intro x y q hxy
  cases q with
  | nil => exact absurd rfl hxy
  | cons h _ => exact ⟨_, h⟩

/-- An active row is the component of each of its members. -/
lemma active_eq_comp {j : Row V} (hj : IsActiveRow G lab F j) {u : V} (hu : u ∈ j.2) :
    j.2 = comp G lab F j.1 u := by
  obtain ⟨a, -, ha⟩ := hj
  rw [← ha] at hu ⊢
  rcases comp_eq_or_disjoint G lab F j.1 a u with h | h
  · exact h
  · exact absurd (mem_comp_self G lab F j.1 u) (Finset.disjoint_left.1 h hu)

/-- **Distinct active components at a root are disjoint.** -/
theorem active_comp_disjoint {j k : Row V} (hj : IsActiveRow G lab F j)
    (hk : IsActiveRow G lab F k) (hroot : j.1 = k.1) (hne : j ≠ k) : Disjoint j.2 k.2 := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  apply hne
  refine Prod.ext hroot ?_
  rw [active_eq_comp hj hu, active_eq_comp hk hu', hroot]

/-- Every member of an active component is non-isolated in the link. -/
lemma linkActive_of_mem {j : Row V} (hj : IsActiveRow G lab F j) {u : V} (hu : u ∈ j.2) :
    LinkActive G lab F j.1 u := by
  obtain ⟨a, ha, hK⟩ := hj
  rw [← hK, mem_comp_iff] at hu
  by_cases hau : u = a
  · exact hau ▸ ha
  · obtain ⟨p⟩ := hu
    exact walk_ne_adj p.reverse hau

/-- The root does not belong to its active components. -/
lemma root_not_mem {j : Row V} (hj : IsActiveRow G lab F j) : j.1 ∉ j.2 := by
  intro h
  obtain ⟨w, hw⟩ := linkActive_of_mem hj h
  exact (link_adj_ne hw).1 rfl

/-- Members of an active component are distinct from the root. -/
lemma root_ne_of_mem {j : Row V} (hj : IsActiveRow G lab F j) {u : V} (hu : u ∈ j.2) :
    j.1 ≠ u := fun h => root_not_mem hj (h ▸ hu)

omit [Fintype V] in
/-- Specification of the chosen colouring of a bipartite row. -/
lemma col_proper {j : Row V} (hb : IsBip G lab F j) {u w : V} (hu : u ∈ j.2) (hw : w ∈ j.2)
    (h : (link G lab F j.1).Adj u w) :
    TypedTriangle.ComponentRows.col G lab F j u ≠ TypedTriangle.ComponentRows.col G lab F j w := by
  unfold TypedTriangle.ComponentRows.col
  rw [dif_pos hb]
  exact Classical.choose_spec hb u hu w hw h

/-! ### The entries -/

omit [Fintype V] in
lemma other_eq {v u : V} (h : v ∈ s(v, u)) : Sym2.Mem.other h = u :=
  Sym2.congr_right.1 (Sym2.other_spec h)

omit [Fintype V] in
/-- Entry on the edge `vu` at a row rooted at `v`. -/
lemma entry_root (v : V) (K : Finset V) (u : V) :
    entry G lab F (v, K) s(v, u) =
      if u ∈ K then TypedTriangle.SignedCover.sgn (TypedTriangle.ComponentRows.col G lab F (v, K) u)
      else 0 := by
  have h : (v, K).1 ∈ s(v, u) := Sym2.mem_mk_left v u
  unfold entry
  rw [dif_pos h, other_eq h]

omit [Fintype V] in
/-- Entry on a pair not containing the root. -/
lemma entry_of_not_mem {j : Row V} {e : Sym2 V} (h : j.1 ∉ e) : entry G lab F j e = 0 := by
  unfold entry
  rw [dif_neg h]

omit [Fintype V] in
lemma sgn_cases (b : Bool) :
    TypedTriangle.SignedCover.sgn b = -1 ∨ TypedTriangle.SignedCover.sgn b = 0 ∨
      TypedTriangle.SignedCover.sgn b = 1 := by
  cases b <;> simp [TypedTriangle.SignedCover.sgn]

omit [Fintype V] in
lemma sgn_add_of_ne {a b : Bool} (h : a ≠ b) :
    TypedTriangle.SignedCover.sgn a + TypedTriangle.SignedCover.sgn b = 0 := by
  cases a <;> cases b <;> simp_all [TypedTriangle.SignedCover.sgn]

omit [Fintype V] in
lemma entry_cases (j : Row V) (e : Sym2 V) :
    entry G lab F j e = -1 ∨ entry G lab F j e = 0 ∨ entry G lab F j e = 1 := by
  unfold entry
  split_ifs
  · exact sgn_cases _
  · simp
  · simp

omit [Fintype V] in
/-- A nonzero entry sits on an edge `s(v, u)` with `u ∈ K`. -/
lemma entry_ne_zero {j : Row V} {e : Sym2 V} (h : entry G lab F j e ≠ 0) :
    ∃ u ∈ j.2, e = s(j.1, u) := by
  unfold entry at h
  split_ifs at h with h1 h2
  · exact ⟨_, h2, (Sym2.other_spec h1).symm⟩
  · exact absurd rfl h
  · exact absurd rfl h

/-- At a fixed endpoint at most one native row is nonzero on a column. -/
theorem eq_of_natB_root {j k : NRow G lab F} {e : NCol G lab F} (hj : natB G lab F j e ≠ 0)
    (hk : natB G lab F k e ≠ 0) (hroot : j.1.1 = k.1.1) : j = k := by
  obtain ⟨u, hu, he⟩ := entry_ne_zero hj
  obtain ⟨u', hu', he'⟩ := entry_ne_zero hk
  rw [he, hroot] at he'
  have huu : u = u' := Sym2.congr_right.1 he'
  subst huu
  apply Subtype.ext
  refine Prod.ext hroot ?_
  rw [active_eq_comp j.2.1 hu, active_eq_comp k.2.1 hu', hroot]

lemma root_mem_of_natB {j : NRow G lab F} {e : NCol G lab F} (h : natB G lab F j e ≠ 0) :
    j.1.1 ∈ e.1 := by
  obtain ⟨u, -, he⟩ := entry_ne_zero h
  rw [he]; exact Sym2.mem_mk_left _ _

/-- **Shape of the native matrix (V35 `LinkMatrix`).** -/
theorem natB_linkMatrix : S07V35.LinkMatrix (natB G lab F) where
  entries i e := entry_cases i.1 e.1
  two e := by
    obtain ⟨a, b, hab⟩ : ∃ a b, e.1 = s(a, b) := e.1.ind (fun a b => ⟨a, b, rfl⟩)
    have hinj : Set.InjOn (fun j : NRow G lab F => j.1.1)
        (S07V35.supp (natB G lab F) e : Set (NRow G lab F)) := by
      intro j hj k hk h
      simp only [S07V35.supp, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hj hk
      exact eq_of_natB_root hj hk h
    refine (Finset.card_le_card_of_injOn (fun j : NRow G lab F => j.1.1) (t := {a, b})
      ?_ hinj).trans Finset.card_le_two
    intro j hj
    simp only [S07V35.supp, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hj
    have := root_mem_of_natB hj
    rw [hab, Sym2.mem_iff] at this
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact this

/-- **No parallel two-entry columns (V35 `SimpleCols`).** -/
theorem natB_simpleCols : S07V35.SimpleCols (natB G lab F) := by
  intro e e' h2 hsame
  obtain ⟨j, k, hjk, hs⟩ := Finset.card_eq_two.1 h2
  have hj : j ∈ S07V35.supp (natB G lab F) e := by rw [hs]; simp
  have hk : k ∈ S07V35.supp (natB G lab F) e := by rw [hs]; simp
  have hj' : j ∈ S07V35.supp (natB G lab F) e' := by rw [hsame]; exact hj
  have hk' : k ∈ S07V35.supp (natB G lab F) e' := by rw [hsame]; exact hk
  simp only [S07V35.supp, mem_filter, mem_univ, true_and] at hj hk hj' hk'
  have hroot : j.1.1 ≠ k.1.1 := fun h => hjk (eq_of_natB_root hj hk h)
  apply Subtype.ext
  have h1 := (Sym2.mem_and_mem_iff hroot).1 ⟨root_mem_of_natB hj, root_mem_of_natB hk⟩
  have h2 := (Sym2.mem_and_mem_iff hroot).1 ⟨root_mem_of_natB hj', root_mem_of_natB hk'⟩
  rw [h1, h2]

/-! ### Triangle balance -/

/-- **Zero row balance of an allowed triangle**, for every active bipartite row. -/
theorem entry_triangle_sum {j : Row V} (hj : IsNRow G lab F j) {T : Finset V}
    (hT : IsAllowed G lab F T) : ∑ e ∈ triEdges T, entry G lab F j e = 0 := by
  obtain ⟨v, K⟩ := j
  by_cases hv : v ∈ T
  · obtain ⟨u, huT, huv, -⟩ := exists_third hT.1 v v
    obtain ⟨w, hwv, hwu, rfl⟩ := allowed_eq_triple hT.1 hv huT (Ne.symm huv)
    have hvu : v ≠ u := Ne.symm huv
    have hvw : v ≠ w := Ne.symm hwv
    have huw : u ≠ w := Ne.symm hwu
    rw [triEdges_triple hvu hvw huw, Finset.sum_insert (not_mem_wedge_uv hvu hvw huw), wedge,
      Finset.sum_pair (by
        rw [Ne, Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hvu h
        · exact hvw h)]
    have h3 : entry G lab F (v, K) s(u, w) = 0 :=
      entry_of_not_mem (by
        show v ∉ s(u, w)
        rw [Sym2.mem_iff]; rintro (h | h)
        · exact hvu h
        · exact hvw h)
    rw [h3, entry_root, entry_root, add_zero]
    have hadj : (link G lab F v).Adj u w := ⟨huw, hT⟩
    have hiff : u ∈ K ↔ w ∈ K := by
      obtain ⟨a, -, ha⟩ := hj.1
      change comp G lab F v a = K at ha
      rw [← ha, mem_comp_iff, mem_comp_iff]
      exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩
    by_cases hu : u ∈ K
    · have hw := hiff.1 hu
      rw [if_pos hu, if_pos hw]
      exact sgn_add_of_ne (col_proper hj.2 hu hw hadj)
    · have hw : w ∉ K := fun h => hu (hiff.2 h)
      rw [if_neg hu, if_neg hw, add_zero]
  · refine Finset.sum_eq_zero fun e he => entry_of_not_mem fun hve => hv ?_
    exact mem_of_mem_triEdges he hve

/-- Row functional of the native matrix on edge vectors. -/
def rowFun (j : NRow G lab F) : (Sym2 V → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ e : NCol G lab F, natB G lab F j e * x e.1
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

lemma rowFun_ind (j : NRow G lab F) {T : Finset V} (hT : IsAllowed G lab F T) :
    rowFun j (ind (triEdges T)) = 0 := by
  change ∑ e : NCol G lab F, entry G lab F j.1 e.1 * ind (triEdges T) e.1 = 0
  rw [← Finset.sum_subtype (univ.filter (IsNCol G lab F)) (by simp)
    (fun e => entry G lab F j.1 e * ind (triEdges T) e)]
  rw [← Finset.sum_subset (s₁ := triEdges T)]
  · rw [← entry_triangle_sum j.2 hT]
    refine Finset.sum_congr rfl fun e he => ?_
    simp [ind, he]
  · intro e he
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨T, hT, he⟩
  · intro e _ he
    simp [ind, he]

/-- **Physical triangle certificates are in the integer kernel of the native matrix.**
Every vector of the physical lattice (integer combinations of allowed triangles) has zero
native row balance. Forward implication only. -/
theorem natB_lattice_kernel {x : Sym2 V → ℤ} (hx : x ∈ lattice G lab F) (j : NRow G lab F) :
    ∑ e : NCol G lab F, natB G lab F j e * x e.1 = 0 := by
  have hle : lattice G lab F ≤ LinearMap.ker (rowFun j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T, hT, rfl⟩
    exact rowFun_ind j hT
  exact hle hx

end S07V36
