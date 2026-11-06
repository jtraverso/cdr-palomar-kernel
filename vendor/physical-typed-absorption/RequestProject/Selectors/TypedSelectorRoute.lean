/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.RobustOddRoute
public import RequestProject.Selectors.TypedLink
public import RequestProject.Selectors.SelectorEmbedding

@[expose] public section

/-!
# PAR and BAL selectors routed in the TYPED link by bounded odd paths (S07 §§2, 5) — V20

The odd subdivision is constructed by `SelEmbed.greedy_embedding` with `ℓ = 4D + 1`, BEFORE any
mode, inside a subgraph `H` of the typed link `L_v = SelTyped.typedLink G lab F v`, from the
robustness
obligations `SelRoute.RobustDiam` / `SelRoute.RobustNonBip` of an active component `K` (to be
instantiated from H3–H4).  The condition `SelEmbed.RobustOddPaths` is DERIVED
(`SelRoute.robustOddPaths_nonbip` / `_bip`), not assumed.  No common-neighbour density input is
used.

Budgets (`v(Q)` vertices, `e(Q)` edges of the abstract selector, `ℓ - 1 = 4D`):
* PAR: `v(Q) = 3r`, `e(Q) ≤ 4r`; routing budget `B = |Z0| + 3r + 4D·4r`; robustness is needed
  for deletions of size `M ≥ B + 3D + 1` (the S07 slack `3D + 4` is more than enough).
* BAL: `v(Q) ≤ 10k`, `e(Q) ≤ 200k` (`k = max l r ≥ 1`); `B = |Z0| + 10k + 4D·200k`, robust
  connectivity with diameter `D` for deletions of size `M ≥ B` (no extra slack is needed in the
  bipartite case: a shortest path between opposite sides is already odd).

Resulting bounds (exact statements below):
* PAR: base edges `≤ (4D+1)·4r`, internal vertices `≤ 4D·4r`, radial edges
  `|W'| ≤ 2r + 4D·4r`, fuel `≤ (4D+1)·4r + 2r + 4D·4r`, base-edge maximum degree `≤ 3`.
* BAL: base edges `≤ (4D+1)·200k`, internal vertices `≤ 4D·200k`, radial edges
  `|W'| ≤ 8k + 4D·200k`, fuel `≤ (4D+1)·200k + 8k + 4D·200k`, base-edge maximum degree `≤ 60`.

Certificates: every base edge is an edge of the TYPED link (so every mode triangle `v x y` is a
permitted triangle); every radial edge `v w`, `w ∈ W'`, is an edge of the ambient `G`.

The host is any `H ≤ L_v` (the robustness hypotheses are stated for `H`).  Taking
`H = L_v.deleteEdges B0` makes all base edges avoid a used-edge set `B0`
(`pathEdge_not_mem_deleted`); `H = L_v` is the plain case.
-/

namespace SelTyped

open Finset SimpleGraph SelSubdiv SelBridge SelEmbed SelRoute ParitySel SelBalanced

variable {V I : Type*} [DecidableEq V]

/-! ### Generic facts -/

/-- A typed-link edge at `x` makes `v x` an ambient edge. -/
lemma root_adj_of_typed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x y : V}
    (h : (typedLink G lab F v).Adj x y) : G.Adj v x :=
  (typedLink_le_linkGraph G lab F v h).2.1

/-- In a robust component with two distinct vertices, every vertex is a link vertex. -/
lemma root_adj_of_two {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {H : SimpleGraph V} (hH : H ≤ typedLink G lab F v)
    {K : Finset V} {M D : ℕ} (hd : RobustDiam H K M D) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : G.Adj v x := by
  obtain ⟨p, -, -⟩ := hd ∅ (by simp) x hx y hy (by simp) (by simp)
  cases p with
  | nil => exact absurd rfl hxy
  | cons h _ => exact root_adj_of_typed (hH h)

variable {α : Type*} [DecidableEq α] {Q : Finset (Sym2 α)}

omit [DecidableEq α] in
/-- Internal subdivision vertices are link vertices (radial edges exist in `G`). -/
lemma root_adj_of_internal {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    (D : OddSubdivision (typedLink G lab F v) Q) {w : V} (hw : w ∈ D.internals) : G.Adj v w := by
  obtain ⟨e, he, j, h1, h2, rfl⟩ := (OddSubdivision.mem_internals _).mp hw
  have := D.adj e he j (by omega)
  have hj : pv D.φ D.src D.tgt D.t D.int e j = D.int e j := OddSubdivision.pathV_mid e h1 h2
  rw [hj] at this
  exact root_adj_of_typed this

omit [DecidableEq α] in
/-- Base edges of a subdivision in a subgraph `H` of the typed link are `H`-edges AND typed. -/
lemma sub_pathEdge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {H : SimpleGraph V} (hH : H ≤ typedLink G lab F v) (D : OddSubdivision H Q) :
    ∀ f ∈ D.pathEdges, ∃ x y, f = s(x, y) ∧ H.Adj x y ∧ (typedLink G lab F v).Adj x y := by
  intro f hf
  obtain ⟨e, he, j, hj, rfl⟩ := (OddSubdivision.mem_pathEdges _).mp hf
  exact ⟨_, _, rfl, D.adj e he j hj, hH (D.adj e he j hj)⟩

omit [DecidableEq α] in
/-- **Used-edge avoidance**: taking `H = L_v.deleteEdges B0` (a legitimate choice of `H ≤ L_v`),
all base edges avoid the forbidden edge set `B0`. -/
lemma pathEdge_not_mem_deleted {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    (B0 : Set (Sym2 V)) (D : OddSubdivision ((typedLink G lab F v).deleteEdges B0) Q) :
    ∀ f ∈ D.pathEdges, f ∉ B0 := by
  intro f hf
  obtain ⟨e, he, j, hj, rfl⟩ := (OddSubdivision.mem_pathEdges _).mp hf
  exact (SimpleGraph.deleteEdges_adj.mp (D.adj e he j hj)).2

omit [DecidableEq α] in
/-- Base-edge degree bound from abstract degrees. -/
lemma filter_mem_card_le {β : Type*} [Fintype β] [DecidableEq β] (Γ : SimpleGraph β)
    [DecidableRel Γ.Adj] {Δ : ℕ} (hΔ : ∀ x, Γ.degree x ≤ Δ) (x : β) :
    (Γ.edgeFinset.filter (fun e => x ∈ e)).card ≤ Δ := by
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  exact hΔ x

omit [DecidableEq α] in
/-- Fuel cardinality bound. -/
lemma fuel_card_le (v : V) (E : Finset (Sym2 V)) (W : Finset V) :
    (fuel v E W).card ≤ E.card + W.card := by
  unfold fuel
  exact (card_union_le _ _).trans (by rw [radial_card])

/-! ### PAR: non-bipartite active component -/

/-- **PAR selector routed in the typed link by bounded odd paths.**  From the robustness
obligations of a non-bipartite active component `K` of `L_v`, with
`|Z0| + 3r + 4D·4r + 3D + 1 ≤ M`, an odd subdivision of the parity selector with paths of length
`≤ 4D+1` is constructed in the typed link, before any mode: prescribed ports `ψ` are fixed,
auxiliaries lie in their candidate sets `Cand x ⊆ K`, everything avoids `Z0`; explicit base,
internal, radial, fuel and degree bounds hold; every base edge is typed and every radial edge
is ambient; and every even demand `S` has a positive mode with the same fuel. -/
theorem parity_selector_typed (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (H : SimpleGraph V) (hH : H ≤ typedLink G lab F v)
    (K Z0 : Finset V) (r M D : ℕ) (hM : Z0.card + 3 * r + 4 * D * (4 * r) + 3 * D + 1 ≤ M)
    (hd : RobustDiam H K M D) (hn : RobustNonBip H K M)
    (ψ : Fin r → V) (hψ : Function.Injective ψ) (hψK : ∀ i, ψ i ∈ K) (hψZ : ∀ i, ψ i ∉ Z0)
    (Cand : PV r → Finset V) (hCK : ∀ x, Cand x ⊆ K)
    (hCand : ∀ x, Z0.card + 3 * r ≤ (Cand x).card) :
    ∃ Dt : OddSubdivision H (paritySelector r).edgeFinset,
      (∀ i, Dt.φ (pu i) = ψ i) ∧ (∀ x ∈ auxSet r, Dt.φ x ∈ Cand x) ∧
      (∀ x, Dt.φ x ∉ Z0) ∧ (∀ y ∈ Dt.internals, y ∉ Z0) ∧
      (∀ e ∈ (paritySelector r).edgeFinset, 2 * Dt.t e + 1 ≤ 4 * D + 1) ∧
      Dt.pathEdges.card ≤ (4 * D + 1) * (4 * r) ∧
      Dt.internals.card ≤ 4 * D * (4 * r) ∧
      ((auxSet r).image Dt.φ ∪ Dt.internals).card ≤ 2 * r + 4 * D * (4 * r) ∧
      (fuel v Dt.pathEdges ((auxSet r).image Dt.φ ∪ Dt.internals)).card ≤
        (4 * D + 1) * (4 * r) + (2 * r + 4 * D * (4 * r)) ∧
      (∀ y, (Dt.pathEdges.filter (fun f => y ∈ f)).card ≤ 3) ∧
      (∀ f ∈ Dt.pathEdges, ∃ x y, f = s(x, y) ∧ H.Adj x y ∧ (typedLink G lab F v).Adj x y) ∧
      (∀ w ∈ (auxSet r).image Dt.φ ∪ Dt.internals, G.Adj v w) ∧
      ∀ S : Finset (Fin r), Even S.card →
        ∃ F' : Finset (Sym2 (PV r)),
          IsMode (paritySelector r).edgeFinset (auxSet r) (portSet S) F' ∧
          IsMode Dt.pathEdges ((auxSet r).image Dt.φ ∪ Dt.internals) ((portSet S).image Dt.φ)
            (Dt.modeEdges F') ∧
          (∀ e ∈ Dt.modeEdges F', ∃ x y, e = s(x, y) ∧ x ≠ y ∧
            TypedTriangle.SparseEdge.IsAllowed G lab F {v, x, y}) ∧
          (Dt.modeEdges F' : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
          Disjoint (fuel v Dt.pathEdges ((auxSet r).image Dt.φ ∪ Dt.internals))
            (radial v ((portSet S).image Dt.φ)) ∧
          fuel v Dt.pathEdges ((auxSet r).image Dt.φ ∪ Dt.internals) ∪
              radial v ((portSet S).image Dt.φ) =
            (Dt.modeEdges F').biUnion (triE v) ∪ (Dt.pathEdges \ Dt.modeEdges F') ∧
          Disjoint ((Dt.modeEdges F').biUnion (triE v)) (Dt.pathEdges \ Dt.modeEdges F') := by
  set Q := (paritySelector r).edgeFinset
  have hQc : Q.card ≤ 4 * r := paritySelector_card_edgeFinset_le r
  let Ports : Finset (PV r) := univ.image pu
  let ψ' : PV r → V := Sum.elim ψ (fun _ => v)
  have hψ' : Set.InjOn ψ' Ports := by
    intro x hx y hy hxy
    simp only [Ports, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    simp only [ψ', Sum.elim_inl] at hxy
    rw [hψ hxy]
  have hPorts : ∀ x ∈ Ports, ∃ i, x = pu i := by
    intro x hx; obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact ⟨i, rfl⟩
  have hR : RobustOddPaths H (ParAllowed K) (4 * D + 1)
      (Z0.card + 3 * r + 4 * D * (4 * r)) := robustOddPaths_nonbip (by omega) hd hn
  obtain ⟨Dt, hP, hC, hZ, hlen, hint⟩ := greedy_embedding H (ParAllowed K)
    hR Q not_isDiag_of_mem (fun _ a => a ∈ K) (fun _ _ _ _ _ a b hab ha hb => ⟨ha, hb, hab⟩)
    Ports ψ' hψ' (fun x hx => by obtain ⟨i, rfl⟩ := hPorts x hx; exact hψK i)
    Z0 (fun x hx => by obtain ⟨i, rfl⟩ := hPorts x hx; exact hψZ i)
    Cand (fun x _ a ha => hCK x ha) (fun x _ => by rw [card_PV]; exact hCand x)
    (by
      rw [card_PV, Nat.add_sub_cancel]
      have : 4 * D * Q.card ≤ 4 * D * (4 * r) := Nat.mul_le_mul_left _ hQc
      omega)
  have hφP : ∀ i, Dt.φ (pu i) = ψ i := fun i => hP (pu i) (mem_image_of_mem _ (mem_univ i))
  have hφC : ∀ x ∈ auxSet r, Dt.φ x ∈ Cand x := by
    intro x hx
    apply hC
    intro hxP
    obtain ⟨i, rfl⟩ := hPorts x hxP
    simp [auxSet] at hx
  have hpe := OddSubdivision.pathEdges_card_le (D := Dt) hlen
  have hin := OddSubdivision.internals_card_le (D := Dt) hlen
  have hpe' : Dt.pathEdges.card ≤ (4 * D + 1) * (4 * r) :=
    hpe.trans (Nat.mul_le_mul_left _ hQc)
  have hin' : Dt.internals.card ≤ 4 * D * (4 * r) := by
    rw [Nat.add_sub_cancel] at hin; exact hin.trans (Nat.mul_le_mul_left _ hQc)
  have haux : (auxSet r).card = 2 * r := by
    have : auxSet r = univ.map ⟨(Sum.inr : Fin r ⊕ Fin r → PV r), Sum.inr_injective⟩ := by
      ext x; cases x <;> simp [auxSet]
    rw [this, card_map, card_univ, Fintype.card_sum, Fintype.card_fin]; ring
  have hW : ((auxSet r).image Dt.φ ∪ Dt.internals).card ≤ 2 * r + 4 * D * (4 * r) := by
    have := card_union_le ((auxSet r).image Dt.φ) Dt.internals
    have := card_image_le (s := auxSet r) (f := Dt.φ)
    omega
  refine ⟨Dt, hφP, hφC, hZ, hint, hlen, hpe', hin', hW,
    (fuel_card_le v _ _).trans (Nat.add_le_add hpe' hW), ?_, sub_pathEdge hH Dt, ?_, ?_⟩
  · intro y
    exact (OddSubdivision.pathEdges_degree_le (D := Dt)
      (filter_mem_card_le _ (paritySelector_degree_le r)) y).trans (by simp)
  · intro w hw
    rcases mem_union.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
      obtain ⟨i⟩ : Nonempty (Fin r) := by
        rcases x with i | (i | i)
        · exact ⟨i⟩
        · exact ⟨i⟩
        · exact ⟨i⟩
      refine root_adj_of_two hH hd (hCK x (hφC x hx)) (hψK i) ?_
      rw [← hφP i]
      intro h
      have := Dt.φ_inj h
      subst this
      simp [auxSet] at hx
    · exact root_adj_of_internal (Dt.mono hH) hw
  · intro S hS
    obtain ⟨F', h1, h2, -, h4, h5, h6, h7⟩ :=
      OddSubdivision.parity_subdiv_positive_modes (Dt.mono (hH.trans (typedLink_le_linkGraph G lab F v)))
        S hS
    exact ⟨F', h1, h2, typed_modeEdge (Dt.mono hH) F', h4, h5, h6, h7⟩

/-! ### BAL: bipartite active component -/

omit [DecidableEq V] in
lemma card_auxB_le (l r : ℕ) : (OddSubdivision.auxB l r).card ≤ 8 * max l r := by
  unfold OddSubdivision.auxB
  have h1 := card_union_le
    ((univ : Finset (Fin (4 * max l r))).image (fun a => (Sum.inl (Sum.inl a) : BV l r)))
    ((univ : Finset (Fin (4 * max l r))).image (fun b => (Sum.inr (Sum.inl b) : BV l r)))
  have h2 := card_image_le (s := (univ : Finset (Fin (4 * max l r))))
    (f := fun a => (Sum.inl (Sum.inl a) : BV l r))
  have h3 := card_image_le (s := (univ : Finset (Fin (4 * max l r))))
    (f := fun b => (Sum.inr (Sum.inl b) : BV l r))
  simp only [card_univ, Fintype.card_fin] at h2 h3
  omega

open Classical in
/-- **BAL selector routed in the typed link by bounded odd paths.**  For `k = max l r ≥ 1`,
from robust connectivity with diameter `D` of a bipartite active component `K` of `L_v` with
sides `X, Y ⊆ K`, and `|Z0| + 10k + 4D·200k ≤ M`, a balanced selector `QB` (bipartite, degree
`≤ 60`, `≤ 200k` edges) and an odd subdivision of it in the typed link, with paths of length
`≤ 4D+1`, sides respected, ports fixed and auxiliaries in their candidate sets, are constructed
before any mode; explicit base, internal, radial, fuel and degree bounds hold; every base edge
is typed and every radial edge is ambient; every balanced demand has a positive mode with the
same fuel. -/
theorem balanced_selector_typed (l r : ℕ) (hk : 1 ≤ max l r)
    (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (H : SimpleGraph V) (hH : H ≤ typedLink G lab F v) (K X Y Z0 : Finset V) (M D : ℕ)
    (hM : Z0.card + 10 * max l r + 4 * D * (200 * max l r) ≤ M)
    (hd : RobustDiam H K M D) (hXK : X ⊆ K) (hYK : Y ⊆ K) (hXY : Disjoint X Y)
    (hbip : ∀ x ∈ K, ∀ y ∈ K, H.Adj x y → (x ∈ X ↔ y ∉ X))
    (ψL : Fin l → V) (ψR : Fin r → V) (hψL : Function.Injective ψL)
    (hψR : Function.Injective ψR) (hψLX : ∀ p, ψL p ∈ X) (hψRY : ∀ q, ψR q ∈ Y)
    (hψLZ : ∀ p, ψL p ∉ Z0) (hψRZ : ∀ q, ψR q ∉ Z0)
    (Cand : BV l r → Finset V) (hCX : ∀ x : BV l r, x.isLeft → Cand x ⊆ X)
    (hCY : ∀ x : BV l r, x.isRight → Cand x ⊆ Y)
    (hCand : ∀ x, Z0.card + 10 * max l r ≤ (Cand x).card) :
    ∃ QB : SimpleGraph (BV l r),
      (∀ u w, QB.Adj u w → (u.isLeft ∧ w.isRight) ∨ (u.isRight ∧ w.isLeft)) ∧
      QB.maxDegree ≤ 60 ∧ QB.edgeFinset.card ≤ 200 * max l r ∧
      ∃ Dt : OddSubdivision H QB.edgeFinset,
        (∀ p, Dt.φ (Sum.inl (Sum.inr p)) = ψL p) ∧ (∀ q, Dt.φ (Sum.inr (Sum.inr q)) = ψR q) ∧
        (∀ x ∈ OddSubdivision.auxB l r, Dt.φ x ∈ Cand x) ∧ (∀ x, balSide X Y x (Dt.φ x)) ∧
        (∀ x, Dt.φ x ∉ Z0) ∧ (∀ y ∈ Dt.internals, y ∉ Z0) ∧
        (∀ e ∈ QB.edgeFinset, 2 * Dt.t e + 1 ≤ 4 * D + 1) ∧
        Dt.pathEdges.card ≤ (4 * D + 1) * (200 * max l r) ∧
        Dt.internals.card ≤ 4 * D * (200 * max l r) ∧
        ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals).card ≤
          8 * max l r + 4 * D * (200 * max l r) ∧
        (fuel v Dt.pathEdges ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals)).card ≤
          (4 * D + 1) * (200 * max l r) + (8 * max l r + 4 * D * (200 * max l r)) ∧
        (∀ y, (Dt.pathEdges.filter (fun f => y ∈ f)).card ≤ 60) ∧
        (∀ f ∈ Dt.pathEdges, ∃ x y, f = s(x, y) ∧ H.Adj x y ∧ (typedLink G lab F v).Adj x y) ∧
        (∀ w ∈ (OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals, G.Adj v w) ∧
        ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
          ∃ F' : Finset (Sym2 (BV l r)),
            IsMode QB.edgeFinset (OddSubdivision.auxB l r) (OddSubdivision.portsB SL SR) F' ∧
            IsMode Dt.pathEdges ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals)
              ((OddSubdivision.portsB SL SR).image Dt.φ) (Dt.modeEdges F') ∧
            (∀ e ∈ Dt.modeEdges F', ∃ x y, e = s(x, y) ∧ x ≠ y ∧
              TypedTriangle.SparseEdge.IsAllowed G lab F {v, x, y}) ∧
            (Dt.modeEdges F' : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
            Disjoint (fuel v Dt.pathEdges ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals))
              (radial v ((OddSubdivision.portsB SL SR).image Dt.φ)) ∧
            fuel v Dt.pathEdges ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals) ∪
                radial v ((OddSubdivision.portsB SL SR).image Dt.φ) =
              (Dt.modeEdges F').biUnion (triE v) ∪ (Dt.pathEdges \ Dt.modeEdges F') ∧
            Disjoint ((Dt.modeEdges F').biUnion (triE v)) (Dt.pathEdges \ Dt.modeEdges F') := by
  obtain ⟨QB, hbipQ, hdeg, hmax, hE, hQB⟩ := balancedSelector_exists l r hk
  refine ⟨QB, hbipQ, hmax, by convert hE, ?_⟩
  set Q := QB.edgeFinset
  have hQc : Q.card ≤ 200 * max l r := by convert hE
  let Ports : Finset (BV l r) := OddSubdivision.portsB univ univ
  have hPorts : ∀ x ∈ Ports, (∃ p, x = Sum.inl (Sum.inr p)) ∨ ∃ q, x = Sum.inr (Sum.inr q) := by
    intro x hx
    simp only [Ports, OddSubdivision.portsB, mem_union, mem_image, mem_univ, true_and] at hx
    rcases hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact Or.inl ⟨p, rfl⟩
    · exact Or.inr ⟨q, rfl⟩
  have hψ' : Set.InjOn (balPorts v ψL ψR) Ports := by
    intro x hx y hy hxy
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩ <;> rcases hPorts y hy with ⟨p', rfl⟩ | ⟨q', rfl⟩
    · simp only [balPorts] at hxy; rw [hψL hxy]
    · simp only [balPorts] at hxy
      exact absurd (hxy ▸ hψLX p) (disjoint_right.mp hXY (hψRY q'))
    · simp only [balPorts] at hxy
      exact absurd (hxy ▸ hψRY q) (disjoint_left.mp hXY (hψLX p'))
    · simp only [balPorts] at hxy; rw [hψR hxy]
  have hR : RobustOddPaths H (BalAllowed X Y) (4 * D + 1)
      (Z0.card + 10 * max l r + 4 * D * (200 * max l r)) :=
    robustOddPaths_bip hM hd hXK hYK hXY hbip
  have hside : ∀ e ∈ Q, ∀ x y, s(x, y) = e → ∀ a b, a ≠ b → balSide X Y x a →
      balSide X Y y b → BalAllowed X Y a b := by
    intro e he x y hxy a b _ ha hb
    rw [← hxy, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hbipQ x y he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨ha.1 hx, hb.2 hy⟩
    · exact Or.inr ⟨ha.2 hx, hb.1 hy⟩
  have hψS : ∀ x ∈ Ports, balSide X Y x (balPorts v ψL ψR x) := by
    intro x hx
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨fun _ => hψLX p, fun h => by simp at h⟩
    · exact ⟨fun h => by simp at h, fun _ => hψRY q⟩
  have hψZ : ∀ x ∈ Ports, balPorts v ψL ψR x ∉ Z0 := by
    intro x hx
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact hψLZ p
    · exact hψRZ q
  have hCS : ∀ x ∉ Ports, ∀ a ∈ Cand x, balSide X Y x a := by
    intro x _ a ha
    exact ⟨fun h => hCX x h ha, fun h => hCY x h ha⟩
  have hkV := card_BV_le l r
  obtain ⟨Dt, hP, hC, hZ, hlen, hint⟩ := greedy_embedding H (BalAllowed X Y)
    hR Q not_isDiag_of_mem (balSide X Y) hside Ports (balPorts v ψL ψR) hψ' hψS Z0 hψZ Cand hCS
    (fun x _ => le_trans (by omega) (hCand x))
    (by
      rw [Nat.add_sub_cancel]
      have : 4 * D * Q.card ≤ 4 * D * (200 * max l r) := Nat.mul_le_mul_left _ hQc
      omega)
  have hφS : ∀ x, balSide X Y x (Dt.φ x) := by
    intro x
    by_cases hx : x ∈ Ports
    · rw [hP x hx]; exact hψS x hx
    · exact hCS x hx _ (hC x hx)
  have hφC : ∀ x ∈ OddSubdivision.auxB l r, Dt.φ x ∈ Cand x := fun x hx =>
    hC x (fun hxP => disjoint_left.mp (OddSubdivision.portsB_disjoint univ univ) hxP hx)
  have hpe := OddSubdivision.pathEdges_card_le (D := Dt) hlen
  have hin := OddSubdivision.internals_card_le (D := Dt) hlen
  have hpe' : Dt.pathEdges.card ≤ (4 * D + 1) * (200 * max l r) :=
    hpe.trans (Nat.mul_le_mul_left _ hQc)
  have hin' : Dt.internals.card ≤ 4 * D * (200 * max l r) := by
    rw [Nat.add_sub_cancel] at hin; exact hin.trans (Nat.mul_le_mul_left _ hQc)
  have hW : ((OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals).card ≤
      8 * max l r + 4 * D * (200 * max l r) := by
    have := card_union_le ((OddSubdivision.auxB l r).image Dt.φ) Dt.internals
    have := card_image_le (s := OddSubdivision.auxB l r) (f := Dt.φ)
    have := card_auxB_le l r
    omega
  have h4k : 0 < 4 * max l r := by omega
  refine ⟨Dt, fun p => ?_, fun q => ?_, hφC, hφS, hZ, hint, hlen, hpe', hin', hW,
    (fuel_card_le v _ _).trans (Nat.add_le_add hpe' hW), ?_, sub_pathEdge hH Dt, ?_, ?_⟩
  · rw [hP _ (by simp [Ports, OddSubdivision.portsB])]; rfl
  · rw [hP _ (by simp [Ports, OddSubdivision.portsB])]; rfl
  · intro y
    exact (OddSubdivision.pathEdges_degree_le (D := Dt)
      (filter_mem_card_le QB hdeg) y).trans (by simp)
  · intro w hw
    rcases mem_union.mp hw with hw | hw
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hw
      have hxK : Dt.φ x ∈ K := by
        rcases x with x | x
        · exact hXK ((hφS _).1 rfl)
        · exact hYK ((hφS _).2 rfl)
      let yL : BV l r := Sum.inl (Sum.inl ⟨0, h4k⟩)
      let yR : BV l r := Sum.inr (Sum.inl ⟨0, h4k⟩)
      have hyL : Dt.φ yL ∈ X := (hφS yL).1 rfl
      have hyR : Dt.φ yR ∈ Y := (hφS yR).2 rfl
      rcases x with x | x
      · have hx : Dt.φ (Sum.inl x) ∈ X := (hφS _).1 rfl
        exact root_adj_of_two hH hd hxK (hYK hyR)
          (fun h => disjoint_left.mp hXY hx (h ▸ hyR))
      · have hx : Dt.φ (Sum.inr x) ∈ Y := (hφS _).2 rfl
        exact root_adj_of_two hH hd hxK (hXK hyL)
          (fun h => disjoint_left.mp hXY hyL (h ▸ hx))
    · exact root_adj_of_internal (Dt.mono hH) hw
  · intro SL SR hS
    obtain ⟨F', h1, h2, -, h4, h5, h6, h7⟩ :=
      OddSubdivision.balanced_subdiv_positive_modes QB hQB
        (Dt.mono (hH.trans (typedLink_le_linkGraph G lab F v))) SL SR hS
    exact ⟨F', h1, h2, typed_modeEdge (Dt.mono hH) F', h4, h5, h6, h7⟩

end SelTyped
