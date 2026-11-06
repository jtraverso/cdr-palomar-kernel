/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.LocalContract

@[expose] public section

/-!
# The simultaneous layer: fixed fuel, all modes, exact partitions (S07 §7) — V21

Fix a host `X` (the edges to be retired), a forbidden graph `B0`, a root set `Z` with `X[Z]`
empty (a hypothesis of THIS layer only), and a family `σ v` of local selectors with ports
`U_v = N_X(v)`.  `SimulFamily` records the three invariants produced by the scheduling
induction (`SimulSchedule.lean`):

* each `σ v` satisfies the local contract with windows `Z ∪ N_X(v) ∪ N_{B0}(v)` (vertices)
  and `E(X) ∪ E(B0)` (edges);
* base edges of distinct roots are disjoint;
* every vertex is an auxiliary of at most `q` roots.

From these, with `Δ(X) ≤ r` (no other input):

* `fuels_disjoint`, `fuelU_avoid` : the fuels `R_v = P_v ∪ {vw : w ∈ W_v}` are pairwise
  disjoint and the union `R` avoids `X ∪ B0`;
* `fuelU_edeg_le` : (7.3) `Δ(R) ≤ max(A·r, 60·r + 61·q)`;
* `layer_partition` : (7.4) for every `L ⊆ E(X)` whose stars at `Z` are locally admissible,
  with the SAME `R`: `R ∩ L = ∅`, `R ∪ L = E(D_L) ⊔ Y_L` exactly, `D_L` a packing of
  pairwise edge-disjoint PERMITTED triangles rooted in `Z`, `Y_L` without edges incident to
  `Z`, `Δ(Y_L) ≤ 61·r + 60·q`;
* `charge_identity` : (7.5) for every additive charge `c` on edges,
  `c(Y_L) − c(K_0) = c(L) − (c(D_L) − c(D_0))` with `K_0 = Y_∅`, exactly.

NOT claimed: that `K_0` or `Y_L` lies in the triangle lattice, or is decomposable.
-/

namespace SelSimul

open Finset SelBridge SelTyped

variable {V I : Type*} [DecidableEq V] [Fintype V]

section defs

variable (X : SimpleGraph V) [DecidableRel X.Adj]

/-- The demand of `L` at the root `v`: the ports `u ∈ N_X(v)` with `vu ∈ L`. -/
def demand (L : Finset (Sym2 V)) (v : V) : Finset V :=
  (X.neighborFinset v).filter (fun u => s(v, u) ∈ L)

/-- The union of the fuels. -/
def fuelU (Z : Finset V) (σ : V → LocalSel V) : Finset (Sym2 V) :=
  Z.biUnion (fun v => fuel v (σ v).P (σ v).W)

/-- The packing `D_L`: rooted triangles `(v, xy)`, `xy` in the mode of the demand at `v`. -/
def packing (Z : Finset V) (σ : V → LocalSel V) (L : Finset (Sym2 V)) :
    Finset (V × Sym2 V) :=
  Z.biUnion (fun v => ((σ v).mode (demand X L v)).image (fun e => (v, e)))

/-- Residual tokens `K_L`. -/
def tokens (Z : Finset V) (σ : V → LocalSel V) (L : Finset (Sym2 V)) : Finset (Sym2 V) :=
  Z.biUnion (fun v => (σ v).P \ (σ v).mode (demand X L v))

/-- The residual `Y_L = K_L ∪ {edges of L not meeting Z}`. -/
def residual (Z : Finset V) (σ : V → LocalSel V) (L : Finset (Sym2 V)) : Finset (Sym2 V) :=
  tokens X Z σ L ∪ L.filter (fun f => ∀ v ∈ Z, v ∉ f)

end defs

/-- Edge set of a family of rooted triangles. -/
def packEdges (D : Finset (V × Sym2 V)) : Finset (Sym2 V) := D.biUnion (fun p => triE p.1 p.2)

/-- **Invariants of the simultaneous family** (output of the scheduling induction). -/
structure SimulFamily (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z : Finset V)
    (Adm : V → Finset V → Prop) (A q : ℕ) (σ : V → LocalSel V) : Prop where
  valid : ∀ v ∈ Z, (σ v).Valid G lab F v (X.neighborFinset v) (Adm v)
    (Z ∪ X.neighborFinset v ∪ B0.neighborFinset v) (X.edgeFinset ∪ B0.edgeFinset) A
  disjP : ∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' → Disjoint (σ v).P (σ v').P
  cnt : ∀ x, auxCount Z (fun v => (σ v).W) x ≤ q

namespace SimulFamily

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj] {Z : Finset V}
  {Adm : V → Finset V → Prop} {A q : ℕ} {σ : V → LocalSel V}

/-- Auxiliaries lie outside `Z`. -/
lemma aux_not_Z (h : SimulFamily G lab F X B0 Z Adm A q σ) {v w : V} (hv : v ∈ Z)
    (hw : w ∈ (σ v).W) : w ∉ Z := fun hwZ =>
  disjoint_left.mp (h.valid v hv).avoidZ hw (by simp [hwZ])

/-- Auxiliaries are not `X`-neighbours of their root. -/
lemma aux_not_nbr (h : SimulFamily G lab F X B0 Z Adm A q σ) {v w : V} (hv : v ∈ Z)
    (hw : w ∈ (σ v).W) : ¬ X.Adj v w := fun hX =>
  disjoint_left.mp (h.valid v hv).avoidZ hw (by simp [hX])

omit [DecidableEq V] in
/-- Ports lie outside `Z` (`X[Z]` empty). -/
lemma port_not_Z (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {v u : V} (hv : v ∈ Z)
    (hu : u ∈ X.neighborFinset v) : u ∉ Z := fun huZ =>
  hZ v hv u huZ ((SimpleGraph.mem_neighborFinset _ _ _).mp hu)

/-- Vertices of base edges lie outside `Z`. -/
lemma base_vert_not_Z (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {v : V} (hv : v ∈ Z) {f : Sym2 V}
    (hf : f ∈ (σ v).P) {y : V} (hy : y ∈ f) : y ∉ Z := by
  rcases (h.valid v hv).supp f hf y hy with hu | hw
  · exact port_not_Z hZ hv hu
  · exact h.aux_not_Z hv hw

/-- Base edges are not edges of `X`. -/
lemma base_not_X (h : SimulFamily G lab F X B0 Z Adm A q σ) {v : V} (hv : v ∈ Z) {f : Sym2 V}
    (hf : f ∈ (σ v).P) : f ∉ X.edgeFinset := fun hX =>
  disjoint_left.mp (h.valid v hv).avoidB hf (mem_union_left _ hX)

/-- Base edges are not edges of `B0`. -/
lemma base_not_B0 (h : SimulFamily G lab F X B0 Z Adm A q σ) {v : V} (hv : v ∈ Z) {f : Sym2 V}
    (hf : f ∈ (σ v).P) : f ∉ B0.edgeFinset := fun hB =>
  disjoint_left.mp (h.valid v hv).avoidB hf (mem_union_right _ hB)

omit [Fintype V] in
lemma mem_radial {v : V} {W : Finset V} {f : Sym2 V} :
    f ∈ radial v W ↔ ∃ w ∈ W, f = s(v, w) := by
  simp only [radial, mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

omit [Fintype V] in
lemma mem_fuel {v : V} {P : Finset (Sym2 V)} {W : Finset V} {f : Sym2 V} :
    f ∈ fuel v P W ↔ f ∈ P ∨ ∃ w ∈ W, f = s(v, w) := by
  rw [fuel, mem_union, mem_radial]

/-- **Pairwise disjoint fuels.** -/
theorem fuels_disjoint (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {v v' : V} (hv : v ∈ Z) (hv' : v' ∈ Z)
    (hne : v ≠ v') : Disjoint (fuel v (σ v).P (σ v).W) (fuel v' (σ v').P (σ v').W) := by
  rw [disjoint_left]
  intro f hf hf'
  rw [mem_fuel] at hf hf'
  rcases hf with hf | ⟨w, hw, rfl⟩ <;> rcases hf' with hf' | ⟨w', hw', hf'⟩
  · exact disjoint_left.mp (h.disjP v hv v' hv' hne) hf hf'
  · exact h.base_vert_not_Z hZ hv hf (hf' ▸ Sym2.mem_mk_left v' w') hv'
  · exact h.base_vert_not_Z hZ hv' hf' (Sym2.mem_mk_left v w) hv
  · rcases Sym2.eq_iff.mp hf' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hne h1
    · exact h.aux_not_Z hv' hw' (h1 ▸ hv)

/-- **The fuel avoids `X ∪ B0`.** -/
theorem fuelU_avoid (h : SimulFamily G lab F X B0 Z Adm A q σ) :
    Disjoint (fuelU Z σ) (X.edgeFinset ∪ B0.edgeFinset) := by
  rw [disjoint_left]
  intro f hf hXB
  obtain ⟨v, hv, hf⟩ := mem_biUnion.mp hf
  rcases mem_fuel.mp hf with hf | ⟨w, hw, rfl⟩
  · exact disjoint_left.mp (h.valid v hv).avoidB hf hXB
  · rcases mem_union.mp hXB with hX | hB
    · exact h.aux_not_nbr hv hw (SimpleGraph.mem_edgeFinset.mp hX)
    · exact disjoint_left.mp (h.valid v hv).avoidZ hw
        (mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr
          (SimpleGraph.mem_edgeFinset.mp hB)))

/-- Bases and auxiliaries lie outside `Z`. -/
theorem outside_Z (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') :
    ∀ v ∈ Z, (∀ w ∈ (σ v).W, w ∉ Z) ∧ ∀ f ∈ (σ v).P, ∀ y ∈ f, y ∉ Z :=
  fun _ hv => ⟨fun _ hw => h.aux_not_Z hv hw, fun _ hf _ hy => h.base_vert_not_Z hZ hv hf hy⟩

/-- Degree of the union of the bases: `≤ 60·(r + q)`. -/
theorem bases_edeg_le (h : SimulFamily G lab F X B0 Z Adm A q σ) {r : ℕ}
    (hX : ∀ x, X.degree x ≤ r) (y : V) :
    edeg (Z.biUnion (fun v => (σ v).P)) y ≤ 60 * (r + q) := by
  refine (edeg_biUnion_le Z _ (fun v => X.neighborFinset v ∪ (σ v).W)
    (fun v hv => (h.valid v hv).deg_le)
    (fun v hv f hf y hy => mem_union.mpr ((h.valid v hv).supp f hf y hy)) y).trans ?_
  refine Nat.mul_le_mul_left _ ?_
  have h1 := filter_or_card_le Z (fun v => y ∈ X.neighborFinset v) (fun v => y ∈ (σ v).W)
  have h2 := portCount_le X Z y
  have h3 : (Z.filter (fun v => y ∈ (σ v).W)).card ≤ q := h.cnt y
  have h4 := hX y
  simp only [mem_union]
  omega

/-- **(7.3)** `Δ(R) ≤ max(A·r, 60·r + 61·q)`. -/
theorem fuelU_edeg_le (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {r : ℕ} (hX : ∀ x, X.degree x ≤ r) (y : V) :
    edeg (fuelU Z σ) y ≤ max (A * r) (60 * r + 61 * q) := by
  have hsplit : fuelU Z σ =
      Z.biUnion (fun v => (σ v).P) ∪ Z.biUnion (fun v => radial v (σ v).W) := by
    ext f; simp only [fuelU, fuel, mem_biUnion, mem_union]
    constructor
    · rintro ⟨v, hv, h | h⟩
      · exact Or.inl ⟨v, hv, h⟩
      · exact Or.inr ⟨v, hv, h⟩
    · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact ⟨v, hv, Or.inl h⟩
      · exact ⟨v, hv, Or.inr h⟩
  rw [hsplit]
  refine (edeg_union_le _ _ y).trans ?_
  by_cases hy : y ∈ Z
  · have hb : edeg (Z.biUnion (fun v => (σ v).P)) y = 0 := by
      unfold edeg
      rw [card_eq_zero, filter_eq_empty_iff]
      intro f hf hyf
      obtain ⟨v, hv, hf⟩ := mem_biUnion.mp hf
      exact h.base_vert_not_Z hZ hv hf hyf hy
    have hr : edeg (Z.biUnion (fun v => radial v (σ v).W)) y ≤ A * r := by
      unfold edeg
      have hsub : (Z.biUnion (fun v => radial v (σ v).W)).filter (fun f => y ∈ f) ⊆
          radial y (σ y).W := by
        intro f hf
        rw [mem_filter, mem_biUnion] at hf
        obtain ⟨⟨v, hv, hf⟩, hyf⟩ := hf
        obtain ⟨w, hw, rfl⟩ := mem_radial.mp hf
        rcases Sym2.mem_iff.mp hyf with rfl | rfl
        · exact mem_radial.mpr ⟨w, hw, rfl⟩
        · exact absurd hy (h.aux_not_Z hv hw)
      refine (card_le_card hsub).trans ?_
      rw [radial_card]
      refine ((h.valid y hy).card_le).trans (Nat.mul_le_mul_left _ ?_)
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX y
    rw [hb]; omega
  · have hb := h.bases_edeg_le hX y
    have hr : edeg (Z.biUnion (fun v => radial v (σ v).W)) y ≤ q := by
      unfold edeg
      have hsub : (Z.biUnion (fun v => radial v (σ v).W)).filter (fun f => y ∈ f) ⊆
          (Z.filter (fun v => y ∈ (σ v).W)).image (fun v => s(v, y)) := by
        intro f hf
        rw [mem_filter, mem_biUnion] at hf
        obtain ⟨⟨v, hv, hf⟩, hyf⟩ := hf
        obtain ⟨w, hw, rfl⟩ := mem_radial.mp hf
        rcases Sym2.mem_iff.mp hyf with rfl | rfl
        · exact absurd hv hy
        · exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hw⟩, rfl⟩
      exact (card_le_card hsub).trans (card_image_le.trans (h.cnt y))
    omega

/-! ### All modes with the same fuel -/

/-- Each edge of `L ⊆ E(X)` meeting `Z` is a radial input of its root's demand. -/
lemma L_split {L : Finset (Sym2 V)} (hL : L ⊆ X.edgeFinset) :
    L = Z.biUnion (fun v => radial v (demand X L v)) ∪ L.filter (fun f => ∀ v ∈ Z, v ∉ f) := by
  ext f
  simp only [mem_union, mem_biUnion, mem_filter, mem_radial, demand]
  constructor
  · intro hf
    by_cases hZf : ∀ v ∈ Z, v ∉ f
    · exact Or.inr ⟨hf, hZf⟩
    · push_neg at hZf
      obtain ⟨v, hv, hvf⟩ := hZf
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hvf
      have hX : X.Adj v u := SimpleGraph.mem_edgeFinset.mp (hL hf)
      exact Or.inl ⟨v, hv, u, ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hX, hf⟩, rfl⟩
  · rintro (⟨v, -, u, ⟨-, hu⟩, rfl⟩ | ⟨hf, -⟩)
    · exact hu
    · exact hf

lemma packEdges_packing (L : Finset (Sym2 V)) :
    packEdges (packing X Z σ L) =
      Z.biUnion (fun v => ((σ v).mode (demand X L v)).biUnion (triE v)) := by
  ext f
  simp only [packEdges, packing, mem_biUnion, mem_image]
  constructor
  · rintro ⟨p, ⟨v, hv, e, he, rfl⟩, hf⟩; exact ⟨v, hv, e, he, hf⟩
  · rintro ⟨v, hv, e, he, hf⟩; exact ⟨(v, e), ⟨v, hv, e, he, rfl⟩, hf⟩

lemma mem_packing {L : Finset (Sym2 V)} {p : V × Sym2 V} :
    p ∈ packing X Z σ L ↔ p.1 ∈ Z ∧ p.2 ∈ (σ p.1).mode (demand X L p.1) := by
  simp only [packing, mem_biUnion, mem_image]
  constructor
  · rintro ⟨v, hv, e, he, rfl⟩; exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩; exact ⟨p.1, hv, p.2, he, rfl⟩

/-- **(7.4) Simultaneous modes with one fixed fuel.** -/
theorem layer_partition (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {r : ℕ} (hX : ∀ x, X.degree x ≤ r)
    {L : Finset (Sym2 V)} (hL : L ⊆ X.edgeFinset) (hadm : ∀ v ∈ Z, Adm v (demand X L v)) :
    Disjoint (fuelU Z σ) L ∧
    fuelU Z σ ∪ L = packEdges (packing X Z σ L) ∪ residual X Z σ L ∧
    Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L) ∧
    (packing X Z σ L : Set (V × Sym2 V)).PairwiseDisjoint (fun p => triE p.1 p.2) ∧
    (∀ p ∈ packing X Z σ L, p.1 ∈ Z ∧ ∃ x y, p.2 = s(x, y) ∧ x ≠ y ∧
      TypedTriangle.SparseEdge.IsAllowed G lab F {p.1, x, y}) ∧
    (∀ f ∈ residual X Z σ L, ∀ v ∈ Z, v ∉ f) ∧
    (∀ y, edeg (residual X Z σ L) y ≤ 61 * r + 60 * q) := by
  have hM : ∀ v ∈ Z, IsMode (σ v).P (σ v).W (demand X L v) ((σ v).mode (demand X L v)) :=
    fun v hv => (h.valid v hv).modes _ (filter_subset _ _) (hadm v hv)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- R ∩ L = ∅
    exact (h.fuelU_avoid).mono_right (hL.trans subset_union_left)
  · -- exact partition
    rw [residual, packEdges_packing]
    conv_lhs => rw [L_split (Z := Z) hL]
    have hpart : ∀ v ∈ Z, fuel v (σ v).P (σ v).W ∪ radial v (demand X L v) =
        ((σ v).mode (demand X L v)).biUnion (triE v) ∪ ((σ v).P \ (σ v).mode (demand X L v)) :=
      fun v hv => mode_partition (hM v hv)
    ext f
    simp only [fuelU, tokens, mem_union, mem_biUnion]
    constructor
    · rintro (⟨v, hv, hf⟩ | ⟨v, hv, hf⟩ | hf)
      · have := (Finset.ext_iff.mp (hpart v hv) f).mp (mem_union_left _ hf)
        rcases mem_union.mp this with h1 | h1
        · exact Or.inl ⟨v, hv, mem_biUnion.mp h1⟩
        · exact Or.inr (Or.inl ⟨v, hv, h1⟩)
      · have := (Finset.ext_iff.mp (hpart v hv) f).mp (mem_union_right _ hf)
        rcases mem_union.mp this with h1 | h1
        · exact Or.inl ⟨v, hv, mem_biUnion.mp h1⟩
        · exact Or.inr (Or.inl ⟨v, hv, h1⟩)
      · exact Or.inr (Or.inr hf)
    · rintro (⟨v, hv, e, he, hf⟩ | ⟨v, hv, hf⟩ | hf)
      · have := (Finset.ext_iff.mp (hpart v hv) f).mpr
          (mem_union_left _ (mem_biUnion.mpr ⟨e, he, hf⟩))
        rcases mem_union.mp this with h1 | h1
        · exact Or.inl ⟨v, hv, h1⟩
        · exact Or.inr (Or.inl ⟨v, hv, h1⟩)
      · have := (Finset.ext_iff.mp (hpart v hv) f).mpr (mem_union_right _ hf)
        rcases mem_union.mp this with h1 | h1
        · exact Or.inl ⟨v, hv, h1⟩
        · exact Or.inr (Or.inl ⟨v, hv, h1⟩)
      · exact Or.inr (Or.inr hf)
  · -- triangles and residual are disjoint
    rw [disjoint_left]
    intro f hf hY
    obtain ⟨p, hp, hf⟩ := mem_biUnion.mp hf
    obtain ⟨hv, he⟩ := mem_packing.mp hp
    have heP := (hM p.1 hv).1 he
    rcases (mem_triE p.1 p.2 f).mp hf with rfl | ⟨x, hx, rfl⟩
    · rcases mem_union.mp hY with hY | hY
      · obtain ⟨v', hv', hY⟩ := mem_biUnion.mp hY
        rw [mem_sdiff] at hY
        by_cases hvv : p.1 = v'
        · subst hvv; exact hY.2 he
        · exact disjoint_left.mp (h.disjP _ hv _ hv' hvv) heP hY.1
      · exact h.base_not_X hv heP (hL (mem_filter.mp hY).1)
    · rcases mem_union.mp hY with hY | hY
      · obtain ⟨v', hv', hY⟩ := mem_biUnion.mp hY
        exact h.base_vert_not_Z hZ hv' (mem_sdiff.mp hY).1 (Sym2.mem_mk_left _ _) hv
      · exact (mem_filter.mp hY).2 p.1 hv (Sym2.mem_mk_left _ _)
  · -- pairwise disjoint triangles
    intro p hp p' hp' hne
    obtain ⟨hv, he⟩ := mem_packing.mp (mem_coe.mp hp)
    obtain ⟨hv', he'⟩ := mem_packing.mp (mem_coe.mp hp')
    have heP := (hM p.1 hv).1 he
    have heP' := (hM p'.1 hv').1 he'
    by_cases hvv : p.1 = p'.1
    · have hee : p.2 ≠ p'.2 := fun h2 => hne (Prod.ext hvv h2)
      have := mode_pairwiseDisjoint (h.valid p.1 hv).inLink (hM p.1 hv)
      rw [← hvv] at he'
      have hd := this (mem_coe.mpr he) (mem_coe.mpr he') hee
      simpa [Function.onFun, hvv] using hd
    · simp only [Function.onFun]
      rw [disjoint_left]
      intro f hf hf'
      rcases (mem_triE _ _ f).mp hf with rfl | ⟨x, hx, rfl⟩ <;>
        rcases (mem_triE _ _ _).mp hf' with h2 | ⟨x', hx', h2⟩
      · exact disjoint_left.mp (h.disjP _ hv _ hv' hvv) heP (h2 ▸ heP')
      · exact h.base_vert_not_Z hZ hv heP (h2 ▸ Sym2.mem_mk_left _ _) hv'
      · exact h.base_vert_not_Z hZ hv' heP' (h2 ▸ Sym2.mem_mk_left _ _) hv
      · rcases Sym2.eq_iff.mp h2 with ⟨h3, -⟩ | ⟨h3, -⟩
        · exact hvv h3
        · exact h.base_vert_not_Z hZ hv' heP' hx' (h3 ▸ hv)
  · -- permitted triangles rooted in Z
    intro p hp
    obtain ⟨hv, he⟩ := mem_packing.mp hp
    exact ⟨hv, (h.valid p.1 hv).permitted ((hM p.1 hv).1 he)⟩
  · -- no residual edge meets Z
    intro f hf v hv hvf
    rcases mem_union.mp hf with hf | hf
    · obtain ⟨v', hv', hf⟩ := mem_biUnion.mp hf
      exact h.base_vert_not_Z hZ hv' (mem_sdiff.mp hf).1 hvf hv
    · exact (mem_filter.mp hf).2 v hv hvf
  · -- degree of the residual
    intro y
    refine (edeg_union_le _ _ y).trans ?_
    have h1 : edeg (tokens X Z σ L) y ≤ 60 * (r + q) := by
      refine le_trans (edeg_mono ?_ y) (h.bases_edeg_le hX y)
      exact biUnion_mono fun v _ => sdiff_subset
    have h2 : edeg (L.filter (fun f => ∀ v ∈ Z, v ∉ f)) y ≤ r := by
      refine le_trans (edeg_mono ((filter_subset _ _).trans hL) y) ?_
      rw [edeg_edgeFinset]; exact hX y
    omega

/-- **(7.5) Exact charge identity relative to `K_0 = Y_∅`**: for every additive charge `c`
on edges, `c(Y_L) − c(K_0) = c(L) − (c(D_L) − c(D_0))`, where `c(D)` sums `c` over the three
edges of each triangle. -/
theorem charge_identity (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {r : ℕ} (hX : ∀ x, X.degree x ≤ r)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    {L : Finset (Sym2 V)} (hL : L ⊆ X.edgeFinset) (hadm : ∀ v ∈ Z, Adm v (demand X L v))
    {M : Type*} [AddCommGroup M] (c : Sym2 V → M) :
    ∑ f ∈ residual X Z σ L, c f - ∑ f ∈ residual X Z σ ∅, c f =
      ∑ f ∈ L, c f - (∑ p ∈ packing X Z σ L, ∑ f ∈ triE p.1 p.2, c f -
        ∑ p ∈ packing X Z σ ∅, ∑ f ∈ triE p.1 p.2, c f) := by
  have hdem0 : ∀ v, demand X ∅ v = ∅ := fun v => by simp [demand]
  obtain ⟨hRL, hpart, hdisj, hpw, -⟩ := h.layer_partition hZ hX hL hadm
  obtain ⟨-, hpart0, hdisj0, hpw0, -⟩ :=
    h.layer_partition hZ hX (empty_subset _) (fun v hv => by rw [hdem0]; exact hAdm0 v hv)
  have e1 := congrArg (fun s => ∑ f ∈ s, c f) hpart
  rw [sum_union hRL, sum_union hdisj, packEdges, sum_biUnion hpw] at e1
  have e0 := congrArg (fun s => ∑ f ∈ s, c f) hpart0
  simp only [union_empty] at e0
  rw [sum_union hdisj0, packEdges, sum_biUnion hpw0] at e0
  have hY : ∑ f ∈ residual X Z σ L, c f = ∑ f ∈ fuelU Z σ, c f + ∑ f ∈ L, c f -
      ∑ p ∈ packing X Z σ L, ∑ f ∈ triE p.1 p.2, c f := by rw [e1]; abel
  have hY0 : ∑ f ∈ residual X Z σ ∅, c f = ∑ f ∈ fuelU Z σ, c f -
      ∑ p ∈ packing X Z σ ∅, ∑ f ∈ triE p.1 p.2, c f := by rw [e0]; abel
  rw [hY, hY0]; abel

/-- **(7.5) in indicator form**: for every edge `e`,
`[e ∈ Y_L] − [e ∈ K_0] = [e ∈ L] − (#{t ∈ D_L : e ∈ t} − #{t ∈ D_0 : e ∈ t})` in `ℤ`. -/
theorem indicator_identity (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {r : ℕ} (hX : ∀ x, X.degree x ≤ r)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    {L : Finset (Sym2 V)} (hL : L ⊆ X.edgeFinset) (hadm : ∀ v ∈ Z, Adm v (demand X L v))
    (e : Sym2 V) :
    ((if e ∈ residual X Z σ L then 1 else 0 : ℤ) - if e ∈ residual X Z σ ∅ then 1 else 0) =
      (if e ∈ L then 1 else 0 : ℤ) -
        ((((packing X Z σ L).filter (fun p => e ∈ triE p.1 p.2)).card : ℤ) -
          (((packing X Z σ ∅).filter (fun p => e ∈ triE p.1 p.2)).card : ℤ)) := by
  have := h.charge_identity hZ hX hAdm0 hL hadm (fun f => if f = e then (1 : ℤ) else 0)
  simp only [sum_ite_eq', sum_boole] at this
  convert this using 3

end SimulFamily

end SelSimul
