/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Host

/-!
# The CDR host for Paper III: hypothesis H2 (the all-edges indicator is physical)

Direct lattice argument, independent of any decomposition and of every external hypothesis.

Work in the quotient `Q = ℤ^{Sym2 V} / Λ` (`Λ` = integer span of the bicoloured triangles of the
complete graph labelled by three classes) and write `g e` for the class of the edge `e`.

* A bicoloured triangle `xyz` gives `g(xy) + g(xz) + g(yz) = 0`.
* With three points in a class `X` and `w, w' ∉ X`, the difference `g(xw) - g(xw')` is
  independent of `x ∈ X` and has order `2` (`tri_D`).
* Fix a base point `o_X` in each class and set `ε(v) = g(v o_{X+1}) - g(o_X o_{X+1})` for
  `v ∈ X`. Then `2ε = 0` and every edge satisfies
  `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)` (`formula`), where `κ(X,Y) = g(o_X o_Y)` for `X ≠ Y`
  and `κ(X,X) = -2 g(o_X o_{X+1})`; moreover `2κ(X,Y)` is the same element `γ` for all `X ≠ Y`.
* Summing over all edges: the `ε` part is `(n-1) Σ ε = 0` (`n` odd), and the `κ` part is
  `(Σ_{X<Y} |X||Y|/2 - Σ_X C(|X|,2)) γ`, which vanishes by the admissibility identity
  (every product `|X||Y|` is even).

Requires only: each class has at least three points, `n` odd, the three products even, and the
admissibility identity.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Lattice

variable {V : Type*} [Fintype V]

/-- The complete host labelled by `lab`. -/
abbrev cHost (lab : V → Fin 3) : Host V (Fin 3) := ⟨⊤, lab⟩

/-- The quotient of `ℤ^{Sym2 V}` by the physical lattice. -/
abbrev LQ (lab : V → Fin 3) := (Sym2 V → ℤ) ⧸ lattice (cHost lab) cdrF

/-- The class of a single edge. -/
def gq (lab : V → Fin 3) (e : Sym2 V) : LQ lab :=
  Submodule.Quotient.mk (ind ({e} : Finset (Sym2 V)))

/-- Size of a class. -/
def csz (lab : V → Fin 3) (k : Fin 3) : ℕ := (univ.filter fun v => lab v = k).card

/-- Every class has a point avoiding any two given points. -/
def Big (lab : V → Fin 3) : Prop := ∀ (k : Fin 3) (u v : V), ∃ w, lab w = k ∧ w ≠ u ∧ w ≠ v

theorem cdrF_of {p q r : Fin 3}
    (h : (p = q ∧ q ≠ r) ∨ (p = r ∧ p ≠ q) ∨ (q = r ∧ p ≠ q)) :
    ({p, q, r} : Multiset (Fin 3)) ∈ cdrF := by
  simp only [cdrF, Set.mem_ofPred_eq]
  revert h
  fin_cases p <;> fin_cases q <;> fin_cases r <;> decide

theorem fin3_succ_ne (X : Fin 3) : X + 1 ≠ X := by fin_cases X <;> decide

theorem triEdges_triple [DecidableEq V] {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = {s(x, y), s(x, z), s(y, z)} := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_insert,
      mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hu, hv⟩, huv⟩
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> simp_all
    · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
        simp_all <;> (intro h; subst h; simp_all)

theorem ind_triple [DecidableEq V] {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ind (triEdges ({x, y, z} : Finset V)) =
      ind {s(x, y)} + ind {s(x, z)} + ind {s(y, z)} := by
  rw [triEdges_triple hxy hxz hyz]
  have h1 : s(x, y) ≠ s(x, z) := by simp [hyz, hxz]
  have h2 : s(x, y) ≠ s(y, z) := by simp [hxy, hxz]
  have h3 : s(x, z) ≠ s(y, z) := by simp [hxy, hxz]
  funext e
  simp only [ind, Pi.add_apply, mem_insert, mem_singleton]
  by_cases e1 : e = s(x, y) <;> by_cases e2 : e = s(x, z) <;> by_cases e3 : e = s(y, z) <;>
    simp_all

theorem isAllowed_triple [DecidableEq V] (lab : V → Fin 3) {x y z : V} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF) :
    IsAllowed (cHost lab) cdrF {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, fun u _ v _ huv => ?_, ?_⟩
  · simpa [cHost] using huv
  · rw [val_map_triple lab hxy (Ne.symm hxz) (Ne.symm hyz)]; exact hF

/-- Triangle relation in the quotient. -/
theorem tri_rel (lab : V → Fin 3) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF) :
    gq lab s(x, y) + gq lab s(x, z) + gq lab s(y, z) = 0 := by
  classical
  have hmem : ind (triEdges ({x, y, z} : Finset V)) ∈ lattice (cHost lab) cdrF :=
    Submodule.subset_span ⟨{x, y, z}, isAllowed_triple lab hxy hxz hyz hF, rfl⟩
  rw [ind_triple hxy hxz hyz] at hmem
  simp only [gq, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

theorem eq_neg_sub_of_add {G : Type*} [AddCommGroup G] {a b c : G} (h : a + b + c = 0) :
    a = -b - c := by
  rw [← sub_eq_zero, ← h]; abel

/-- A monochromatic edge in terms of two bichromatic ones. -/
theorem mono_rel (lab : V → Fin 3) {x x' w : V} (hxx : x ≠ x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) :
    gq lab s(x, x') = -gq lab s(x, w) - gq lab s(x', w) := by
  have hxw : x ≠ w := fun h => hw (by rw [h])
  have hx'w : x' ≠ w := fun h => hw (by rw [← h, hl])
  exact eq_neg_sub_of_add (tri_rel lab hxx hxw hx'w
    (cdrF_of (Or.inl ⟨hl.symm, by rw [hl]; exact Ne.symm hw⟩)))

theorem sq_rel (lab : V → Fin 3) {x x' w w' : V} (hxx : x ≠ x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x) :
    (gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x', w) - gq lab s(x', w')) = 0 := by
  have h1 := mono_rel lab hxx hl hw
  have h2 := mono_rel lab hxx hl hw'
  rw [h1] at h2
  rw [← neg_eq_zero, ← sub_eq_zero.2 h2]; abel

/-- With three points of a class: the difference `g(xw) - g(xw')` has order two and does not
depend on `x`. -/
theorem tri_D (lab : V → Fin 3) {x x' x'' w w' : V} (h1 : x ≠ x') (h2 : x ≠ x'')
    (h3 : x' ≠ x'') (l1 : lab x' = lab x) (l2 : lab x'' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) :
    (gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x, w) - gq lab s(x, w')) = 0 ∧
    gq lab s(x', w) - gq lab s(x', w') = gq lab s(x, w) - gq lab s(x, w') := by
  have A := sq_rel lab h1 l1 hw hw'
  have B := sq_rel lab h2 l2 hw hw'
  have C := sq_rel lab (w := w) (w' := w') h3 (l2.trans l1.symm) (by rw [l1]; exact hw) (by rw [l1]; exact hw')
  have hD : (gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x, w) - gq lab s(x, w')) = 0 := by
    calc _ = ((gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x', w) - gq lab s(x', w'))) +
          ((gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x'', w) - gq lab s(x'', w'))) -
          ((gq lab s(x', w) - gq lab s(x', w')) + (gq lab s(x'', w) - gq lab s(x'', w'))) := by
            abel
      _ = 0 := by rw [A, B, C]; simp
  refine ⟨hD, ?_⟩
  rw [← sub_eq_zero]
  calc _ = ((gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x', w) - gq lab s(x', w'))) -
        ((gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x, w) - gq lab s(x, w'))) := by abel
    _ = 0 := by rw [A, hD, sub_zero]

/-! ### Base points and the vertex potential `ε` -/

/-- The vertex potential. -/
def eps (lab : V → Fin 3) (o : Fin 3 → V) (v : V) : LQ lab :=
  gq lab s(v, o (lab v + 1)) - gq lab s(o (lab v), o (lab v + 1))

/-- The class of the edge between two base points. -/
def beta (lab : V → Fin 3) (o : Fin 3 → V) (X Y : Fin 3) : LQ lab := gq lab s(o X, o Y)

/-- The class constant. -/
def kap (lab : V → Fin 3) (o : Fin 3 → V) (X Y : Fin 3) : LQ lab :=
  if X = Y then -(beta lab o X (X + 1) + beta lab o X (X + 1)) else beta lab o X Y

variable {lab : V → Fin 3} {o : Fin 3 → V}

theorem eps_base (ho : ∀ k, lab (o k) = k) (k : Fin 3) : eps lab o (o k) = 0 := by
  simp only [eps, ho k, sub_self]

theorem eps_spec (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {v w : V} (hw : lab w ≠ lab v) :
    gq lab s(v, w) = gq lab s(o (lab v), w) + eps lab o v := by
  by_cases hv : v = o (lab v)
  · have : eps lab o v = 0 := by
      unfold eps; rw [← hv, sub_self]
    rw [this, add_zero, ← hv]
  · obtain ⟨x'', hl'', h1, h2⟩ := hbig (lab v) v (o (lab v))
    have hw' : lab (o (lab v + 1)) ≠ lab v := by rw [ho]; exact fin3_succ_ne _
    have E := (tri_D lab hv (Ne.symm h1) (Ne.symm h2) (ho _) hl'' hw hw').2
    rw [← sub_eq_zero] at E
    unfold eps
    rw [← sub_eq_zero, ← neg_eq_zero, ← E]; abel

theorem two_eps (hbig : Big lab) (ho : ∀ k, lab (o k) = k) (v : V) :
    eps lab o v + eps lab o v = 0 := by
  obtain ⟨y1, hy1, h11, -⟩ := hbig (lab v + 1) (o (lab v + 1)) (o (lab v + 1))
  obtain ⟨y2, hy2, h21, h22⟩ := hbig (lab v + 1) (o (lab v + 1)) y1
  have lw : lab (o (lab v + 1)) = lab v + 1 := ho _
  have hv : lab v ≠ lab (o (lab v + 1)) := by rw [lw]; exact (fin3_succ_ne _).symm
  have ho' : lab (o (lab v)) ≠ lab (o (lab v + 1)) := by
    rw [lw, ho]; exact (fin3_succ_ne _).symm
  have := (tri_D lab (x := o (lab v + 1)) (x' := y1) (x'' := y2) (Ne.symm h11) (Ne.symm h21)
    (Ne.symm h22) (hy1.trans lw.symm) (hy2.trans lw.symm) hv ho').1
  unfold eps
  rw [Sym2.eq_swap (a := v), Sym2.eq_swap (a := o (lab v))]
  exact this

theorem beta_symm (X Y : Fin 3) : beta lab o X Y = beta lab o Y X := by
  unfold beta; rw [Sym2.eq_swap]

theorem bichrom_formula (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {u v : V}
    (huv : lab u ≠ lab v) :
    gq lab s(u, v) = beta lab o (lab u) (lab v) + eps lab o u + eps lab o v := by
  rw [eps_spec hbig ho (Ne.symm huv), Sym2.eq_swap (a := o (lab u)),
    eps_spec hbig ho (v := v) (w := o (lab u)) (by rw [ho]; exact huv)]
  unfold beta
  rw [Sym2.eq_swap (a := o (lab v))]; abel

theorem mono_formula (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {u v : V} (huv : u ≠ v)
    (hl : lab v = lab u) :
    gq lab s(u, v) = -(beta lab o (lab u) (lab u + 1) + beta lab o (lab u) (lab u + 1)) +
      eps lab o u + eps lab o v := by
  have hw : lab (o (lab u + 1)) ≠ lab u := by rw [ho]; exact fin3_succ_ne _
  rw [mono_rel lab huv hl hw, bichrom_formula hbig ho (Ne.symm hw),
    bichrom_formula hbig ho (u := v) (v := o (lab u + 1)) (by rw [hl]; exact Ne.symm hw)]
  simp only [ho, eps_base ho, add_zero]
  rw [hl]
  have h1 := two_eps hbig ho u
  have h2 := two_eps hbig ho v
  rw [← sub_eq_zero]
  calc _ = -((eps lab o u + eps lab o u) + (eps lab o v + eps lab o v)) := by abel
    _ = 0 := by rw [h1, h2]; simp

/-- **Edge formula**: `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)`. -/
theorem formula (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {u v : V} (huv : u ≠ v) :
    gq lab s(u, v) = kap lab o (lab u) (lab v) + eps lab o u + eps lab o v := by
  unfold kap
  by_cases hl : lab u = lab v
  · rw [if_pos hl, mono_formula hbig ho huv hl.symm]
  · rw [if_neg hl, bichrom_formula hbig ho hl]

theorem beta_rel (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {X Y Z : Fin 3} (hXY : X ≠ Y)
    (hXZ : X ≠ Z) :
    beta lab o X Y + beta lab o X Y = beta lab o X Z + beta lab o X Z := by
  obtain ⟨x1, hx1, h11, -⟩ := hbig X (o X) (o X)
  obtain ⟨x2, hx2, h21, h22⟩ := hbig X (o X) x1
  have := (tri_D lab (x := o X) (x' := x1) (x'' := x2) (w := o Y) (w' := o Z) (Ne.symm h11)
    (Ne.symm h21) (Ne.symm h22) (by rw [hx1, ho]) (by rw [hx2, ho])
    (by rw [ho, ho]; exact Ne.symm hXY) (by rw [ho, ho]; exact Ne.symm hXZ)).1
  unfold beta
  rw [← sub_eq_zero, ← this]; abel

theorem two_beta (hbig : Big lab) (ho : ∀ k, lab (o k) = k) {X Y : Fin 3} (h : X ≠ Y) :
    beta lab o X Y + beta lab o X Y = beta lab o 0 1 + beta lab o 0 1 := by
  have c02 : beta lab o 0 2 + beta lab o 0 2 = beta lab o 0 1 + beta lab o 0 1 :=
    beta_rel hbig ho (by decide) (by decide)
  have c12 : beta lab o 1 2 + beta lab o 1 2 = beta lab o 0 1 + beta lab o 0 1 := by
    rw [beta_rel hbig ho (X := 1) (Y := 2) (Z := 0) (by decide) (by decide), beta_symm 1 0]
  obtain rfl | rfl | rfl : X = 0 ∨ X = 1 ∨ X = 2 := by fin_cases X <;> simp
  all_goals obtain rfl | rfl | rfl : Y = 0 ∨ Y = 1 ∨ Y = 2 := by fin_cases Y <;> simp
  all_goals first
    | exact absurd rfl h
    | rfl
    | exact c02
    | exact c12
    | (rw [beta_symm]; exact c02)
    | (rw [beta_symm]; exact c12)
    | (rw [beta_symm])

/-! ### Summation -/

theorem ind_edges_eq_sum (lab : V → Fin 3) :
    ind (edges (cHost lab)) = ∑ e ∈ edges (cHost lab), ind ({e} : Finset (Sym2 V)) := by
  classical
  funext e'
  rw [Finset.sum_apply]
  by_cases h : e' ∈ edges (cHost lab)
  · rw [sum_eq_single_of_mem e' h]
    · simp [ind, h]
    · intro b _ hb; simp [ind, Ne.symm hb]
  · rw [sum_eq_zero]
    · simp [ind, h]
    · intro b hb
      have : e' ≠ b := fun h' => h (h' ▸ hb)
      simp [ind, this]

theorem edges_cHost [DecidableEq V] (lab : V → Fin 3) :
    edges (cHost lab) = (univ : Finset V).sym2.filter (fun e => ¬ e.IsDiag) := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [edges, cHost]

theorem sum_offDiag_fst [DecidableEq V] {G : Type*} [AddCommGroup G] (f : V → G) :
    ∑ p ∈ (univ : Finset V).offDiag, f p.1 = ∑ v, (Fintype.card V - 1) • f v := by
  have hset : (univ : Finset V).offDiag = (univ ×ˢ univ).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p; simp [mem_offDiag]
  rw [hset, sum_filter, sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter]
  dsimp only
  rw [sum_const]
  congr 1
  rw [← card_univ, ← card_erase_of_mem (mem_univ v)]
  congr 1
  ext a
  simp [ne_comm]

theorem cnt_swap [LinearOrder V] (lab : V → Fin 3) (X Y : Fin 3) :
    (((univ : Finset V).offDiag.filter fun p : V × V => p.1 < p.2).filter
        fun p => (lab p.1, lab p.2) = (X, Y)).card +
      (((univ : Finset V).offDiag.filter fun p : V × V => p.1 < p.2).filter
        fun p => (lab p.1, lab p.2) = (Y, X)).card =
      ((univ : Finset V).offDiag.filter fun p : V × V => (lab p.1, lab p.2) = (X, Y)).card := by
  rw [← card_filter_add_card_filter_not (s := (univ : Finset V).offDiag.filter
    fun p : V × V => (lab p.1, lab p.2) = (X, Y)) (fun p : V × V => p.1 < p.2)]
  congr 1
  · congr 1; ext p; simp only [mem_filter]; tauto
  · apply card_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [coe_filter, mem_filter, mem_offDiag, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap, Prod.mk.injEq] at hp ⊢
      exact ⟨⟨Ne.symm hp.1.1, hp.2.2, hp.2.1⟩, not_lt.2 hp.1.2.le⟩
    · intro p hp
      simp only [coe_filter, mem_filter, mem_offDiag, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap, Prod.mk.injEq] at hp ⊢
      exact ⟨⟨Ne.symm hp.1.1, lt_of_le_of_ne (not_lt.1 hp.2) (Ne.symm hp.1.1)⟩, hp.1.2.2,
        hp.1.2.1⟩
    · intro p _; simp
    · intro p _; simp

theorem offDiag_lab_ne [DecidableEq V] (lab : V → Fin 3) {X Y : Fin 3} (h : X ≠ Y) :
    ((univ : Finset V).offDiag.filter fun p : V × V => (lab p.1, lab p.2) = (X, Y)).card =
      csz lab X * csz lab Y := by
  rw [csz, csz, ← card_product]
  congr 1
  ext p
  simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_product, Prod.mk.injEq]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h (by rw [← h1, ← h2, e]), h1, h2⟩

theorem offDiag_lab_eq [DecidableEq V] (lab : V → Fin 3) (X : Fin 3) :
    ((univ : Finset V).offDiag.filter fun p : V × V => (lab p.1, lab p.2) = (X, X)).card =
      csz lab X * csz lab X - csz lab X := by
  rw [csz, ← offDiag_card]
  congr 1
  ext p
  simp only [mem_filter, mem_offDiag, mem_univ, true_and, Prod.mk.injEq]
  tauto

theorem pair_term {G : Type*} [AddCommGroup G] {k γ : G} (h : k + k = γ) {n m p : ℕ}
    (e : n + m = p + p) : n • k + m • k = p • γ := by
  rw [← add_nsmul, e, add_nsmul, ← nsmul_add, h]

/-- **The edge-formula sum vanishes.**  For any abelian group, class constants `κ` with
`κ(X,X) = -γ`, `κ` symmetric with `2κ(X,Y) = γ` off the diagonal, and vertex potentials of
order two, the sum of `κ(lab u, lab v) + ε u + ε v` over all pairs `u < v` is `0` when `n` is
odd, the products of class sizes are even and the admissibility identity holds. -/
theorem formula_sum_zero [LinearOrder V] {Q : Type*} [AddCommGroup Q] (κ : Fin 3 → Fin 3 → Q)
    (ε : V → Q) (γ : Q) (hε : ∀ v, ε v + ε v = 0) (hdiag : ∀ X, κ X X = -γ)
    (hsym : ∀ X Y, κ X Y = κ Y X) (hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ)
    (hn : Even (Fintype.card V - 1)) (h01 : Even (csz lab 0 * csz lab 1))
    (h02 : Even (csz lab 0 * csz lab 2)) (h12 : Even (csz lab 1 * csz lab 2))
    (hadm : (csz lab 0 : ℤ) ^ 2 + (csz lab 1 : ℤ) ^ 2 + (csz lab 2 : ℤ) ^ 2 -
      csz lab 0 * csz lab 1 - csz lab 0 * csz lab 2 - csz lab 1 * csz lab 2 =
      csz lab 0 + csz lab 1 + csz lab 2) :
    ∑ p ∈ (univ : Finset V).offDiag.filter (fun p : V × V => p.1 < p.2),
      (κ (lab p.1) (lab p.2) + ε p.1 + ε p.2) = 0 := by
  classical
  set P := (univ : Finset V).offDiag.filter (fun p : V × V => p.1 < p.2) with hP
  rw [sum_add_distrib, sum_add_distrib]
  -- the `ε` part
  have hswap : ∑ p ∈ P, ε p.2 =
      ∑ p ∈ (univ : Finset V).offDiag.filter (fun p : V × V => ¬ p.1 < p.2), ε p.1 := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [hP, coe_filter, mem_filter, mem_offDiag, mem_univ, true_and,
        Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨Ne.symm hp.1, not_lt.2 hp.2.le⟩
    · intro p hp
      simp only [hP, coe_filter, mem_filter, mem_offDiag, mem_univ, true_and,
        Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨Ne.symm hp.1, lt_of_le_of_ne (not_lt.1 hp.2) (Ne.symm hp.1)⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
  have heps : ∑ p ∈ P, ε p.1 + ∑ p ∈ P, ε p.2 = 0 := by
    rw [hswap, hP, sum_filter_add_sum_filter_not, sum_offDiag_fst]
    obtain ⟨k, hk⟩ := hn
    refine sum_eq_zero fun v _ => ?_
    rw [hk, add_nsmul, ← nsmul_add, hε, nsmul_zero]
  rw [add_assoc, heps, add_zero]
  -- the `κ` part
  rw [← sum_fiberwise' P (fun p : V × V => (lab p.1, lab p.2))
    (fun j : Fin 3 × Fin 3 => κ j.1 j.2)]
  simp only [sum_const, Fintype.sum_prod_type, Fin.sum_univ_three]
  set N : Fin 3 → Fin 3 → ℕ := fun X Y => (P.filter fun p => (lab p.1, lab p.2) = (X, Y)).card
    with hN
  have hpair : ∀ X Y : Fin 3, X ≠ Y → N X Y + N Y X = csz lab X * csz lab Y := by
    intro X Y h
    simp only [hN, hP]
    rw [cnt_swap, offDiag_lab_ne lab h]
  have hdg : ∀ X : Fin 3, N X X + N X X = csz lab X * csz lab X - csz lab X := by
    intro X
    simp only [hN, hP]
    rw [cnt_swap, offDiag_lab_eq]
  change N 0 0 • κ 0 0 + N 0 1 • κ 0 1 + N 0 2 • κ 0 2 +
      (N 1 0 • κ 1 0 + N 1 1 • κ 1 1 + N 1 2 • κ 1 2) +
      (N 2 0 • κ 2 0 + N 2 1 • κ 2 1 + N 2 2 • κ 2 2) = 0
  rw [hdiag 0, hdiag 1, hdiag 2, hsym 1 0, hsym 2 0, hsym 2 1]
  obtain ⟨p01, e01⟩ := h01
  obtain ⟨p02, e02⟩ := h02
  obtain ⟨p12, e12⟩ := h12
  have t01 := pair_term (hoff 0 1 (by decide)) ((hpair 0 1 (by decide)).trans e01)
  have t02 := pair_term (hoff 0 2 (by decide)) ((hpair 0 2 (by decide)).trans e02)
  have t12 := pair_term (hoff 1 2 (by decide)) ((hpair 1 2 (by decide)).trans e12)
  have hd : p01 + p02 + p12 = N 0 0 + N 1 1 + N 2 2 := by
    have d0 := hdg 0
    have d1 := hdg 1
    have d2 := hdg 2
    have l0 : csz lab 0 ≤ csz lab 0 * csz lab 0 := Nat.le_mul_self _
    have l1 : csz lab 1 ≤ csz lab 1 * csz lab 1 := Nat.le_mul_self _
    have l2 : csz lab 2 ≤ csz lab 2 * csz lab 2 := Nat.le_mul_self _
    zify [l0, l1, l2] at d0 d1 d2
    zify at e01 e02 e12 ⊢
    have h2 : 2 * ((p01 : ℤ) + p02 + p12) = 2 * ((N 0 0 : ℤ) + N 1 1 + N 2 2) := by
      linear_combination -e01 - e02 - e12 - d0 - d1 - d2 - hadm
    omega
  calc _ = (N 0 1 • κ 0 1 + N 1 0 • κ 0 1) + (N 0 2 • κ 0 2 + N 2 0 • κ 0 2) +
        (N 1 2 • κ 1 2 + N 2 1 • κ 1 2) - (N 0 0 • γ + N 1 1 • γ + N 2 2 • γ) := by
          simp only [smul_neg]; abel
    _ = 0 := by
      rw [t01, t02, t12, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, hd, sub_self]

/-- **H2, general form**: for the complete graph labelled by three classes with at least three
points each, `n` odd, all products of class sizes even and the admissibility identity, the
indicator of all edges lies in the lattice of bicoloured triangles. -/
theorem physical_of [LinearOrder V] (hbig : Big lab) (ho : ∀ k, lab (o k) = k)
    (hn : Even (Fintype.card V - 1)) (h01 : Even (csz lab 0 * csz lab 1))
    (h02 : Even (csz lab 0 * csz lab 2)) (h12 : Even (csz lab 1 * csz lab 2))
    (hadm : (csz lab 0 : ℤ) ^ 2 + (csz lab 1 : ℤ) ^ 2 + (csz lab 2 : ℤ) ^ 2 -
      csz lab 0 * csz lab 1 - csz lab 0 * csz lab 2 - csz lab 1 * csz lab 2 =
      csz lab 0 + csz lab 1 + csz lab 2) :
    IsPhysical (cHost lab) cdrF (edges (cHost lab)) := by
  unfold IsPhysical
  rw [← Submodule.Quotient.mk_eq_zero, ind_edges_eq_sum, ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  change ∑ e ∈ edges (cHost lab), gq lab e = 0
  rw [edges_cHost, sum_sym2_filter_not_isDiag]
  rw [sum_congr rfl (fun p hp => formula (o := o) hbig ho
    (mem_offDiag.1 (mem_filter.1 hp).1).2.2)]
  set γ := beta lab o 0 1 + beta lab o 0 1 with hγ
  refine formula_sum_zero (kap lab o) (eps lab o) γ (two_eps hbig ho) (fun X => ?_)
    (fun X Y => ?_) (fun X Y h => ?_) hn h01 h02 h12 hadm
  · unfold kap; rw [if_pos rfl]
    obtain rfl | rfl | rfl : X = 0 ∨ X = 1 ∨ X = 2 := by fin_cases X <;> simp
    · rfl
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, two_beta hbig ho (by decide)]
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, two_beta hbig ho (by decide)]
  · unfold kap
    by_cases h : X = Y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), beta_symm]
  · unfold kap; rw [if_neg h]; exact two_beta hbig ho h

end Lattice

/-! ### The CDR host -/

theorem adm_even_mul {a b c : ℕ} (h : AdmissibleProfile a b c) :
    Even (a * b) ∧ Even (a * c) ∧ Even (b * c) := by
  obtain ⟨ha, hb, hc, hmod, hid, -⟩ := h
  have hodd : ¬ Even (a + b + c) := by rw [Nat.even_iff]; omega
  have e : a * b + a * c + b * c = a * (a - 1) + b * (b - 1) + c * (c - 1) := by
    zify [Nat.one_le_iff_ne_zero.2 ha.ne', Nat.one_le_iff_ne_zero.2 hb.ne',
      Nat.one_le_iff_ne_zero.2 hc.ne']
    linear_combination (-1 : ℤ) * hid
  have hev : Even (a * b + a * c + b * c) := by
    rw [e]
    exact ((Nat.even_mul_pred_self a).add (Nat.even_mul_pred_self b)).add
      (Nat.even_mul_pred_self c)
  simp only [Nat.even_add, Nat.even_mul] at hodd hev ⊢
  tauto

theorem big_of_three {V : Type*} [Fintype V] {lab : V → Fin 3} (h : ∀ k, 3 ≤ csz lab k) :
    Big lab := by
  classical
  intro k u v
  set S := univ.filter fun w : V => lab w = k with hS
  have h1 := pred_card_le_card_erase (s := S.erase u) (a := v)
  have h2 := pred_card_le_card_erase (s := S) (a := u)
  have h3 : 3 ≤ S.card := h k
  obtain ⟨w, hw⟩ : ((S.erase u).erase v).Nonempty := by
    rw [← card_pos]; omega
  simp only [mem_erase, hS, mem_filter, mem_univ, true_and] at hw
  exact ⟨w, hw.2.2, hw.2.1, hw.1⟩

theorem csz_col3 (a b c : ℕ) (k : Fin 3) : csz (col3 a b c) k = ![a, b, c] k := card_class a b c k

/-- **H2** for the CDR host: the indicator of all edges is physical, for every admissible
profile whose classes have at least three points. -/
theorem cdr_H2_of_three {a b c : ℕ} (h : AdmissibleProfile a b c) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hc : 3 ≤ c) : IsPhysical (cdrHost a b c) cdrF (edges (cdrHost a b c)) := by
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  have hbig : Big (col3 a b c) := big_of_three fun k => by
    fin_cases k
    · simpa [hs0] using ha
    · simpa [hs1] using hb
    · simpa [hs2] using hc
  have hex : ∀ k : Fin 3, ∃ v, col3 a b c v = k := fun k => by
    obtain ⟨w, hw, -⟩ := hbig k ⟨0, by omega⟩ ⟨0, by omega⟩
    exact ⟨w, hw⟩
  choose o ho using hex
  obtain ⟨h01, h02, h12⟩ := adm_even_mul h
  have hn : Even (Fintype.card (Fin (a + b + c)) - 1) := by
    rw [Fintype.card_fin, Nat.even_iff]; have := h.2.2.2.1; omega
  have hid := h.2.2.2.2.1
  exact physical_of (lab := col3 a b c) hbig ho hn (by rw [hs0, hs1]; exact h01)
    (by rw [hs0, hs2]; exact h02) (by rw [hs1, hs2]; exact h12)
    (by rw [hs0, hs1, hs2]; exact hid)

/-- **H2** for the CDR host, `n ≥ 400`. -/
theorem cdr_H2 {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    IsPhysical (cdrHost a b c) cdrF (edges (cdrHost a b c)) := by
  obtain ⟨ha, hb, hc⟩ := class_lower_all h hn
  exact cdr_H2_of_three h (by omega) (by omega) (by omega)

end CDRBicolour.Absorption
