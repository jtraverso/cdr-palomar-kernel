/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Hinge
public import CDRBicolour.Absorption.Lattice

/-!
# k-bicolourings: hypothesis H2 (the all-edges indicator is physical)

The direct lattice argument of `CDRBicolour.Absorption.Lattice`, for `k` classes. In the quotient
`Q = ℤ^{Sym2 V} / Λ` write `g e` for the class of the edge `e`.

* A bicoloured triangle gives `g(xy) + g(xz) + g(yz) = 0`; with three points in a class `X` and
  `w, w' ∉ X`, `g(xw) - g(xw')` has order two and does not depend on `x` (`tri_D`).
* Fix base points `o X` and a class `nx X ≠ X` for every `X`; with
  `ε(v) = g(v, o(nx(lab v))) - g(o(lab v), o(nx(lab v)))` we get `2ε = 0` and
  `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)`.
* `2 g(o X, o Y)` depends on neither `X` nor `Y`: it does not depend on `Y` (`beta_rel`) and is
  symmetric, so it is a constant `γ`; `κ(X, X) = -γ` and `2 κ(X, Y) = γ` for `X ≠ Y`.
* Summing over all edges: the `ε` part vanishes (`n` odd) and the `κ` part is
  `(Σ_{X<Y} |X||Y|/2 - Σ_X C(|X|, 2)) γ`, which vanishes by the pair identity
  `Σ_{X<Y} |X||Y| = Σ_X |X|(|X|-1)` (equivalent to `Σ_X C(|X|,2) = C(n,2)/3`), all the
  products `|X||Y|` being even.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

section Lattice

variable {k : ℕ} {V : Type*} [Fintype V]

/-- The quotient of `ℤ^{Sym2 V}` by the physical lattice. -/
abbrev LQ (lab : V → Fin k) := (Sym2 V → ℤ) ⧸ lattice (kHost lab) (bicF k)

/-- The class of a single edge. -/
def gq (lab : V → Fin k) (e : Sym2 V) : LQ lab :=
  Submodule.Quotient.mk (ind ({e} : Finset (Sym2 V)))

/-- Every class has a point avoiding any two given points. -/
def Big (lab : V → Fin k) : Prop := ∀ (X : Fin k) (u v : V), ∃ w, lab w = X ∧ w ≠ u ∧ w ≠ v

/-- Triangle relation in the quotient. -/
theorem tri_rel (lab : V → Fin k) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hF : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k) :
    gq lab s(x, y) + gq lab s(x, z) + gq lab s(y, z) = 0 := by
  classical
  have hmem : ind (triEdges ({x, y, z} : Finset V)) ∈
      lattice (kHost lab) (bicF k) :=
    Submodule.subset_span ⟨{x, y, z}, isAllowed_triple lab hxy hxz hyz hF, rfl⟩
  rw [CDRBicolour.Absorption.ind_triple hxy hxz hyz] at hmem
  simp only [gq, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

theorem eq_neg_sub_of_add {G : Type*} [AddCommGroup G] {a b c : G} (h : a + b + c = 0) :
    a = -b - c := by
  rw [← sub_eq_zero, ← h]; abel

/-- A monochromatic edge in terms of two bichromatic ones. -/
theorem mono_rel (lab : V → Fin k) {x x' w : V} (hxx : x ≠ x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) :
    gq lab s(x, x') = -gq lab s(x, w) - gq lab s(x', w) := by
  have hxw : x ≠ w := fun h => hw (by rw [h])
  have hx'w : x' ≠ w := fun h => hw (by rw [← h, hl])
  exact eq_neg_sub_of_add (tri_rel lab hxx hxw hx'w
    (mem_bicF.2 (Or.inl ⟨hl.symm, by rw [hl]; exact Ne.symm hw⟩)))

theorem sq_rel (lab : V → Fin k) {x x' w w' : V} (hxx : x ≠ x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x) :
    (gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x', w) - gq lab s(x', w')) = 0 := by
  have h1 := mono_rel lab hxx hl hw
  have h2 := mono_rel lab hxx hl hw'
  rw [h1] at h2
  rw [← neg_eq_zero, ← sub_eq_zero.2 h2]; abel

theorem tri_D (lab : V → Fin k) {x x' x'' w w' : V} (h1 : x ≠ x') (h2 : x ≠ x'')
    (h3 : x' ≠ x'') (l1 : lab x' = lab x) (l2 : lab x'' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) :
    (gq lab s(x, w) - gq lab s(x, w')) + (gq lab s(x, w) - gq lab s(x, w')) = 0 ∧
    gq lab s(x', w) - gq lab s(x', w') = gq lab s(x, w) - gq lab s(x, w') := by
  have A := sq_rel lab h1 l1 hw hw'
  have B := sq_rel lab h2 l2 hw hw'
  have C := sq_rel lab (w := w) (w' := w') h3 (l2.trans l1.symm) (by rw [l1]; exact hw)
    (by rw [l1]; exact hw')
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

/-! ### Base points and the vertex potential -/

/-- The vertex potential. -/
def eps (lab : V → Fin k) (o : Fin k → V) (nx : Fin k → Fin k) (v : V) : LQ lab :=
  gq lab s(v, o (nx (lab v))) - gq lab s(o (lab v), o (nx (lab v)))

/-- The class of the edge between two base points. -/
def beta (lab : V → Fin k) (o : Fin k → V) (X Y : Fin k) : LQ lab := gq lab s(o X, o Y)

/-- The class constant. -/
def kap (lab : V → Fin k) (o : Fin k → V) (nx : Fin k → Fin k) (X Y : Fin k) : LQ lab :=
  if X = Y then -(beta lab o X (nx X) + beta lab o X (nx X)) else beta lab o X Y

variable {lab : V → Fin k} {o : Fin k → V} {nx : Fin k → Fin k}

theorem eps_base (ho : ∀ X, lab (o X) = X) (X : Fin k) : eps lab o nx (o X) = 0 := by
  simp only [eps, ho X, sub_self]

theorem eps_spec (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X) {v w : V}
    (hw : lab w ≠ lab v) :
    gq lab s(v, w) = gq lab s(o (lab v), w) + eps lab o nx v := by
  by_cases hv : v = o (lab v)
  · have : eps lab o nx v = 0 := by
      unfold eps; rw [← hv, sub_self]
    rw [this, add_zero, ← hv]
  · obtain ⟨x'', hl'', h1, h2⟩ := hbig (lab v) v (o (lab v))
    have hw' : lab (o (nx (lab v))) ≠ lab v := by rw [ho]; exact hnx _
    have E := (tri_D lab hv (Ne.symm h1) (Ne.symm h2) (ho _) hl'' hw hw').2
    rw [← sub_eq_zero] at E
    unfold eps
    rw [← sub_eq_zero, ← neg_eq_zero, ← E]; abel

theorem two_eps (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X) (v : V) :
    eps lab o nx v + eps lab o nx v = 0 := by
  obtain ⟨y1, hy1, h11, -⟩ := hbig (nx (lab v)) (o (nx (lab v))) (o (nx (lab v)))
  obtain ⟨y2, hy2, h21, h22⟩ := hbig (nx (lab v)) (o (nx (lab v))) y1
  have lw : lab (o (nx (lab v))) = nx (lab v) := ho _
  have hv : lab v ≠ lab (o (nx (lab v))) := by rw [lw]; exact (hnx _).symm
  have ho' : lab (o (lab v)) ≠ lab (o (nx (lab v))) := by
    rw [lw, ho]; exact (hnx _).symm
  have := (tri_D lab (x := o (nx (lab v))) (x' := y1) (x'' := y2) (Ne.symm h11) (Ne.symm h21)
    (Ne.symm h22) (hy1.trans lw.symm) (hy2.trans lw.symm) hv ho').1
  unfold eps
  rw [Sym2.eq_swap (a := v), Sym2.eq_swap (a := o (lab v))]
  exact this

theorem beta_symm (X Y : Fin k) : beta lab o X Y = beta lab o Y X := by
  unfold beta; rw [Sym2.eq_swap]

theorem bichrom_formula (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X)
    {u v : V} (huv : lab u ≠ lab v) :
    gq lab s(u, v) = beta lab o (lab u) (lab v) + eps lab o nx u + eps lab o nx v := by
  rw [eps_spec hbig ho hnx (Ne.symm huv), Sym2.eq_swap (a := o (lab u)),
    eps_spec hbig ho hnx (v := v) (w := o (lab u)) (by rw [ho]; exact huv)]
  unfold beta
  rw [Sym2.eq_swap (a := o (lab v))]; abel

theorem mono_formula (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X)
    {u v : V} (huv : u ≠ v) (hl : lab v = lab u) :
    gq lab s(u, v) = -(beta lab o (lab u) (nx (lab u)) + beta lab o (lab u) (nx (lab u))) +
      eps lab o nx u + eps lab o nx v := by
  have hw : lab (o (nx (lab u))) ≠ lab u := by rw [ho]; exact hnx _
  rw [mono_rel lab huv hl hw, bichrom_formula hbig ho hnx (Ne.symm hw),
    bichrom_formula hbig ho hnx (u := v) (v := o (nx (lab u))) (by rw [hl]; exact Ne.symm hw)]
  simp only [ho, eps_base ho, add_zero]
  rw [hl]
  have h1 := two_eps hbig ho hnx u
  have h2 := two_eps hbig ho hnx v
  rw [← sub_eq_zero]
  calc _ = -((eps lab o nx u + eps lab o nx u) + (eps lab o nx v + eps lab o nx v)) := by abel
    _ = 0 := by rw [h1, h2]; simp

/-- **Edge formula**: `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)`. -/
theorem formula (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X) {u v : V}
    (huv : u ≠ v) :
    gq lab s(u, v) = kap lab o nx (lab u) (lab v) + eps lab o nx u + eps lab o nx v := by
  unfold kap
  by_cases hl : lab u = lab v
  · rw [if_pos hl, mono_formula hbig ho hnx huv hl.symm]
  · rw [if_neg hl, bichrom_formula hbig ho hnx hl]

theorem beta_rel (hbig : Big lab) (ho : ∀ X, lab (o X) = X) {X Y Z : Fin k} (hXY : X ≠ Y)
    (hXZ : X ≠ Z) :
    beta lab o X Y + beta lab o X Y = beta lab o X Z + beta lab o X Z := by
  obtain ⟨x1, hx1, h11, -⟩ := hbig X (o X) (o X)
  obtain ⟨x2, hx2, h21, h22⟩ := hbig X (o X) x1
  have := (tri_D lab (x := o X) (x' := x1) (x'' := x2) (w := o Y) (w' := o Z) (Ne.symm h11)
    (Ne.symm h21) (Ne.symm h22) (by rw [hx1, ho]) (by rw [hx2, ho])
    (by rw [ho, ho]; exact Ne.symm hXY) (by rw [ho, ho]; exact Ne.symm hXZ)).1
  unfold beta
  rw [← sub_eq_zero, ← this]; abel

/-- `2 β(X, Y)` is the same for all `X ≠ Y`. -/
theorem two_beta (hbig : Big lab) (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X)
    (X₀ : Fin k) {X Y : Fin k} (h : X ≠ Y) :
    beta lab o X Y + beta lab o X Y = beta lab o X₀ (nx X₀) + beta lab o X₀ (nx X₀) := by
  -- `f X = 2 β(X, nx X)`; `2 β(X, Y) = f X` and, by symmetry, `= f Y`
  have hf : ∀ X Y, X ≠ Y →
      beta lab o X Y + beta lab o X Y = beta lab o X (nx X) + beta lab o X (nx X) :=
    fun X Y h => beta_rel hbig ho h (hnx X).symm
  have hsym : ∀ X Y, X ≠ Y →
      beta lab o X (nx X) + beta lab o X (nx X) = beta lab o Y (nx Y) + beta lab o Y (nx Y) := by
    intro X Y h
    rw [← hf X Y h, ← hf Y X (Ne.symm h), beta_symm X Y]
  rw [hf X Y h]
  by_cases hX : X = X₀
  · rw [hX]
  · exact hsym X X₀ hX

/-! ### Summation -/

theorem ind_edges_eq_sum (lab : V → Fin k) :
    ind (edges (kHost lab)) =
      ∑ e ∈ edges (kHost lab), ind ({e} : Finset (Sym2 V)) := by
  classical
  funext e'
  rw [Finset.sum_apply]
  by_cases h : e' ∈ edges (kHost lab)
  · rw [sum_eq_single_of_mem e' h]
    · simp [ind, h]
    · intro b _ hb; simp [ind, Ne.symm hb]
  · rw [sum_eq_zero]
    · simp [ind, h]
    · intro b hb
      have : e' ≠ b := fun h' => h (h' ▸ hb)
      simp [ind, this]

theorem edges_kHost [DecidableEq V] (lab : V → Fin k) :
    edges (kHost lab) = (univ : Finset V).sym2.filter (fun e => ¬ e.IsDiag) := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [edges, kHost]

theorem cnt_swap [LinearOrder V] (lab : V → Fin k) (X Y : Fin k) :
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

theorem offDiag_lab_ne [DecidableEq V] (lab : V → Fin k) {X Y : Fin k} (h : X ≠ Y) :
    ((univ : Finset V).offDiag.filter fun p : V × V => (lab p.1, lab p.2) = (X, Y)).card =
      ksz lab X * ksz lab Y := by
  rw [ksz, ksz, ← card_product]
  congr 1
  ext p
  simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_product, Prod.mk.injEq]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h (by rw [← h1, ← h2, e]), h1, h2⟩

theorem offDiag_lab_eq [DecidableEq V] (lab : V → Fin k) (X : Fin k) :
    ((univ : Finset V).offDiag.filter fun p : V × V => (lab p.1, lab p.2) = (X, X)).card =
      ksz lab X * ksz lab X - ksz lab X := by
  rw [ksz, ← offDiag_card]
  congr 1
  ext p
  simp only [mem_filter, mem_offDiag, mem_univ, true_and, Prod.mk.injEq]
  tauto

/-- Splitting a double sum over `Fin k` into the diagonal and the pairs `X < Y`. -/
theorem sum_pairs {Q : Type*} [AddCommMonoid Q] (f : Fin k → Fin k → Q) :
    ∑ j : Fin k × Fin k, f j.1 j.2 =
      ∑ X, f X X + ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), (f j.1 j.2 + f j.2 j.1) := by
  rw [sum_add_distrib]
  rw [← sum_filter_add_sum_filter_not (univ : Finset (Fin k × Fin k)) (fun j => j.1 < j.2)]
  rw [← sum_filter_add_sum_filter_not (univ.filter fun j : Fin k × Fin k => ¬ j.1 < j.2)
    (fun j => j.1 = j.2)]
  have hdiag : ∑ j ∈ (univ.filter fun j : Fin k × Fin k => ¬ j.1 < j.2).filter
      (fun j => j.1 = j.2), f j.1 j.2 = ∑ X, f X X := by
    apply sum_nbij' (fun j => j.1) (fun X => (X, X))
    · intro _ _; simp
    · intro X _; simp
    · intro j hj
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj
      exact Prod.ext rfl hj.2
    · intro X _; rfl
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [hj.2]
  have hgt : ∑ j ∈ (univ.filter fun j : Fin k × Fin k => ¬ j.1 < j.2).filter
      (fun j => ¬ j.1 = j.2), f j.1 j.2 =
      ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), f j.2 j.1 := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro j hj
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap] at hj ⊢
      exact lt_of_le_of_ne (not_lt.1 hj.1) (Ne.symm hj.2)
    · intro j hj
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap] at hj ⊢
      exact ⟨not_lt.2 hj.le, Ne.symm (ne_of_lt hj)⟩
    · intro j _; simp
    · intro j _; simp
    · intro j _; rfl
  rw [hdiag, hgt]
  abel

theorem pair_term {G : Type*} [AddCommGroup G] {κ γ : G} (h : κ + κ = γ) {n m p : ℕ}
    (e : n + m = p + p) : n • κ + m • κ = p • γ := by
  rw [← add_nsmul, e, add_nsmul, ← nsmul_add, h]

/-- **The edge-formula sum vanishes**, for `k` classes. -/
theorem formula_sum_zero [LinearOrder V] {Q : Type*} [AddCommGroup Q] (κ : Fin k → Fin k → Q)
    (ε : V → Q) (γ : Q) (hε : ∀ v, ε v + ε v = 0) (hdiag : ∀ X, κ X X = -γ)
    (hsym : ∀ X Y, κ X Y = κ Y X) (hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ)
    (hn : Even (Fintype.card V - 1))
    (heven : ∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y))
    (hpair : ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), ksz lab j.1 * ksz lab j.2 =
      ∑ X, ksz lab X * (ksz lab X - 1)) :
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
    rw [hswap, hP, sum_filter_add_sum_filter_not, CDRBicolour.Absorption.sum_offDiag_fst]
    obtain ⟨m, hm⟩ := hn
    refine sum_eq_zero fun v _ => ?_
    rw [hm, add_nsmul, ← nsmul_add, hε, nsmul_zero]
  rw [add_assoc, heps, add_zero]
  -- the `κ` part
  rw [← sum_fiberwise' P (fun p : V × V => (lab p.1, lab p.2))
    (fun j : Fin k × Fin k => κ j.1 j.2)]
  simp only [sum_const]
  set N : Fin k → Fin k → ℕ := fun X Y => (P.filter fun p => (lab p.1, lab p.2) = (X, Y)).card
    with hN
  change ∑ j : Fin k × Fin k, N j.1 j.2 • κ j.1 j.2 = 0
  have hpr : ∀ X Y : Fin k, X ≠ Y → N X Y + N Y X = ksz lab X * ksz lab Y := by
    intro X Y h
    simp only [hN, hP]
    rw [cnt_swap, offDiag_lab_ne lab h]
  have hdg : ∀ X : Fin k, N X X + N X X = ksz lab X * ksz lab X - ksz lab X := by
    intro X
    simp only [hN, hP]
    rw [cnt_swap, offDiag_lab_eq]
  rw [sum_pairs (fun X Y => N X Y • κ X Y)]
  -- off-diagonal pairs
  have hoffsum : ∀ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2),
      N j.1 j.2 • κ j.1 j.2 + N j.2 j.1 • κ j.2 j.1 = (ksz lab j.1 * ksz lab j.2 / 2) • γ := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have hne : j.1 ≠ j.2 := ne_of_lt hj
    rw [hsym j.2 j.1]
    obtain ⟨q, hq⟩ := heven j.1 j.2 hne
    have hdiv : ksz lab j.1 * ksz lab j.2 / 2 = q := by omega
    rw [hdiv]
    exact pair_term (hoff j.1 j.2 hne) ((hpr j.1 j.2 hne).trans hq)
  -- `Σ_{X<Y} |X||Y|/2 = Σ_X N X X`
  have hcount : ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2),
      ksz lab j.1 * ksz lab j.2 / 2 = ∑ X, N X X := by
    have h2 : ∀ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2),
        2 * (ksz lab j.1 * ksz lab j.2 / 2) = ksz lab j.1 * ksz lab j.2 := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      obtain ⟨q, hq⟩ := heven j.1 j.2 (ne_of_lt hj)
      omega
    have h3 : ∀ X, 2 * N X X = ksz lab X * (ksz lab X - 1) := by
      intro X
      have := hdg X
      rw [Nat.mul_sub, mul_one]
      omega
    have e1 : 2 * ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2),
        ksz lab j.1 * ksz lab j.2 / 2 = 2 * ∑ X, N X X := by
      rw [mul_sum, mul_sum, sum_congr rfl h2, hpair]
      exact sum_congr rfl fun X _ => (h3 X).symm
    omega
  rw [sum_congr rfl hoffsum]
  simp only [hdiag, smul_neg, sum_neg_distrib, ← sum_smul]
  rw [hcount]
  abel

/-- **H2, general form**: for the complete graph labelled by `k` classes with at least three
points each, `n` odd, all products of class sizes even and the pair identity, the indicator of
all edges lies in the lattice of bicoloured triangles. -/
theorem physical_of [LinearOrder V] (hbig : Big lab) (ho : ∀ X, lab (o X) = X)
    (hnx : ∀ X, nx X ≠ X) (X₀ : Fin k)
    (hn : Even (Fintype.card V - 1))
    (heven : ∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y))
    (hpair : ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), ksz lab j.1 * ksz lab j.2 =
      ∑ X, ksz lab X * (ksz lab X - 1)) :
    IsPhysical (kHost lab) (bicF k) (edges (kHost lab)) := by
  classical
  unfold IsPhysical
  rw [← Submodule.Quotient.mk_eq_zero, ind_edges_eq_sum, ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  change ∑ e ∈ edges (kHost lab), gq lab e = 0
  rw [edges_kHost, sum_sym2_filter_not_isDiag]
  rw [sum_congr rfl (fun p hp => formula (o := o) (nx := nx) hbig ho hnx
    (mem_offDiag.1 (mem_filter.1 hp).1).2.2)]
  set γ := beta lab o X₀ (nx X₀) + beta lab o X₀ (nx X₀) with hγ
  refine formula_sum_zero (kap lab o nx) (eps lab o nx) γ (two_eps hbig ho hnx) (fun X => ?_)
    (fun X Y => ?_) (fun X Y h => ?_) hn heven hpair
  · unfold kap; rw [if_pos rfl, two_beta hbig ho hnx X₀ (hnx X).symm]
  · unfold kap
    by_cases h : X = Y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), beta_symm]
  · unfold kap; rw [if_neg h]; exact two_beta hbig ho hnx X₀ h

end Lattice

end CDRBicolour.KBicolor
