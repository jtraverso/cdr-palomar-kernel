/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Lattice

/-!
# H2 for residual hosts (backlog item 2a)

Let `P` be a packing of bicoloured triangles of the complete graph labelled by three classes,
`L` its set of edges and `G = K_n - L`.  The lattice of `G` is spanned only by the bicoloured
triangles contained in `G`, so H2 for `G` does not follow from H2 for `K_n`; we redo the
potential argument inside `G`.

The density hypothesis `BigR`: for every class and any four points there is a point of that
class adjacent in `G` to all four.  Under `BigR` every relation of the complete case still
holds (the auxiliary points are chosen adjacent to everything in sight), so every edge `uv` of
`G` satisfies `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)` (`formulaR`).  Summing over `E(G)` =
`E(K_n) \ L`: the sum over `E(K_n)` of the formula vanishes (`formula_sum_zero`), and the sum
over `L` splits into the triangles of `P`, each contributing `κ`-sum `0` (bicoloured type) plus
`2(ε x + ε y + ε z) = 0`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Residual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete graph minus a set `L` of edges. -/
def rG (L : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∉ L}

theorem rG_adj {L : Finset (Sym2 V)} {u v : V} : (rG L).Adj u v ↔ s(u, v) ∉ L ∧ u ≠ v := by
  simp [rG]

/-- The residual host. -/
abbrev rHost (lab : V → Fin 3) (L : Finset (Sym2 V)) : Host V (Fin 3) := ⟨rG L, lab⟩

/-- The quotient by the residual lattice. -/
abbrev RQ (lab : V → Fin 3) (L : Finset (Sym2 V)) := (Sym2 V → ℤ) ⧸ lattice (rHost lab L) cdrF

/-- The class of an edge in the residual quotient. -/
def rg (lab : V → Fin 3) (L : Finset (Sym2 V)) (e : Sym2 V) : RQ lab L :=
  Submodule.Quotient.mk (ind ({e} : Finset (Sym2 V)))

/-- Density: in every class there is a point adjacent in `G` to any four given points. -/
def BigR (lab : V → Fin 3) (L : Finset (Sym2 V)) : Prop :=
  ∀ (k : Fin 3) (p q r s : V), ∃ w, lab w = k ∧ (rG L).Adj w p ∧ (rG L).Adj w q ∧
    (rG L).Adj w r ∧ (rG L).Adj w s

variable {lab : V → Fin 3} {L : Finset (Sym2 V)}

/-- The class of the edge between two base points. -/
def betaR (o : Fin 3 → V) (X Y : Fin 3) : RQ lab L := rg lab L s(o X, o Y)

/-- The class constant. -/
def kapR (o : Fin 3 → V) (X Y : Fin 3) : RQ lab L :=
  if X = Y then -(betaR (L := L) (lab := lab) o X (X + 1) + betaR (L := L) (lab := lab) o X (X + 1))
  else betaR (L := L) (lab := lab) o X Y


theorem betaR_symm (o : Fin 3 → V) (X Y : Fin 3) :
    betaR (L := L) (lab := lab) o X Y = betaR (L := L) (lab := lab) o Y X := by
  unfold betaR; rw [Sym2.eq_swap]

theorem isAllowed_tripleR {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF) :
    IsAllowed (rHost lab L) cdrF {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy.ne, hxz.ne, hyz.ne, rfl⟩, fun u hu v hv huv => ?_, ?_⟩
  · simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> first | exact absurd rfl huv | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
  · show ({x, y, z} : Finset V).val.map lab ∈ cdrF
    rw [val_map_triple lab hxy.ne hxz.ne.symm hyz.ne.symm]; exact hF

theorem tri_relR {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF) :
    rg lab L s(x, y) + rg lab L s(x, z) + rg lab L s(y, z) = 0 := by
  classical
  have hmem : ind (triEdges ({x, y, z} : Finset V)) ∈ lattice (rHost lab L) cdrF :=
    Submodule.subset_span ⟨{x, y, z}, isAllowed_tripleR hxy hxz hyz hF, rfl⟩
  rw [ind_triple hxy.ne hxz.ne hyz.ne] at hmem
  simp only [rg, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

theorem mono_relR {x x' w : V} (hxx : (rG L).Adj x x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hxw : (rG L).Adj x w) (hx'w : (rG L).Adj x' w) :
    rg lab L s(x, x') = -rg lab L s(x, w) - rg lab L s(x', w) :=
  eq_neg_sub_of_add (tri_relR hxx hxw hx'w
    (cdrF_of (Or.inl ⟨hl.symm, by rw [hl]; exact Ne.symm hw⟩)))

theorem sq_relR {x x' w w' : V} (hxx : (rG L).Adj x x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x) (a1 : (rG L).Adj x w) (a2 : (rG L).Adj x' w)
    (a3 : (rG L).Adj x w') (a4 : (rG L).Adj x' w') :
    (rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x', w) - rg lab L s(x', w')) = 0 := by
  have h1 := mono_relR hxx hl hw a1 a2
  have h2 := mono_relR hxx hl hw' a3 a4
  rw [h1] at h2
  rw [← neg_eq_zero, ← sub_eq_zero.2 h2]; abel

/-- Three mutually adjacent points of a class, all adjacent to `w, w'`. -/
theorem tri_DR {x x' x'' w w' : V} (h1 : (rG L).Adj x x') (h2 : (rG L).Adj x x'')
    (h3 : (rG L).Adj x' x'') (l1 : lab x' = lab x) (l2 : lab x'' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) (a : (rG L).Adj x w) (a' : (rG L).Adj x w')
    (b : (rG L).Adj x' w) (b' : (rG L).Adj x' w') (c : (rG L).Adj x'' w)
    (c' : (rG L).Adj x'' w') :
    (rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x, w) - rg lab L s(x, w')) = 0 ∧
    rg lab L s(x', w) - rg lab L s(x', w') = rg lab L s(x, w) - rg lab L s(x, w') := by
  have A := sq_relR h1 l1 hw hw' a b a' b'
  have B := sq_relR h2 l2 hw hw' a c a' c'
  have C := sq_relR (w := w) (w' := w') h3 (l2.trans l1.symm) (by rw [l1]; exact hw)
    (by rw [l1]; exact hw') b c b' c'
  have hD : (rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x, w) - rg lab L s(x, w')) = 0 := by
    calc _ = ((rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x', w) - rg lab L s(x', w'))) +
          ((rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x'', w) - rg lab L s(x'', w'))) -
          ((rg lab L s(x', w) - rg lab L s(x', w')) + (rg lab L s(x'', w) - rg lab L s(x'', w'))) := by
            abel
      _ = 0 := by rw [A, B, C]; simp
  refine ⟨hD, ?_⟩
  rw [← sub_eq_zero]
  calc _ = ((rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x', w) - rg lab L s(x', w'))) -
        ((rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x, w) - rg lab L s(x, w'))) := by abel
    _ = 0 := by rw [A, hD, sub_zero]

variable (hbig : BigR lab L)
include hbig

/-- `g(xw) - g(xw')` has order two. -/
theorem two_diffR {x w w' : V} (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x)
    (a : (rG L).Adj x w) (a' : (rG L).Adj x w') :
    (rg lab L s(x, w) - rg lab L s(x, w')) + (rg lab L s(x, w) - rg lab L s(x, w')) = 0 := by
  obtain ⟨x', l1, b1, b2, b3, -⟩ := hbig (lab x) x w w' w
  obtain ⟨x'', l2, c1, c2, c3, c4⟩ := hbig (lab x) x x' w w'
  exact (tri_DR b1.symm c1.symm c2.symm l1 l2 hw hw' a a' b2 b3 c3 c4).1

/-- `g(xw) - g(xw')` does not depend on `x` in its class. -/
theorem diff_indepR {x x' w w' : V} (hl : lab x' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) (a : (rG L).Adj x w) (a' : (rG L).Adj x w') (b : (rG L).Adj x' w)
    (b' : (rG L).Adj x' w') :
    rg lab L s(x', w) - rg lab L s(x', w') = rg lab L s(x, w) - rg lab L s(x, w') := by
  obtain ⟨y, ly, y1, y2, y3, y4⟩ := hbig (lab x) x x' w w'
  obtain ⟨z, lz, z1, z2, z3, z4⟩ := hbig (lab x) x y w w'
  obtain ⟨z', lz', z1', z2', z3', z4'⟩ := hbig (lab x) x' y w w'
  have E1 := (tri_DR y1.symm z1.symm z2.symm ly lz hw hw' a a' y3 y4 z3 z4).2
  have E2 := (tri_DR (x := x') y2.symm z1'.symm z2'.symm (ly.trans hl.symm) (lz'.trans hl.symm)
    (by rw [hl]; exact hw) (by rw [hl]; exact hw') b b' y3 y4 z3' z4').2
  rw [← E1, E2]

/-- The vertex potential (with base points `o`). -/
def epsR (o : Fin 3 → V) (v : V) : RQ lab L :=
  rg lab L s(v, Classical.choose (hbig (lab v + 1) v (o (lab v)) v v)) -
    rg lab L s(o (lab v), Classical.choose (hbig (lab v + 1) v (o (lab v)) v v))

variable {o : Fin 3 → V} (ho : ∀ k, lab (o k) = k)
  (hoadj : ∀ j k, j ≠ k → (rG L).Adj (o j) (o k))
include ho

theorem epsR_eq {v w : V} (hw : lab w ≠ lab v) (a : (rG L).Adj v w)
    (a' : (rG L).Adj (o (lab v)) w) :
    epsR hbig o v = rg lab L s(v, w) - rg lab L s(o (lab v), w) := by
  have hs := Classical.choose_spec (hbig (lab v + 1) v (o (lab v)) v v)
  set w0 := Classical.choose (hbig (lab v + 1) v (o (lab v)) v v)
  obtain ⟨l0, b1, b2, -, -⟩ := hs
  have hw0 : lab w0 ≠ lab v := by rw [l0]; exact fin3_succ_ne _
  have E := diff_indepR hbig (x := v) (x' := o (lab v)) (w := w0) (w' := w) (ho _) hw0 hw
    b1.symm a b2.symm a'
  unfold epsR
  rw [← sub_eq_zero] at E
  rw [← sub_eq_zero, ← neg_eq_zero, ← E]; abel

theorem two_epsR (v : V) : epsR hbig o v + epsR hbig o v = 0 := by
  have hs := Classical.choose_spec (hbig (lab v + 1) v (o (lab v)) v v)
  obtain ⟨l0, b1, b2, -, -⟩ := hs
  have hv : lab v ≠ lab (Classical.choose (hbig (lab v + 1) v (o (lab v)) v v)) := by
    rw [l0]; exact (fin3_succ_ne _).symm
  have ho' : lab (o (lab v)) ≠ lab (Classical.choose (hbig (lab v + 1) v (o (lab v)) v v)) := by
    rw [l0, ho]; exact (fin3_succ_ne _).symm
  have := two_diffR hbig hv ho' b1 b2
  unfold epsR
  rw [Sym2.eq_swap (a := v), Sym2.eq_swap (a := o (lab v))]
  exact this

theorem epsR_base (k : Fin 3) : epsR hbig o (o k) = 0 := by
  obtain ⟨w, lw, a, -, -, -⟩ := hbig (lab (o k) + 1) (o k) (o k) (o k) (o k)
  have hw : lab w ≠ lab (o k) := by rw [lw]; exact fin3_succ_ne _
  have hoo : o (lab (o k)) = o k := by rw [ho]
  have := epsR_eq hbig ho hw a.symm (by rw [hoo]; exact a.symm)
  rw [this, hoo, sub_self]

/-- Moving the endpoint of an edge inside its class. -/
theorem shiftR {x x' w : V} (hl : lab x' = lab x) (hw : lab w ≠ lab x) (a : (rG L).Adj x w)
    (b : (rG L).Adj x' w) :
    rg lab L s(x, w) = rg lab L s(x', w) + epsR hbig o x - epsR hbig o x' := by
  obtain ⟨w', l', c1, c2, c3, -⟩ := hbig (lab x + 1) x x' (o (lab x)) w
  have hw' : lab w' ≠ lab x := by rw [l']; exact fin3_succ_ne _
  have ex := epsR_eq hbig ho hw' c1.symm c3.symm
  have ex' := epsR_eq hbig ho (v := x') (by rw [hl]; exact hw') c2.symm (by rw [hl]; exact c3.symm)
  rw [hl] at ex'
  have E := diff_indepR hbig hl hw hw' a c1.symm b c2.symm
  rw [ex, ex']
  calc rg lab L s(x, w) = (rg lab L s(x, w) - rg lab L s(x, w')) + rg lab L s(x, w') := by abel
    _ = (rg lab L s(x', w) - rg lab L s(x', w')) + rg lab L s(x, w') := by rw [E]
    _ = _ := by abel

include hoadj

theorem bichromR {u v : V} (huv : (rG L).Adj u v) (hl : lab u ≠ lab v) :
    rg lab L s(u, v) = betaR (L := L) (lab := lab) o (lab u) (lab v) + epsR hbig o u + epsR hbig o v := by
  obtain ⟨v', l', c1, c2, -, -⟩ := hbig (lab v) u (o (lab u)) u u
  have S1 := shiftR hbig ho (x := v) (x' := v') (w := u) l' hl huv.symm c1
  have S2 := shiftR hbig ho (x := u) (x' := o (lab u)) (w := v') (ho _) (by rw [l']; exact hl.symm)
    c1.symm (c2.symm)
  have S3 := shiftR hbig ho (x := v') (x' := o (lab v)) (w := o (lab u)) (by rw [ho, l'])
    (by rw [ho, l']; exact hl) c2 (hoadj _ _ hl.symm)
  rw [epsR_base hbig ho] at S2 S3
  unfold betaR
  rw [Sym2.eq_swap (a := u), S1, Sym2.eq_swap (a := v'), S2, Sym2.eq_swap (a := o (lab u)), S3,
    Sym2.eq_swap (a := o (lab v))]
  abel

theorem monoR {u v : V} (huv : (rG L).Adj u v) (hl : lab v = lab u) :
    rg lab L s(u, v) = -(betaR (L := L) (lab := lab) o (lab u) (lab u + 1) +
      betaR (L := L) (lab := lab) o (lab u) (lab u + 1)) + epsR hbig o u + epsR hbig o v := by
  obtain ⟨w, lw, c1, c2, -, -⟩ := hbig (lab u + 1) u v u u
  have hw : lab w ≠ lab u := by rw [lw]; exact fin3_succ_ne _
  rw [mono_relR huv hl hw c1.symm c2.symm, bichromR hbig ho hoadj c1.symm hw.symm,
    bichromR hbig ho hoadj c2.symm (by rw [hl]; exact hw.symm), lw, hl]
  have h1 := two_epsR hbig ho u
  have h2 := two_epsR hbig ho v
  have h3 := two_epsR hbig ho w
  rw [← sub_eq_zero]
  calc _ = -((epsR hbig o u + epsR hbig o u) + (epsR hbig o v + epsR hbig o v) +
        (epsR hbig o w + epsR hbig o w)) := by abel
    _ = 0 := by rw [h1, h2, h3]; simp

/-- **Edge formula in the residual host.** -/
theorem formulaR {u v : V} (huv : (rG L).Adj u v) :
    rg lab L s(u, v) = kapR (L := L) (lab := lab) o (lab u) (lab v) + epsR hbig o u + epsR hbig o v := by
  unfold kapR
  by_cases hl : lab u = lab v
  · rw [if_pos hl, monoR hbig ho hoadj huv hl.symm]
  · rw [if_neg hl, bichromR hbig ho hoadj huv hl]

theorem betaR_rel {X Y Z : Fin 3} (hXY : X ≠ Y) (hXZ : X ≠ Z) :
    betaR (L := L) (lab := lab) o X Y + betaR (L := L) (lab := lab) o X Y =
      betaR (L := L) (lab := lab) o X Z + betaR (L := L) (lab := lab) o X Z := by
  have := two_diffR hbig (x := o X) (w := o Y) (w' := o Z) (by rw [ho, ho]; exact Ne.symm hXY)
    (by rw [ho, ho]; exact Ne.symm hXZ) (hoadj _ _ hXY) (hoadj _ _ hXZ)
  unfold betaR
  rw [← sub_eq_zero, ← this]; abel

theorem two_betaR {X Y : Fin 3} (h : X ≠ Y) :
    betaR (L := L) (lab := lab) o X Y + betaR (L := L) (lab := lab) o X Y =
      betaR (L := L) (lab := lab) o 0 1 + betaR (L := L) (lab := lab) o 0 1 := by
  have c02 := betaR_rel hbig ho hoadj (X := 0) (Y := 2) (Z := 1) (by decide) (by decide)
  have c12 : betaR (L := L) (lab := lab) o 1 2 + betaR (L := L) (lab := lab) o 1 2 =
      betaR (L := L) (lab := lab) o 0 1 + betaR (L := L) (lab := lab) o 0 1 := by
    rw [betaR_rel hbig ho hoadj (X := 1) (Y := 2) (Z := 0) (by decide) (by decide), betaR_symm o 1 0]
  obtain rfl | rfl | rfl : X = 0 ∨ X = 1 ∨ X = 2 := by fin_cases X <;> simp
  all_goals obtain rfl | rfl | rfl : Y = 0 ∨ Y = 1 ∨ Y = 2 := by fin_cases Y <;> simp
  all_goals first
    | exact absurd rfl h
    | rfl
    | exact c02
    | exact c12
    | (rw [betaR_symm o]; exact c02)
    | (rw [betaR_symm o]; exact c12)
    | (rw [betaR_symm o])

end Residual

/-! ### Summation over the residual edges -/

section ResidualSum

variable {V : Type*} [Fintype V] [LinearOrder V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

theorem ind_eq_sum (J : Finset (Sym2 V)) : ind J = ∑ e ∈ J, ind ({e} : Finset (Sym2 V)) := by
  funext e'
  rw [Finset.sum_apply]
  by_cases h : e' ∈ J
  · rw [sum_eq_single_of_mem e' h]
    · simp [ind, h]
    · intro b _ hb; simp [ind, Ne.symm hb]
  · rw [sum_eq_zero]
    · simp [ind, h]
    · intro b hb
      have : e' ≠ b := fun h' => h (h' ▸ hb)
      simp [ind, this]

theorem cdrF_cases {X Y Z : Fin 3} (h : ({X, Y, Z} : Multiset (Fin 3)) ∈ cdrF) :
    (X = Y ∧ X ≠ Z) ∨ (X = Z ∧ X ≠ Y) ∨ (Y = Z ∧ X ≠ Y) := by
  simp only [cdrF, Set.mem_ofPred_eq] at h
  revert h
  fin_cases X <;> fin_cases Y <;> fin_cases Z <;> decide

/-- The class constants vanish on a bicoloured triangle. -/
theorem kap_tri {Q : Type*} [AddCommGroup Q] (κ : Fin 3 → Fin 3 → Q) (γ : Q)
    (hdiag : ∀ X, κ X X = -γ) (hsym : ∀ X Y, κ X Y = κ Y X)
    (hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ) {X Y Z : Fin 3}
    (h : ({X, Y, Z} : Multiset (Fin 3)) ∈ cdrF) : κ X Y + κ X Z + κ Y Z = 0 := by
  rcases cdrF_cases h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rw [hdiag, add_assoc, hoff X Z h']; abel
  · rw [hdiag, hsym Y X, show κ X Y + -γ + κ X Y = (κ X Y + κ X Y) - γ by abel, hoff X Y h',
      sub_self]
  · rw [hdiag, hoff X Y h']; abel

theorem edges_rHost :
    edges (rHost lab L) = ((univ : Finset V).sym2.filter fun e => ¬ e.IsDiag).filter
      fun e => e ∉ L := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [edges, rG, and_comm]

/-- **H2 for the residual host**, general form. -/
theorem residual_physical (hbig : BigR lab L) {o : Fin 3 → V}
    (ho : ∀ k, lab (o k) = k) (hoadj : ∀ j k, j ≠ k → (rG L).Adj (o j) (o k))
    (P : Finset (Finset V)) (hPall : ∀ T ∈ P, IsAllowed (cHost lab) cdrF T)
    (hPdisj : (P : Set (Finset V)).PairwiseDisjoint triEdges) (hL : L = P.biUnion triEdges)
    (hn : Even (Fintype.card V - 1)) (h01 : Even (csz lab 0 * csz lab 1))
    (h02 : Even (csz lab 0 * csz lab 2)) (h12 : Even (csz lab 1 * csz lab 2))
    (hadm : (csz lab 0 : ℤ) ^ 2 + (csz lab 1 : ℤ) ^ 2 + (csz lab 2 : ℤ) ^ 2 -
      csz lab 0 * csz lab 1 - csz lab 0 * csz lab 2 - csz lab 1 * csz lab 2 =
      csz lab 0 + csz lab 1 + csz lab 2) :
    IsPhysical (rHost lab L) cdrF (edges (rHost lab L)) := by
  unfold IsPhysical
  rw [← Submodule.Quotient.mk_eq_zero, ind_eq_sum, ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  change ∑ e ∈ edges (rHost lab L), rg lab L e = 0
  set κ := kapR (L := L) (lab := lab) o with hκ
  set ε := epsR hbig o with hε
  set γ := betaR (L := L) (lab := lab) o 0 1 + betaR (L := L) (lab := lab) o 0 1 with hγ
  have hdiag : ∀ X, κ X X = -γ := by
    intro X
    simp only [hκ, kapR, if_pos]
    obtain rfl | rfl | rfl : X = 0 ∨ X = 1 ∨ X = 2 := by fin_cases X <;> simp
    · rfl
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, two_betaR hbig ho hoadj (by decide)]
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, two_betaR hbig ho hoadj (by decide)]
  have hsym : ∀ X Y, κ X Y = κ Y X := by
    intro X Y
    simp only [hκ, kapR]
    by_cases h : X = Y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), betaR_symm]
  have hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ := by
    intro X Y h
    simp only [hκ, kapR, if_neg h]
    exact two_betaR hbig ho hoadj h
  have h2ε : ∀ v, ε v + ε v = 0 := two_epsR hbig ho
  let f : Sym2 V → RQ lab L := Sym2.lift ⟨fun u v => κ (lab u) (lab v) + ε u + ε v,
    fun u v => by
      show κ (lab u) (lab v) + ε u + ε v = κ (lab v) (lab u) + ε v + ε u
      rw [hsym]; abel⟩
  -- the edges of `G` satisfy the formula
  have hform : ∑ e ∈ edges (rHost lab L), rg lab L e = ∑ e ∈ edges (rHost lab L), f e := by
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | _ u v =>
    have hadj : (rG L).Adj u v := by
      simp only [edges, mem_filter, mem_univ, true_and] at he
      exact he
    exact formulaR hbig ho hoadj hadj
  rw [hform, edges_rHost]
  set N := (univ : Finset V).sym2.filter fun e => ¬ e.IsDiag with hN
  have hLN : N.filter (fun e => e ∈ L) = L := by
    ext e
    simp only [hN, mem_filter, mem_sym2_iff, mem_univ, implies_true, true_and]
    constructor
    · exact fun h => h.2
    · intro he
      refine ⟨?_, he⟩
      rw [hL] at he
      obtain ⟨T, -, hT⟩ := mem_biUnion.mp he
      simp only [triEdges, mem_filter] at hT
      exact hT.2
  have hsplit := sum_filter_add_sum_filter_not N (fun e => e ∈ L) f
  rw [hLN] at hsplit
  -- the sum over all pairs vanishes
  have hall : ∑ e ∈ N, f e = 0 := by
    rw [hN, sum_sym2_filter_not_isDiag]
    exact formula_sum_zero κ ε γ h2ε hdiag hsym hoff hn h01 h02 h12 hadm
  -- the sum over the packing vanishes
  have hpack : ∑ e ∈ L, f e = 0 := by
    have hre : ∑ e ∈ L, f e = ∑ e ∈ P.biUnion triEdges, f e := by rw [← hL]
    rw [hre, sum_biUnion hPdisj]
    refine sum_eq_zero fun T hT => ?_
    obtain ⟨h3, -, hF⟩ := hPall T hT
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp h3
    have hlab : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF := by
      have : ({x, y, z} : Finset V).val.map lab ∈ cdrF := hF
      rwa [val_map_triple lab hxy hxz.symm hyz.symm] at this
    rw [triEdges_triple hxy hxz hyz, sum_insert (by simp [hyz, hxz]),
      sum_insert (by simp [hxy, hxz]), sum_singleton]
    simp only [f, Sym2.lift_mk]
    have k := kap_tri κ γ hdiag hsym hoff hlab
    have ex := h2ε x
    have ey := h2ε y
    have ez := h2ε z
    calc _ = (κ (lab x) (lab y) + κ (lab x) (lab z) + κ (lab y) (lab z)) + (ε x + ε x) +
          (ε y + ε y) + (ε z + ε z) := by abel
      _ = 0 := by rw [k, ex, ey, ez]; simp
  rw [hpack, hall, zero_add] at hsplit
  exact hsplit

omit [Fintype V] [LinearOrder V] in
/-- Base points of the three classes, pairwise adjacent. -/
theorem exists_base (hbig : BigR lab L) (p : V) :
    ∃ o : Fin 3 → V, (∀ k, lab (o k) = k) ∧ ∀ j k, j ≠ k → (rG L).Adj (o j) (o k) := by
  obtain ⟨o0, l0, -, -, -, -⟩ := hbig 0 p p p p
  obtain ⟨o1, l1, a10, -, -, -⟩ := hbig 1 o0 o0 o0 o0
  obtain ⟨o2, l2, a20, a21, -, -⟩ := hbig 2 o0 o1 o1 o1
  refine ⟨![o0, o1, o2], fun k => ?_, fun j k hjk => ?_⟩
  · fin_cases k <;> simpa
  · fin_cases j <;> fin_cases k <;> simp_all [a10.symm, a20.symm, a21.symm]

end ResidualSum

end CDRBicolour.Absorption
