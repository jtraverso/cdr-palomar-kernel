/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Lattice
public import CDRBicolour.Absorption.ResidualHinge

/-!
# H2 for the residual `k`-class host

The residual host `K_n − L` with labels in `Fin k` (`rHostK`), where `L` is the edge set of a
packing of allowed triangles. With the density condition `BigRk` (every class has a point
adjacent, in `K_n − L`, to any `k + 4` given points; `bigRk_of_deg` from a degree bound on `L`):

* local relations in the quotient by the lattice (the three-class residual relations with the
  next-class map `nx` of the `k`-class complete host);
* `formulaRk`: `g(uv) = κ(lab u, lab v) + ε(u) + ε(v)` for every residual edge;
* `residual_physicalK`: the indicator of the residual edges lies in the lattice
  (`formula_sum_zero` over all pairs, minus the triangles of the packing).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption

section ResidualK

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The residual host with `k` labels. -/
abbrev rHostK (lab : V → Fin k) (L : Finset (Sym2 V)) : Host V (Fin k) := ⟨rG L, lab⟩

/-- The quotient by the lattice of the residual host. -/
abbrev RQk (lab : V → Fin k) (L : Finset (Sym2 V)) :=
  (Sym2 V → ℤ) ⧸ lattice (rHostK lab L) (bicF k)

/-- The class of a single edge. -/
def rgk (lab : V → Fin k) (L : Finset (Sym2 V)) (e : Sym2 V) : RQk lab L :=
  Submodule.Quotient.mk (ind ({e} : Finset (Sym2 V)))

/-- Density: every class has a point adjacent in `K_n − L` to any `k + 4` given points. -/
def BigRk (lab : V → Fin k) (L : Finset (Sym2 V)) : Prop :=
  ∀ (X : Fin k) (S : Finset V), S.card ≤ k + 4 → ∃ w, lab w = X ∧ ∀ s ∈ S, (rG L).Adj w s

variable {lab : V → Fin k} {L : Finset (Sym2 V)}

theorem big4 (hbig : BigRk lab L) (X : Fin k) (p q r s : V) :
    ∃ w, lab w = X ∧ (rG L).Adj w p ∧ (rG L).Adj w q ∧ (rG L).Adj w r ∧ (rG L).Adj w s := by
  have hc : ({p, q, r, s} : Finset V).card ≤ k + 4 := by
    have := card_le_four (a := p) (b := q) (c := r) (d := s); omega
  obtain ⟨w, hw, ha⟩ := hbig X {p, q, r, s} hc
  exact ⟨w, hw, ha p (by simp), ha q (by simp), ha r (by simp), ha s (by simp)⟩

/-- Density from a degree bound on the leave. -/
theorem bigRk_of_deg {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ)
    (hcls : ∀ X, (k + 4) * (Δ + 1) < ksz lab X) : BigRk lab L := by
  intro X S hS
  set B := S.biUnion (fun s => insert s (nbL L s)) with hB
  have hBc : #B ≤ (k + 4) * (Δ + 1) := by
    calc #B ≤ ∑ s ∈ S, #(insert s (nbL L s)) := card_biUnion_le
      _ ≤ ∑ _s ∈ S, (Δ + 1) := sum_le_sum fun s _ =>
          (card_insert_le _ _).trans (Nat.succ_le_succ (hdeg s))
      _ = #S * (Δ + 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ (k + 4) * (Δ + 1) := Nat.mul_le_mul_right _ hS
  have hlt : #B < #(univ.filter fun v => lab v = X) := lt_of_le_of_lt hBc (hcls X)
  obtain ⟨w, hw, hwB⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, (mem_filter.1 hw).2, fun s hs => ?_⟩
  have hws : w ∉ insert s (nbL L s) := fun h => hwB (mem_biUnion.2 ⟨s, hs, h⟩)
  exact adj_of_not_nbL (fun h => hws (h ▸ mem_insert_self _ _))
    (fun h => hws (mem_insert_of_mem h))

/-! ### Local relations -/

def betaRk (lab : V → Fin k) (L : Finset (Sym2 V)) (o : Fin k → V) (X Y : Fin k) : RQk lab L :=
  rgk lab L s(o X, o Y)

def kapRk (lab : V → Fin k) (L : Finset (Sym2 V)) (o : Fin k → V) (nx : Fin k → Fin k)
    (X Y : Fin k) : RQk lab L :=
  if X = Y then -(betaRk lab L o X (nx X) + betaRk lab L o X (nx X)) else betaRk lab L o X Y

theorem betaRk_symm (o : Fin k → V) (X Y : Fin k) : betaRk lab L o X Y = betaRk lab L o Y X := by
  unfold betaRk; rw [Sym2.eq_swap]

theorem isAllowed_tripleRk {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k) :
    IsAllowed (rHostK lab L) (bicF k) {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy.ne, hxz.ne, hyz.ne, rfl⟩, fun u hu v hv huv => ?_, ?_⟩
  · simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> first | exact absurd rfl huv | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
  · show ({x, y, z} : Finset V).val.map lab ∈ bicF k
    rw [val_map_triple lab hxy.ne hxz.ne.symm hyz.ne.symm]; exact hF

theorem tri_relRk {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k) :
    rgk lab L s(x, y) + rgk lab L s(x, z) + rgk lab L s(y, z) = 0 := by
  have hmem : ind (triEdges ({x, y, z} : Finset V)) ∈ lattice (rHostK lab L) (bicF k) :=
    Submodule.subset_span ⟨{x, y, z}, isAllowed_tripleRk hxy hxz hyz hF, rfl⟩
  rw [ind_triple hxy.ne hxz.ne hyz.ne] at hmem
  simp only [rgk, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

theorem mono_relRk {x x' w : V} (hxx : (rG L).Adj x x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hxw : (rG L).Adj x w) (hx'w : (rG L).Adj x' w) :
    rgk lab L s(x, x') = -rgk lab L s(x, w) - rgk lab L s(x', w) :=
  eq_neg_sub_of_add (tri_relRk hxx hxw hx'w
    (mem_bicF.2 (Or.inl ⟨hl.symm, by rw [hl]; exact Ne.symm hw⟩)))

theorem sq_relRk {x x' w w' : V} (hxx : (rG L).Adj x x') (hl : lab x' = lab x)
    (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x) (a1 : (rG L).Adj x w) (a2 : (rG L).Adj x' w)
    (a3 : (rG L).Adj x w') (a4 : (rG L).Adj x' w') :
    (rgk lab L s(x, w) - rgk lab L s(x, w')) + (rgk lab L s(x', w) - rgk lab L s(x', w')) = 0 := by
  have h1 := mono_relRk hxx hl hw a1 a2
  have h2 := mono_relRk hxx hl hw' a3 a4
  rw [h1] at h2
  rw [← neg_eq_zero, ← sub_eq_zero.2 h2]; abel

theorem tri_DRk {x x' x'' w w' : V} (h1 : (rG L).Adj x x') (h2 : (rG L).Adj x x'')
    (h3 : (rG L).Adj x' x'') (l1 : lab x' = lab x) (l2 : lab x'' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) (a : (rG L).Adj x w) (a' : (rG L).Adj x w')
    (b : (rG L).Adj x' w) (b' : (rG L).Adj x' w') (c : (rG L).Adj x'' w)
    (c' : (rG L).Adj x'' w') :
    (rgk lab L s(x, w) - rgk lab L s(x, w')) + (rgk lab L s(x, w) - rgk lab L s(x, w')) = 0 ∧
    rgk lab L s(x', w) - rgk lab L s(x', w') = rgk lab L s(x, w) - rgk lab L s(x, w') := by
  have A := sq_relRk h1 l1 hw hw' a b a' b'
  have B := sq_relRk h2 l2 hw hw' a c a' c'
  have C := sq_relRk (w := w) (w' := w') h3 (l2.trans l1.symm) (by rw [l1]; exact hw)
    (by rw [l1]; exact hw') b c b' c'
  have hD : (rgk lab L s(x, w) - rgk lab L s(x, w')) +
      (rgk lab L s(x, w) - rgk lab L s(x, w')) = 0 := by
    calc _ = ((rgk lab L s(x, w) - rgk lab L s(x, w')) +
            (rgk lab L s(x', w) - rgk lab L s(x', w'))) +
          ((rgk lab L s(x, w) - rgk lab L s(x, w')) +
            (rgk lab L s(x'', w) - rgk lab L s(x'', w'))) -
          ((rgk lab L s(x', w) - rgk lab L s(x', w')) +
            (rgk lab L s(x'', w) - rgk lab L s(x'', w'))) := by abel
      _ = 0 := by rw [A, B, C]; simp
  refine ⟨hD, ?_⟩
  rw [← sub_eq_zero]
  calc _ = ((rgk lab L s(x, w) - rgk lab L s(x, w')) +
          (rgk lab L s(x', w) - rgk lab L s(x', w'))) -
        ((rgk lab L s(x, w) - rgk lab L s(x, w')) +
          (rgk lab L s(x, w) - rgk lab L s(x, w'))) := by abel
    _ = 0 := by rw [A, hD, sub_zero]

variable (hbig : BigRk lab L)
include hbig

theorem two_diffRk {x w w' : V} (hw : lab w ≠ lab x) (hw' : lab w' ≠ lab x)
    (a : (rG L).Adj x w) (a' : (rG L).Adj x w') :
    (rgk lab L s(x, w) - rgk lab L s(x, w')) + (rgk lab L s(x, w) - rgk lab L s(x, w')) = 0 := by
  obtain ⟨x', l1, b1, b2, b3, -⟩ := big4 hbig (lab x) x w w' w
  obtain ⟨x'', l2, c1, c2, c3, c4⟩ := big4 hbig (lab x) x x' w w'
  exact (tri_DRk b1.symm c1.symm c2.symm l1 l2 hw hw' a a' b2 b3 c3 c4).1

theorem diff_indepRk {x x' w w' : V} (hl : lab x' = lab x) (hw : lab w ≠ lab x)
    (hw' : lab w' ≠ lab x) (a : (rG L).Adj x w) (a' : (rG L).Adj x w') (b : (rG L).Adj x' w)
    (b' : (rG L).Adj x' w') :
    rgk lab L s(x', w) - rgk lab L s(x', w') = rgk lab L s(x, w) - rgk lab L s(x, w') := by
  obtain ⟨y, ly, y1, y2, y3, y4⟩ := big4 hbig (lab x) x x' w w'
  obtain ⟨z, lz, z1, z2, z3, z4⟩ := big4 hbig (lab x) x y w w'
  obtain ⟨z', lz', z1', z2', z3', z4'⟩ := big4 hbig (lab x) x' y w w'
  have E1 := (tri_DRk y1.symm z1.symm z2.symm ly lz hw hw' a a' y3 y4 z3 z4).2
  have E2 := (tri_DRk (x := x') y2.symm z1'.symm z2'.symm (ly.trans hl.symm) (lz'.trans hl.symm)
    (by rw [hl]; exact hw) (by rw [hl]; exact hw') b b' y3 y4 z3' z4').2
  rw [← E1, E2]

/-- The vertex potential (base points `o`, next-class map `nx`). -/
def epsRk (o : Fin k → V) (nx : Fin k → Fin k) (v : V) : RQk lab L :=
  rgk lab L s(v, Classical.choose (big4 hbig (nx (lab v)) v (o (lab v)) v v)) -
    rgk lab L s(o (lab v), Classical.choose (big4 hbig (nx (lab v)) v (o (lab v)) v v))

variable {o : Fin k → V} {nx : Fin k → Fin k} (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X)
  (hoadj : ∀ X Y, X ≠ Y → (rG L).Adj (o X) (o Y))
include ho hnx

theorem epsRk_eq {v w : V} (hw : lab w ≠ lab v) (a : (rG L).Adj v w)
    (a' : (rG L).Adj (o (lab v)) w) :
    epsRk hbig o nx v = rgk lab L s(v, w) - rgk lab L s(o (lab v), w) := by
  have hs := Classical.choose_spec (big4 hbig (nx (lab v)) v (o (lab v)) v v)
  set w0 := Classical.choose (big4 hbig (nx (lab v)) v (o (lab v)) v v)
  obtain ⟨l0, b1, b2, -, -⟩ := hs
  have hw0 : lab w0 ≠ lab v := by rw [l0]; exact hnx _
  have E := diff_indepRk hbig (x := v) (x' := o (lab v)) (w := w0) (w' := w) (ho _) hw0 hw
    b1.symm a b2.symm a'
  unfold epsRk
  rw [← sub_eq_zero] at E
  rw [← sub_eq_zero, ← neg_eq_zero, ← E]; abel

theorem two_epsRk (v : V) : epsRk hbig o nx v + epsRk hbig o nx v = 0 := by
  have hs := Classical.choose_spec (big4 hbig (nx (lab v)) v (o (lab v)) v v)
  obtain ⟨l0, b1, b2, -, -⟩ := hs
  have hv : lab v ≠ lab (Classical.choose (big4 hbig (nx (lab v)) v (o (lab v)) v v)) := by
    rw [l0]; exact (hnx _).symm
  have ho' : lab (o (lab v)) ≠
      lab (Classical.choose (big4 hbig (nx (lab v)) v (o (lab v)) v v)) := by
    rw [l0, ho]; exact (hnx _).symm
  have := two_diffRk hbig hv ho' b1 b2
  unfold epsRk
  rw [Sym2.eq_swap (a := v), Sym2.eq_swap (a := o (lab v))]
  exact this

theorem epsRk_base (X : Fin k) : epsRk hbig o nx (o X) = 0 := by
  obtain ⟨w, lw, a, -, -, -⟩ := big4 hbig (nx (lab (o X))) (o X) (o X) (o X) (o X)
  have hw : lab w ≠ lab (o X) := by rw [lw]; exact hnx _
  have hoo : o (lab (o X)) = o X := by rw [ho]
  have := epsRk_eq hbig ho hnx hw a.symm (by rw [hoo]; exact a.symm)
  rw [this, hoo, sub_self]

theorem shiftRk {x x' w : V} (hl : lab x' = lab x) (hw : lab w ≠ lab x) (a : (rG L).Adj x w)
    (b : (rG L).Adj x' w) :
    rgk lab L s(x, w) = rgk lab L s(x', w) + epsRk hbig o nx x - epsRk hbig o nx x' := by
  obtain ⟨w', l', c1, c2, c3, -⟩ := big4 hbig (nx (lab x)) x x' (o (lab x)) w
  have hw' : lab w' ≠ lab x := by rw [l']; exact hnx _
  have ex := epsRk_eq hbig ho hnx hw' c1.symm c3.symm
  have ex' := epsRk_eq hbig ho hnx (v := x') (by rw [hl]; exact hw') c2.symm
    (by rw [hl]; exact c3.symm)
  rw [hl] at ex'
  have E := diff_indepRk hbig hl hw hw' a c1.symm b c2.symm
  rw [ex, ex']
  calc rgk lab L s(x, w) = (rgk lab L s(x, w) - rgk lab L s(x, w')) + rgk lab L s(x, w') := by
        abel
    _ = (rgk lab L s(x', w) - rgk lab L s(x', w')) + rgk lab L s(x, w') := by rw [E]
    _ = _ := by abel

include hoadj

theorem bichromRk {u v : V} (huv : (rG L).Adj u v) (hl : lab u ≠ lab v) :
    rgk lab L s(u, v) = betaRk lab L o (lab u) (lab v) + epsRk hbig o nx u + epsRk hbig o nx v := by
  obtain ⟨v', l', c1, c2, -, -⟩ := big4 hbig (lab v) u (o (lab u)) u u
  have S1 := shiftRk hbig ho hnx (x := v) (x' := v') (w := u) l' hl huv.symm c1
  have S2 := shiftRk hbig ho hnx (x := u) (x' := o (lab u)) (w := v') (ho _)
    (by rw [l']; exact hl.symm) c1.symm (c2.symm)
  have S3 := shiftRk hbig ho hnx (x := v') (x' := o (lab v)) (w := o (lab u)) (by rw [ho, l'])
    (by rw [ho, l']; exact hl) c2 (hoadj _ _ hl.symm)
  rw [epsRk_base hbig ho hnx] at S2 S3
  unfold betaRk
  rw [Sym2.eq_swap (a := u), S1, Sym2.eq_swap (a := v'), S2, Sym2.eq_swap (a := o (lab u)), S3,
    Sym2.eq_swap (a := o (lab v))]
  abel

theorem monoRk {u v : V} (huv : (rG L).Adj u v) (hl : lab v = lab u) :
    rgk lab L s(u, v) = -(betaRk lab L o (lab u) (nx (lab u)) +
      betaRk lab L o (lab u) (nx (lab u))) + epsRk hbig o nx u + epsRk hbig o nx v := by
  obtain ⟨w, lw, c1, c2, -, -⟩ := big4 hbig (nx (lab u)) u v u u
  have hw : lab w ≠ lab u := by rw [lw]; exact hnx _
  rw [mono_relRk huv hl hw c1.symm c2.symm, bichromRk hbig ho hnx hoadj c1.symm hw.symm,
    bichromRk hbig ho hnx hoadj c2.symm (by rw [hl]; exact hw.symm), lw, hl]
  have h1 := two_epsRk hbig ho hnx u
  have h2 := two_epsRk hbig ho hnx v
  have h3 := two_epsRk hbig ho hnx w
  rw [← sub_eq_zero]
  calc _ = -((epsRk hbig o nx u + epsRk hbig o nx u) + (epsRk hbig o nx v + epsRk hbig o nx v) +
        (epsRk hbig o nx w + epsRk hbig o nx w)) := by abel
    _ = 0 := by rw [h1, h2, h3]; simp

/-- **Edge formula in the residual `k`-class host.** -/
theorem formulaRk {u v : V} (huv : (rG L).Adj u v) :
    rgk lab L s(u, v) = kapRk lab L o nx (lab u) (lab v) + epsRk hbig o nx u +
      epsRk hbig o nx v := by
  unfold kapRk
  by_cases hl : lab u = lab v
  · rw [if_pos hl, monoRk hbig ho hnx hoadj huv hl.symm]
  · rw [if_neg hl, bichromRk hbig ho hnx hoadj huv hl]

omit hnx in
theorem betaRk_rel {X Y Z : Fin k} (hXY : X ≠ Y) (hXZ : X ≠ Z) :
    betaRk lab L o X Y + betaRk lab L o X Y = betaRk lab L o X Z + betaRk lab L o X Z := by
  have := two_diffRk hbig (x := o X) (w := o Y) (w' := o Z) (by rw [ho, ho]; exact Ne.symm hXY)
    (by rw [ho, ho]; exact Ne.symm hXZ) (hoadj _ _ hXY) (hoadj _ _ hXZ)
  unfold betaRk
  rw [← sub_eq_zero, ← this]; abel

theorem two_betaRk (X₀ : Fin k) {X Y : Fin k} (h : X ≠ Y) :
    betaRk lab L o X Y + betaRk lab L o X Y =
      betaRk lab L o X₀ (nx X₀) + betaRk lab L o X₀ (nx X₀) := by
  have hf : ∀ X Y, X ≠ Y → betaRk lab L o X Y + betaRk lab L o X Y =
      betaRk lab L o X (nx X) + betaRk lab L o X (nx X) :=
    fun X Y h => betaRk_rel hbig ho hoadj h (hnx X).symm
  have hsym : ∀ X Y, X ≠ Y → betaRk lab L o X (nx X) + betaRk lab L o X (nx X) =
      betaRk lab L o Y (nx Y) + betaRk lab L o Y (nx Y) := by
    intro X Y h
    rw [← hf X Y h, ← hf Y X (Ne.symm h), betaRk_symm o X Y]
  rw [hf X Y h]
  by_cases hX : X = X₀
  · rw [hX]
  · exact hsym X X₀ hX

end ResidualK

/-! ### Summation -/

section ResidualKSum

variable {k : ℕ} {V : Type*} [Fintype V] [LinearOrder V]
  {lab : V → Fin k} {L : Finset (Sym2 V)}

theorem kap_tri_k {Q : Type*} [AddCommGroup Q] (κ : Fin k → Fin k → Q) (γ : Q)
    (hdiag : ∀ X, κ X X = -γ) (hsym : ∀ X Y, κ X Y = κ Y X)
    (hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ) {X Y Z : Fin k}
    (h : ({X, Y, Z} : Multiset (Fin k)) ∈ bicF k) : κ X Y + κ X Z + κ Y Z = 0 := by
  rcases mem_bicF.1 h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rw [hdiag, add_assoc, hoff X Z h']; abel
  · rw [hdiag, hsym Y X, show κ X Y + -γ + κ X Y = (κ X Y + κ X Y) - γ by abel, hoff X Y h',
      sub_self]
  · rw [hdiag, hoff X Y h']; abel

theorem edges_rHostK :
    edges (rHostK lab L) = ((univ : Finset V).sym2.filter fun e => ¬ e.IsDiag).filter
      fun e => e ∉ L := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [edges, rG, and_comm]

/-- **H2 for the residual `k`-class host.** -/
theorem residual_physicalK (hbig : BigRk lab L) {o : Fin k → V} {nx : Fin k → Fin k}
    (ho : ∀ X, lab (o X) = X) (hnx : ∀ X, nx X ≠ X)
    (hoadj : ∀ X Y, X ≠ Y → (rG L).Adj (o X) (o Y)) (X₀ : Fin k)
    (P : Finset (Finset V)) (hPall : ∀ T ∈ P, IsAllowed (kHost lab) (bicF k) T)
    (hPdisj : (P : Set (Finset V)).PairwiseDisjoint triEdges) (hL : L = P.biUnion triEdges)
    (hn : Even (Fintype.card V - 1))
    (heven : ∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y))
    (hpair : ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), ksz lab j.1 * ksz lab j.2 =
      ∑ X, ksz lab X * (ksz lab X - 1)) :
    IsPhysical (rHostK lab L) (bicF k) (edges (rHostK lab L)) := by
  unfold IsPhysical
  rw [← Submodule.Quotient.mk_eq_zero, ind_eq_sum, ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  change ∑ e ∈ edges (rHostK lab L), rgk lab L e = 0
  set κ := kapRk lab L o nx with hκ
  set ε := epsRk hbig o nx with hε
  set γ := betaRk lab L o X₀ (nx X₀) + betaRk lab L o X₀ (nx X₀) with hγ
  have hdiag : ∀ X, κ X X = -γ := by
    intro X
    simp only [hκ, kapRk, if_pos]
    by_cases hX : X = X₀
    · subst hX; rfl
    · rw [two_betaRk hbig ho hnx hoadj X₀ (hnx X).symm]
  have hsym : ∀ X Y, κ X Y = κ Y X := by
    intro X Y
    simp only [hκ, kapRk]
    by_cases h : X = Y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), betaRk_symm]
  have hoff : ∀ X Y, X ≠ Y → κ X Y + κ X Y = γ := by
    intro X Y h
    simp only [hκ, kapRk, if_neg h]
    exact two_betaRk hbig ho hnx hoadj X₀ h
  have h2ε : ∀ v, ε v + ε v = 0 := two_epsRk hbig ho hnx
  let f : Sym2 V → RQk lab L := Sym2.lift ⟨fun u v => κ (lab u) (lab v) + ε u + ε v,
    fun u v => by
      show κ (lab u) (lab v) + ε u + ε v = κ (lab v) (lab u) + ε v + ε u
      rw [hsym]; abel⟩
  have hform : ∑ e ∈ edges (rHostK lab L), rgk lab L e = ∑ e ∈ edges (rHostK lab L), f e := by
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | _ u v =>
    have hadj : (rG L).Adj u v := by
      simp only [edges, mem_filter, mem_univ, true_and] at he
      exact he
    exact formulaRk hbig ho hnx hoadj hadj
  rw [hform, edges_rHostK]
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
  have hall : ∑ e ∈ N, f e = 0 := by
    rw [hN, sum_sym2_filter_not_isDiag]
    exact formula_sum_zero κ ε γ h2ε hdiag hsym hoff hn heven hpair
  have hpack : ∑ e ∈ L, f e = 0 := by
    have hre : ∑ e ∈ L, f e = ∑ e ∈ P.biUnion triEdges, f e := by rw [← hL]
    rw [hre, sum_biUnion hPdisj]
    refine sum_eq_zero fun T hT => ?_
    obtain ⟨h3, -, hF⟩ := hPall T hT
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp h3
    have hlab : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k := by
      have : ({x, y, z} : Finset V).val.map lab ∈ bicF k := hF
      rwa [val_map_triple lab hxy hxz.symm hyz.symm] at this
    rw [triEdges_triple hxy hxz hyz, sum_insert (by simp [hyz, hxz]),
      sum_insert (by simp [hxy, hxz]), sum_singleton]
    simp only [f, Sym2.lift_mk]
    have kk := kap_tri_k κ γ hdiag hsym hoff hlab
    have ex := h2ε x
    have ey := h2ε y
    have ez := h2ε z
    calc _ = (κ (lab x) (lab y) + κ (lab x) (lab z) + κ (lab y) (lab z)) + (ε x + ε x) +
          (ε y + ε y) + (ε z + ε z) := by abel
      _ = 0 := by rw [kk, ex, ey, ez]; simp
  rw [hpack, hall, zero_add] at hsplit
  exact hsplit

end ResidualKSum

/-! ### Base points -/

section Base

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin k}
  {L : Finset (Sym2 V)}

/-- Pairwise adjacent base points of all classes. -/
theorem exists_baseK (hbig : BigRk lab L) (v₀ : V) :
    ∃ o : Fin k → V, (∀ X, lab (o X) = X) ∧ ∀ X Y, X ≠ Y → (rG L).Adj (o X) (o Y) := by
  -- induction on the number of classes already placed
  have key : ∀ j ≤ k, ∃ f : Fin k → V, (∀ X : Fin k, X.val < j → lab (f X) = X) ∧
      ∀ X Y : Fin k, X.val < j → Y.val < j → X ≠ Y → (rG L).Adj (f X) (f Y) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨fun _ => v₀, fun X h => absurd h (Nat.not_lt_zero _),
        fun X _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨f, hf1, hf2⟩ := ih (by omega)
      set X₁ : Fin k := ⟨j, by omega⟩
      set S := (univ.filter fun X : Fin k => X.val < j).image f
      have hS : S.card ≤ k + 4 := by
        calc S.card ≤ (univ.filter fun X : Fin k => X.val < j).card := card_image_le
          _ ≤ (univ : Finset (Fin k)).card := card_filter_le _ _
          _ = k := by rw [card_univ, Fintype.card_fin]
          _ ≤ k + 4 := by omega
      obtain ⟨w, hw, hwS⟩ := hbig X₁ S hS
      have hfS : ∀ X : Fin k, X.val < j → (rG L).Adj w (f X) := fun X hX =>
        hwS (f X) (mem_image.2 ⟨X, mem_filter.2 ⟨mem_univ _, hX⟩, rfl⟩)
      refine ⟨Function.update f X₁ w, fun X hX => ?_, fun X Y hX hY hXY => ?_⟩
      · by_cases h : X = X₁
        · subst h; rw [Function.update_self]; exact hw
        · rw [Function.update_of_ne h]
          have : X.val < j := by
            have : X.val ≠ j := fun h' => h (Fin.ext h')
            omega
          exact hf1 X this
      · by_cases hXe : X = X₁
        · subst hXe
          have hY' : Y.val < j := by
            have : Y.val ≠ j := fun h' => hXY (Fin.ext h'.symm)
            omega
          rw [Function.update_self, Function.update_of_ne (Ne.symm hXY)]
          exact hfS Y hY'
        · by_cases hYe : Y = X₁
          · subst hYe
            have hX' : X.val < j := by
              have : X.val ≠ j := fun h' => hXe (Fin.ext h')
              omega
            rw [Function.update_self, Function.update_of_ne hXY]
            exact (hfS X hX').symm
          · rw [Function.update_of_ne hXe, Function.update_of_ne hYe]
            have hX' : X.val < j := by
              have : X.val ≠ j := fun h' => hXe (Fin.ext h')
              omega
            have hY' : Y.val < j := by
              have : Y.val ≠ j := fun h' => hYe (Fin.ext h')
              omega
            exact hf2 X Y hX' hY' hXY
  obtain ⟨f, hf1, hf2⟩ := key k le_rfl
  exact ⟨f, fun X => hf1 X X.2, fun X Y h => hf2 X Y X.2 Y.2 h⟩

end Base

end CDRBicolour.KBicolor
