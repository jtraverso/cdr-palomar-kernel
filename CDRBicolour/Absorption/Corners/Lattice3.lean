/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Defs
public import CDRBicolour.Absorption.ResidualHinge

/-!
# H2 for residual majority-type hosts (item 3, corners)

Let `G = K_n − L` be dense (`BigR`).  In the quotient of `ℤ^{E}` by the lattice of majority
triangles (`XX(X+1)`) there are potentials `φ, ψ : V → Q` with `ψ + ψ = 0` such that

* an `XX` edge `uu'` has class `−φ(u) − φ(u')` (`monoM`);
* an `X(X+1)` edge `uv`, `u ∈ X`, has class `φ(u) + ψ(v)` (`bichM`).

Hence the class of `𝟏_{E(G)}` is `Σ_u φ(u)(deg_{X+1}(u) − deg_X(u)) + Σ_u ψ(u) deg_{X−1}(u)`, which
vanishes when `G` is **balanced** (`deg_X(u) = deg_{X+1}(u)`) and `deg_{X−1}(u)` is even
(`physical_maj`).  Numerically the lattice is exactly `{π_u = 0, σ_u even}`
(`tools/corners/f3_lattice.py`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Corners

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

section Potentials

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

/-- The quotient by the majority lattice of the residual host. -/
abbrev MQ (lab : V → Fin 3) (L : Finset (Sym2 V)) := (Sym2 V → ℤ) ⧸ lattice (rHost lab L) majF

/-- The class of an edge. -/
def mg (lab : V → Fin 3) (L : Finset (Sym2 V)) (e : Sym2 V) : MQ lab L :=
  Submodule.Quotient.mk (ind ({e} : Finset (Sym2 V)))

theorem isAllowed_tripleM {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ majF) :
    IsAllowed (rHost lab L) majF {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy.ne, hxz.ne, hyz.ne, rfl⟩, fun u hu v hv huv => ?_, ?_⟩
  · simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> first | exact absurd rfl huv | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
  · show ({x, y, z} : Finset V).val.map lab ∈ majF
    rw [val_map_triple lab hxy.ne hxz.ne.symm hyz.ne.symm]; exact hF

theorem tri_relM {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ majF) :
    mg lab L s(x, y) + mg lab L s(x, z) + mg lab L s(y, z) = 0 := by
  classical
  have hmem : ind (triEdges ({x, y, z} : Finset V)) ∈ lattice (rHost lab L) majF :=
    Submodule.subset_span ⟨{x, y, z}, isAllowed_tripleM hxy hxz hyz hF, rfl⟩
  rw [ind_triple hxy.ne hxz.ne hyz.ne] at hmem
  simp only [mg, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-- The triangle relation of a majority triangle `uu'v`. -/
theorem maj_relM {u u' v : V} (huu : (rG L).Adj u u') (hl : lab u' = lab u)
    (hv : lab v = lab u + 1) (a1 : (rG L).Adj u v) (a2 : (rG L).Adj u' v) :
    mg lab L s(u, u') = -mg lab L s(u, v) - mg lab L s(u', v) :=
  eq_neg_sub_of_add (tri_relM huu a1 a2 (by rw [hl, hv]; exact ⟨lab u, rfl⟩))

theorem sq_relM {u u' v v' : V} (huu : (rG L).Adj u u') (hl : lab u' = lab u)
    (hv : lab v = lab u + 1) (hv' : lab v' = lab u + 1) (a1 : (rG L).Adj u v)
    (a2 : (rG L).Adj u' v) (a3 : (rG L).Adj u v') (a4 : (rG L).Adj u' v') :
    (mg lab L s(u, v) - mg lab L s(u, v')) + (mg lab L s(u', v) - mg lab L s(u', v')) = 0 := by
  have h1 := maj_relM huu hl hv a1 a2
  have h2 := maj_relM huu hl hv' a3 a4
  rw [h1] at h2
  rw [← neg_eq_zero, ← sub_eq_zero.2 h2]; abel

/-- Three mutually adjacent points of `X`, all adjacent to `v, v' ∈ X+1`. -/
theorem tri_DM {u u' u'' v v' : V} (h1 : (rG L).Adj u u') (h2 : (rG L).Adj u u'')
    (h3 : (rG L).Adj u' u'') (l1 : lab u' = lab u) (l2 : lab u'' = lab u)
    (hv : lab v = lab u + 1) (hv' : lab v' = lab u + 1) (a : (rG L).Adj u v)
    (a' : (rG L).Adj u v') (b : (rG L).Adj u' v) (b' : (rG L).Adj u' v')
    (c : (rG L).Adj u'' v) (c' : (rG L).Adj u'' v') :
    (mg lab L s(u, v) - mg lab L s(u, v')) + (mg lab L s(u, v) - mg lab L s(u, v')) = 0 ∧
    mg lab L s(u', v) - mg lab L s(u', v') = mg lab L s(u, v) - mg lab L s(u, v') := by
  have A := sq_relM h1 l1 hv hv' a b a' b'
  have B := sq_relM h2 l2 hv hv' a c a' c'
  have C := sq_relM (v := v) (v' := v') h3 (l2.trans l1.symm) (by rw [l1]; exact hv)
    (by rw [l1]; exact hv') b c b' c'
  set D := mg lab L s(u, v) - mg lab L s(u, v')
  set D' := mg lab L s(u', v) - mg lab L s(u', v')
  set D'' := mg lab L s(u'', v) - mg lab L s(u'', v')
  have hD : D' = D := by
    have e1 : D' = -D := by rw [← sub_eq_zero]; rw [← A]; abel
    have e2 : D'' = -D := by rw [← sub_eq_zero]; rw [← B]; abel
    have e3 : D' = -D'' := by rw [← sub_eq_zero]; rw [← C]; abel
    rw [e3, e2, neg_neg]
  refine ⟨?_, hD⟩
  calc D + D = D + D' := by rw [hD]
    _ = 0 := A

theorem fin3_add2_add1' (x : Fin 3) : x + 2 + 1 = x := by revert x; decide

variable (hbig : BigR lab L)
include hbig

/-- `D(u; v, v')` has order two. -/
theorem two_diffM {u v v' : V} (hv : lab v = lab u + 1) (hv' : lab v' = lab u + 1)
    (a : (rG L).Adj u v) (a' : (rG L).Adj u v') :
    (mg lab L s(u, v) - mg lab L s(u, v')) + (mg lab L s(u, v) - mg lab L s(u, v')) = 0 := by
  obtain ⟨u', l1, b1, b2, b3, -⟩ := hbig (lab u) u v v' v
  obtain ⟨u'', l2, c1, c2, c3, c4⟩ := hbig (lab u) u u' v v'
  exact (tri_DM b1.symm c1.symm c2.symm l1 l2 hv hv' a a' b2 b3 c3 c4).1

/-- `D(u; v, v')` does not depend on `u` in its class. -/
theorem diff_indepM {u u' v v' : V} (hl : lab u' = lab u) (hv : lab v = lab u + 1)
    (hv' : lab v' = lab u + 1) (a : (rG L).Adj u v) (a' : (rG L).Adj u v')
    (b : (rG L).Adj u' v) (b' : (rG L).Adj u' v') :
    mg lab L s(u', v) - mg lab L s(u', v') = mg lab L s(u, v) - mg lab L s(u, v') := by
  obtain ⟨y, ly, y1, y2, y3, y4⟩ := hbig (lab u) u u' v v'
  obtain ⟨z, lz, z1, z2, z3, z4⟩ := hbig (lab u) u y v v'
  obtain ⟨z', lz', z1', z2', z3', z4'⟩ := hbig (lab u) u' y v v'
  have E1 := (tri_DM y1.symm z1.symm z2.symm ly lz hv hv' a a' y3 y4 z3 z4).2
  have E2 := (tri_DM (u := u') y2.symm z1'.symm z2'.symm (ly.trans hl.symm) (lz'.trans hl.symm)
    (by rw [hl]; exact hv) (by rw [hl]; exact hv') b b' y3 y4 z3' z4').2
  rw [← E1, E2]

variable (o : Fin 3 → V)

/-- The potential `ψ(v) = D(x; v, o)` for `x` in the previous class. -/
def psiM (v : V) : MQ lab L :=
  mg lab L s(Classical.choose (hbig (lab v + 2) v (o (lab v)) v v), v) -
    mg lab L s(Classical.choose (hbig (lab v + 2) v (o (lab v)) v v), o (lab v))

/-- The potential `φ(u) = [u w] − ψ(w)` for a neighbour `w` in the next class. -/
def phiM (u : V) : MQ lab L :=
  mg lab L s(u, Classical.choose (hbig (lab u + 1) u u u u)) -
    psiM hbig o (Classical.choose (hbig (lab u + 1) u u u u))

/-- The half-edge contribution. -/
def halfM (u v : V) : MQ lab L :=
  if lab v = lab u then -phiM hbig o u
  else if lab v = lab u + 1 then phiM hbig o u else psiM hbig o u

variable {o} (ho : ∀ k, lab (o k) = k)
include ho

theorem psiM_eq {v x : V} (hx : lab x = lab v + 2) (a : (rG L).Adj x v)
    (a' : (rG L).Adj x (o (lab v))) :
    psiM hbig o v = mg lab L s(x, v) - mg lab L s(x, o (lab v)) := by
  obtain ⟨l0, b1, b2, -, -⟩ := Classical.choose_spec (hbig (lab v + 2) v (o (lab v)) v v)
  set x0 := Classical.choose (hbig (lab v + 2) v (o (lab v)) v v)
  have hv : lab v = lab x + 1 := by rw [hx, fin3_add2_add1']
  have ho' : lab (o (lab v)) = lab x + 1 := by rw [ho, hv]
  exact diff_indepM hbig (u := x) (u' := x0) (by rw [l0, hx]) hv ho' a a' b1 b2

theorem two_psiM (v : V) : psiM hbig o v + psiM hbig o v = 0 := by
  obtain ⟨l0, b1, b2, -, -⟩ := Classical.choose_spec (hbig (lab v + 2) v (o (lab v)) v v)
  set x0 := Classical.choose (hbig (lab v + 2) v (o (lab v)) v v)
  have hv : lab v = lab x0 + 1 := by rw [l0, fin3_add2_add1']
  have ho' : lab (o (lab v)) = lab x0 + 1 := by rw [ho, hv]
  exact two_diffM hbig hv ho' b1 b2

theorem phiM_eq {u w : V} (hw : lab w = lab u + 1) (a : (rG L).Adj u w) :
    phiM hbig o u = mg lab L s(u, w) - psiM hbig o w := by
  obtain ⟨l0, b1, -, -, -⟩ := Classical.choose_spec (hbig (lab u + 1) u u u u)
  set w0 := Classical.choose (hbig (lab u + 1) u u u u)
  have key : ∀ {w₁ w₂ : V}, lab w₁ = lab u + 1 → lab w₂ = lab u + 1 → (rG L).Adj u w₁ →
      (rG L).Adj u w₂ → mg lab L s(u, w₁) - psiM hbig o w₁ = mg lab L s(u, w₂) - psiM hbig o w₂ := by
    intro w₁ w₂ h1 h2 a1 a2
    obtain ⟨z, lz, z1, z2, z3, z4⟩ := hbig (lab u) w₁ w₂ (o (lab u + 1)) u
    have hz : lab z = lab w₁ + 2 := by rw [lz, h1]; generalize lab u = x; revert x; decide
    have hz' : lab z = lab w₂ + 2 := by rw [lz, h2]; generalize lab u = x; revert x; decide
    have P1 := psiM_eq hbig ho hz z1 (by rw [h1]; exact z3)
    have P2 := psiM_eq hbig ho hz' z2 (by rw [h2]; exact z3)
    rw [h1] at P1; rw [h2] at P2
    have E := diff_indepM hbig (u := u) (u' := z) lz h1 h2 a1 a2 z1 z2
    rw [P1, P2]
    rw [← sub_eq_zero]
    calc _ = (mg lab L s(u, w₁) - mg lab L s(u, w₂)) - (mg lab L s(z, w₁) - mg lab L s(z, w₂)) := by
          abel
      _ = 0 := by rw [E, sub_self]
  exact key l0 hw b1.symm a

/-- **Bichromatic edges**: `[uv] = φ(u) + ψ(v)` for `v` in the next class. -/
theorem bichM {u v : V} (huv : (rG L).Adj u v) (hv : lab v = lab u + 1) :
    mg lab L s(u, v) = phiM hbig o u + psiM hbig o v := by
  rw [phiM_eq hbig ho hv huv]; abel

/-- **Monochromatic edges**: `[uu'] = −φ(u) − φ(u')`. -/
theorem monoM {u u' : V} (huu : (rG L).Adj u u') (hl : lab u' = lab u) :
    mg lab L s(u, u') = -phiM hbig o u - phiM hbig o u' := by
  obtain ⟨v, lv, c1, c2, -, -⟩ := hbig (lab u + 1) u u' u u
  rw [maj_relM huu hl lv c1.symm c2.symm, bichM hbig ho c1.symm lv,
    bichM hbig ho c2.symm (by rw [hl]; exact lv)]
  have h := two_psiM hbig ho v
  rw [← sub_eq_zero]
  calc _ = -(psiM hbig o v + psiM hbig o v) := by abel
    _ = 0 := by rw [h, neg_zero]

/-- **Edge formula.** -/
theorem formulaM {u v : V} (huv : (rG L).Adj u v) :
    mg lab L s(u, v) = halfM hbig o u v + halfM hbig o v u := by
  unfold halfM
  by_cases h1 : lab v = lab u
  · rw [if_pos h1, if_pos h1.symm, monoM hbig ho huv h1]; abel
  by_cases h2 : lab v = lab u + 1
  · have n1 : lab u ≠ lab v + 1 := by
      rw [h2]; generalize lab u = x; revert x; decide
    rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_neg n1, bichM hbig ho huv h2]
  · have h3 : lab u = lab v + 1 := by
      revert h1 h2; generalize lab u = x; generalize lab v = y; revert x y; decide
    have n2 : lab v ≠ lab u + 1 := h2
    rw [if_neg h1, if_neg n2, if_neg (Ne.symm h1), if_pos h3, Sym2.eq_swap,
      bichM hbig ho huv.symm h3]
    abel

end Potentials

/-! ### Summation over the residual edges -/

section Sum

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

theorem ind_eq_sum' (J : Finset (Sym2 V)) : ind J = ∑ e ∈ J, ind ({e} : Finset (Sym2 V)) := by
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

open Classical in
/-- A sum over the edges of a symmetric expression is a sum over ordered adjacent pairs. -/
theorem sum_edges_half {M : Type*} [AddCommGroup M] (f : V → V → M) :
    ∑ e ∈ edges (rHost lab L), Sym2.lift ⟨fun p q => f p q + f q p, fun _ _ => add_comm _ _⟩ e =
      ∑ u, ∑ v ∈ univ.filter fun v => (rG L).Adj u v, f u v := by
  set D : Finset (V × V) := univ.filter fun x => (rG L).Adj x.1 x.2
  have hR : ∑ u, ∑ v ∈ univ.filter (fun v => (rG L).Adj u v), f u v = ∑ x ∈ D, f x.1 x.2 := by
    simp only [D, sum_filter]
    rw [← Fintype.sum_prod_type']
  rw [hR]
  have hmap : ∀ x ∈ D, s(x.1, x.2) ∈ edges (rHost lab L) := by
    intro x hx
    simp only [D, mem_filter, mem_univ, true_and] at hx
    simp only [edges, mem_filter, mem_univ, true_and]
    exact hx
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ p q =>
  have hpq : (rG L).Adj p q := by
    simp only [edges, mem_filter, mem_univ, true_and] at he; exact he
  have hne : p ≠ q := hpq.ne
  have hfib : D.filter (fun x => s(x.1, x.2) = s(p, q)) = {(p, q), (q, p)} := by
    ext ⟨x, y⟩
    simp only [D, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq,
      Sym2.eq_iff]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hpq, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hpq.symm, Or.inr ⟨rfl, rfl⟩⟩
  rw [hfib, sum_pair (by simp [hne])]
  rfl

theorem nsmul_two_zero {M : Type*} [AddCommGroup M] {a : M} (h : a + a = 0) {k : ℕ}
    (hk : Even k) : k • a = 0 := by
  obtain ⟨j, rfl⟩ := hk
  rw [add_nsmul, ← nsmul_add, h, nsmul_zero]

open Classical in
/-- **H2 for balanced residual majority-type hosts.** -/
theorem physical_maj (hbig : BigR lab L) (hex : ∀ k, ∃ v, lab v = k)
    (hbal : ∀ u, #(univ.filter fun v => (rG L).Adj u v ∧ lab v = lab u) =
      #(univ.filter fun v => (rG L).Adj u v ∧ lab v = lab u + 1))
    (hpar : ∀ u, Even #(univ.filter fun v => (rG L).Adj u v ∧ lab v = lab u + 2)) :
    IsPhysical (rHost lab L) majF (edges (rHost lab L)) := by
  classical
  choose o ho using hex
  unfold IsPhysical
  rw [← Submodule.Quotient.mk_eq_zero, ind_eq_sum', ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  change ∑ e ∈ edges (rHost lab L), mg lab L e = 0
  have hform : ∑ e ∈ edges (rHost lab L), mg lab L e = ∑ e ∈ edges (rHost lab L),
      Sym2.lift ⟨fun p q => halfM hbig o p q + halfM hbig o q p, fun _ _ => add_comm _ _⟩ e := by
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | _ u v =>
    have hadj : (rG L).Adj u v := by
      simp only [edges, mem_filter, mem_univ, true_and] at he; exact he
    exact formulaM hbig ho hadj
  rw [hform, sum_edges_half]
  refine sum_eq_zero fun u _ => ?_
  have hpt : ∀ v, halfM hbig o u v = (if lab v = lab u then -phiM hbig o u else 0) +
      (if lab v = lab u + 1 then phiM hbig o u else 0) +
      (if lab v = lab u + 2 then psiM hbig o u else 0) := by
    intro v
    unfold halfM
    by_cases h1 : lab v = lab u
    · have n1 : lab v ≠ lab u + 1 := by rw [h1]; generalize lab u = x; revert x; decide
      have n2 : lab v ≠ lab u + 2 := by rw [h1]; generalize lab u = x; revert x; decide
      simp [h1, n1, n2]
    by_cases h2 : lab v = lab u + 1
    · have n2 : lab v ≠ lab u + 2 := by rw [h2]; generalize lab u = x; revert x; decide
      simp [h1, h2, n2]
    · have h3 : lab v = lab u + 2 := by
        revert h1 h2; generalize lab v = y; generalize lab u = x; revert x y; decide
      simp [h1, h2, h3]
  simp only [hpt, sum_add_distrib, ← sum_filter, sum_const, filter_filter]
  rw [hbal u, nsmul_two_zero (two_psiM hbig ho u) (hpar u), add_zero, smul_neg,
    neg_add_cancel]

end Sum

end CDRBicolour.Absorption.Corners
