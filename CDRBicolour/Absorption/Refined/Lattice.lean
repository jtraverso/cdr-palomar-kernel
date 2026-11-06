/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.GenResidual

/-!
# H2 for the refined host (item 2b)

Labels `(col v, β v) ∈ Fin 3 × Fin 6`; in parity class `j ∈ {0, 1}` the allowed triangles are the
bicoloured ones with `⌊(Σ β mod 6)/3⌋ = j` (`refF j`).

**Reduction to the CDR lattice.** Every bicoloured triangle `xyz` of the residual graph lies in
the refined lattice (`tri_mem_refined`), so the CDR lattice is contained in the refined one and
H2 for the refined host follows from H2 for the CDR host (`refined_physical`).

**Octahedron.** With `x', y', z'` of the colours of `x, y, z` and `β` shifted by `δ`, the two
Pasch halves of the octahedron cover the same twelve edges:
`xyz = xyz' + xy'z + x'yz + x'y'z' − xy'z' − x'yz' − x'y'z` (`oct_ind`).  Writing
`r = (Σβ − 3j) mod 6` (`r ∈ {0,1,2}` means allowed): for `r = 3` take `δ = −1` (the other faces
have `r = 2, 1, 0`), for `r = 5` take `δ = +1` (`r = 0, 1, 2`), and for `r = 4` take `δ = +1`: the
three single-shift faces have `r = 5` (previous case), the others `r = 0, 1`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Refined

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-- Refined label. -/
def refLab {V : Type*} (col : V → Fin 3) (β : V → Fin 6) (v : V) : Fin 3 × Fin 6 := (col v, β v)

/-- Allowed refined types in parity class `j`. -/
def refF (j : ℕ) : Set (Multiset (Fin 3 × Fin 6)) :=
  {m | m.map Prod.fst ∈ cdrF ∧ (m.map fun l => (l.2 : ℕ)).sum % 6 / 3 = j}

theorem refF_triple {j : ℕ} {l₁ l₂ l₃ : Fin 3 × Fin 6} :
    ({l₁, l₂, l₃} : Multiset (Fin 3 × Fin 6)) ∈ refF j ↔
      ({l₁.1, l₂.1, l₃.1} : Multiset (Fin 3)) ∈ cdrF ∧
        ((l₁.2 : ℕ) + l₂.2 + l₃.2) % 6 / 3 = j := by
  simp only [refF, Set.mem_setOf_eq, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton, add_assoc]

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3} {β : V → Fin 6}
  {L : Finset (Sym2 V)}

/-- Density for the refined labels: in every refined class there is a point adjacent in `G` to
any four given points. -/
def BigRef (col : V → Fin 3) (β : V → Fin 6) (L : Finset (Sym2 V)) : Prop :=
  ∀ (k : Fin 3) (r : Fin 6) (p q s t : V), ∃ w, col w = k ∧ β w = r ∧ (rG L).Adj w p ∧
    (rG L).Adj w q ∧ (rG L).Adj w s ∧ (rG L).Adj w t

/-- The refined lattice. -/
abbrev RLat (col : V → Fin 3) (β : V → Fin 6) (L : Finset (Sym2 V)) (j : ℕ) :=
  lattice (gHost (refLab col β) L) (refF j)

theorem mem_of_ok (j : ℕ) {x y z : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (hF : ({col x, col y, col z} : Multiset (Fin 3)) ∈ cdrF)
    (hs : ((β x : ℕ) + β y + β z) % 6 / 3 = j) :
    ind (triEdges ({x, y, z} : Finset V)) ∈ RLat col β L j := by
  have hA : IsAllowed (gHost (refLab col β) L) (refF j) {x, y, z} :=
    gisAllowed_triple hxy hxz hyz (refF_triple.2 ⟨hF, hs⟩)
  exact Submodule.subset_span ⟨_, hA, rfl⟩

/-- The octahedron identity. -/
theorem oct_ind {x y z x' y' z' : V} (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (x'y : x' ≠ y) (x'z : x' ≠ z) (xy' : x ≠ y') (y'z : y' ≠ z) (x'y' : x' ≠ y')
    (xz' : x ≠ z') (yz' : y ≠ z') (x'z' : x' ≠ z') (y'z' : y' ≠ z') :
    ind (triEdges ({x, y, z} : Finset V)) =
      ind (triEdges ({x, y, z'} : Finset V)) + ind (triEdges ({x, y', z} : Finset V)) +
        ind (triEdges ({x', y, z} : Finset V)) + ind (triEdges ({x', y', z'} : Finset V)) -
        ind (triEdges ({x, y', z'} : Finset V)) - ind (triEdges ({x', y, z'} : Finset V)) -
        ind (triEdges ({x', y', z} : Finset V)) := by
  rw [ind_triple xy xz yz, ind_triple xy xz' yz', ind_triple xy' xz y'z, ind_triple x'y x'z yz,
    ind_triple x'y' x'z' y'z', ind_triple xy' xz' y'z', ind_triple x'y x'z' yz',
    ind_triple x'y' x'z y'z]
  abel

theorem exists_oct (hbig : BigRef col β L) (δ : Fin 6) {x y z : V} :
    ∃ x' y' z', col x' = col x ∧ β x' = β x + δ ∧ col y' = col y ∧ β y' = β y + δ ∧
      col z' = col z ∧ β z' = β z + δ ∧
      (rG L).Adj x' y ∧ (rG L).Adj x' z ∧ (rG L).Adj x y' ∧ (rG L).Adj y' z ∧
      (rG L).Adj x' y' ∧ (rG L).Adj x z' ∧ (rG L).Adj y z' ∧ (rG L).Adj x' z' ∧
      (rG L).Adj y' z' := by
  obtain ⟨x', c1, b1, a1, a2, -, -⟩ := hbig (col x) (β x + δ) y z z z
  obtain ⟨y', c2, b2, a3, a4, a5, -⟩ := hbig (col y) (β y + δ) x z x' x'
  obtain ⟨z', c3, b3, a6, a7, a8, a9⟩ := hbig (col z) (β z + δ) x y x' y'
  exact ⟨x', y', z', c1, b1, c2, b2, c3, b3, a1, a2, a3.symm, a4, a5.symm, a6.symm, a7.symm,
    a8.symm, a9.symm⟩

/-- The octahedron step: if the seven other faces are in the lattice, so is `xyz`. -/
theorem mem_of_oct (j : ℕ) {x y z x' y' z' : V} (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z)
    (hyz : (rG L).Adj y z) (a1 : (rG L).Adj x' y) (a2 : (rG L).Adj x' z) (a3 : (rG L).Adj x y')
    (a4 : (rG L).Adj y' z) (a5 : (rG L).Adj x' y') (a6 : (rG L).Adj x z') (a7 : (rG L).Adj y z')
    (a8 : (rG L).Adj x' z') (a9 : (rG L).Adj y' z')
    (f1 : ind (triEdges ({x, y, z'} : Finset V)) ∈ RLat col β L j)
    (f2 : ind (triEdges ({x, y', z} : Finset V)) ∈ RLat col β L j)
    (f3 : ind (triEdges ({x', y, z} : Finset V)) ∈ RLat col β L j)
    (f4 : ind (triEdges ({x', y', z'} : Finset V)) ∈ RLat col β L j)
    (f5 : ind (triEdges ({x, y', z'} : Finset V)) ∈ RLat col β L j)
    (f6 : ind (triEdges ({x', y, z'} : Finset V)) ∈ RLat col β L j)
    (f7 : ind (triEdges ({x', y', z} : Finset V)) ∈ RLat col β L j) :
    ind (triEdges ({x, y, z} : Finset V)) ∈ RLat col β L j := by
  rw [oct_ind hxy.ne hxz.ne hyz.ne a1.ne a2.ne a3.ne a4.ne a5.ne a6.ne a7.ne a8.ne a9.ne]
  exact sub_mem (sub_mem (sub_mem (add_mem (add_mem (add_mem f1 f2) f3) f4) f5) f6) f7

theorem val_shift (b δ : Fin 6) : ((b + δ : Fin 6) : ℕ) = ((b : ℕ) + δ) % 6 := Fin.val_add _ _

/-- Cases `r = 3` and `r = 5`: one octahedron. -/
theorem mem_r35 (hbig : BigRef col β L) (j : ℕ) (hj : j < 2) {x y z : V}
    (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z) (hyz : (rG L).Adj y z)
    (hF : ({col x, col y, col z} : Multiset (Fin 3)) ∈ cdrF)
    (hr : ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 3 ∨
      ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 5) :
    ind (triEdges ({x, y, z} : Finset V)) ∈ RLat col β L j := by
  set δ : Fin 6 := if ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 3 then 5 else 1 with hδ
  have hδv : (δ : ℕ) = if ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 3 then 5 else 1 := by
    rw [hδ]; split_ifs <;> rfl
  obtain ⟨x', y', z', cx, bx, cy, by', cz, bz, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    exists_oct hbig δ (x := x) (y := y) (z := z)
  have ex : (β x' : ℕ) = ((β x : ℕ) + δ) % 6 := by rw [bx, val_shift]
  have ey : (β y' : ℕ) = ((β y : ℕ) + δ) % 6 := by rw [by', val_shift]
  have ez : (β z' : ℕ) = ((β z : ℕ) + δ) % 6 := by rw [bz, val_shift]
  have lx := (β x).isLt; have ly := (β y).isLt; have lz := (β z).isLt
  have hδ' : (((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 3 ∧ (δ : ℕ) = 5) ∨
      (((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 5 ∧ (δ : ℕ) = 1) := by
    rw [hδv]; split_ifs with h <;> omega
  have hF' : ∀ p q s : V, col p = col x → col q = col y → col s = col z →
      ({col p, col q, col s} : Multiset (Fin 3)) ∈ cdrF := by
    intro p q s hp hq hs; rw [hp, hq, hs]; exact hF
  refine mem_of_oct j hxy hxz hyz a1 a2 a3 a4 a5 a6 a7 a8 a9
    (mem_of_ok j hxy a6 a7 (hF' _ _ _ rfl rfl cz) ?_)
    (mem_of_ok j a3 hxz a4 (hF' _ _ _ rfl cy rfl) ?_)
    (mem_of_ok j a1 a2 hyz (hF' _ _ _ cx rfl rfl) ?_)
    (mem_of_ok j a5 a8 a9 (hF' _ _ _ cx cy cz) ?_)
    (mem_of_ok j a3 a6 a9 (hF' _ _ _ rfl cy cz) ?_)
    (mem_of_ok j a1 a8 a7 (hF' _ _ _ cx rfl cz) ?_)
    (mem_of_ok j a5 a2 a4 (hF' _ _ _ cx cy rfl) ?_) <;>
  · simp only [ex, ey, ez]; omega

/-- Case `r = 4`: one octahedron, the single-shift faces fall in case `r = 5`. -/
theorem mem_r4 (hbig : BigRef col β L) (j : ℕ) (hj : j < 2) {x y z : V}
    (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z) (hyz : (rG L).Adj y z)
    (hF : ({col x, col y, col z} : Multiset (Fin 3)) ∈ cdrF)
    (hr : ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 4) :
    ind (triEdges ({x, y, z} : Finset V)) ∈ RLat col β L j := by
  obtain ⟨x', y', z', cx, bx, cy, by', cz, bz, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    exists_oct hbig 1 (x := x) (y := y) (z := z)
  have ex : (β x' : ℕ) = ((β x : ℕ) + 1) % 6 := by rw [bx, val_shift]; rfl
  have ey : (β y' : ℕ) = ((β y : ℕ) + 1) % 6 := by rw [by', val_shift]; rfl
  have ez : (β z' : ℕ) = ((β z : ℕ) + 1) % 6 := by rw [bz, val_shift]; rfl
  have lx := (β x).isLt; have ly := (β y).isLt; have lz := (β z).isLt
  have hF' : ∀ p q s : V, col p = col x → col q = col y → col s = col z →
      ({col p, col q, col s} : Multiset (Fin 3)) ∈ cdrF := by
    intro p q s hp hq hs; rw [hp, hq, hs]; exact hF
  refine mem_of_oct j hxy hxz hyz a1 a2 a3 a4 a5 a6 a7 a8 a9
    (mem_r35 hbig j hj hxy a6 a7 (hF' _ _ _ rfl rfl cz) ?_)
    (mem_r35 hbig j hj a3 hxz a4 (hF' _ _ _ rfl cy rfl) ?_)
    (mem_r35 hbig j hj a1 a2 hyz (hF' _ _ _ cx rfl rfl) ?_)
    (mem_of_ok j a5 a8 a9 (hF' _ _ _ cx cy cz) ?_)
    (mem_of_ok j a3 a6 a9 (hF' _ _ _ rfl cy cz) ?_)
    (mem_of_ok j a1 a8 a7 (hF' _ _ _ cx rfl cz) ?_)
    (mem_of_ok j a5 a2 a4 (hF' _ _ _ cx cy rfl) ?_) <;>
  · simp only [ex, ey, ez]; omega

/-- **Every bicoloured triangle of the residual graph lies in the refined lattice.** -/
theorem tri_mem_refined (hbig : BigRef col β L) (j : ℕ) (hj : j < 2) {x y z : V}
    (hxy : (rG L).Adj x y) (hxz : (rG L).Adj x z) (hyz : (rG L).Adj y z)
    (hF : ({col x, col y, col z} : Multiset (Fin 3)) ∈ cdrF) :
    ind (triEdges ({x, y, z} : Finset V)) ∈ RLat col β L j := by
  have lx := (β x).isLt; have ly := (β y).isLt; have lz := (β z).isLt
  by_cases h4 : ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 4
  · exact mem_r4 hbig j hj hxy hxz hyz hF h4
  by_cases h35 : ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 3 ∨
      ((β x : ℕ) + β y + β z + 6 - 3 * j) % 6 = 5
  · exact mem_r35 hbig j hj hxy hxz hyz hF h35
  exact mem_of_ok j hxy hxz hyz hF (by omega)

/-- The CDR lattice of the residual graph is contained in the refined one. -/
theorem cdr_le_refined (hbig : BigRef col β L) (j : ℕ) (hj : j < 2) :
    lattice (rHost col L) cdrF ≤ RLat col β L j := by
  rw [lattice, Submodule.span_le]
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 hT.1
  have adj : ∀ p ∈ ({x, y, z} : Finset V), ∀ q ∈ ({x, y, z} : Finset V), p ≠ q →
      (rG L).Adj p q := hT.2.1
  have hF : ({col x, col y, col z} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({x, y, z} : Finset V).val.map col ∈ cdrF := hT.2.2
    rwa [val_map_triple col hxy (Ne.symm hxz) (Ne.symm hyz)] at this
  exact tri_mem_refined hbig j hj (adj x (by simp) y (by simp) hxy)
    (adj x (by simp) z (by simp) hxz) (adj y (by simp) z (by simp) hyz) hF

/-- **H2 for the refined residual host**, from H2 for the CDR residual host. -/
theorem refined_physical (hbig : BigRef col β L) (j : ℕ) (hj : j < 2)
    (hphys : IsPhysical (rHost col L) cdrF (edges (rHost col L))) :
    IsPhysical (gHost (refLab col β) L) (refF j) (edges (gHost (refLab col β) L)) :=
  cdr_le_refined hbig j hj hphys

/-- Density of the refined classes from a degree bound. -/
theorem bigRef_of_deg {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ)
    (hcls : ∀ k, 4 * (Δ + 1) < gsz (refLab col β) k) : BigRef col β L := by
  intro k r p q s t
  set B : Finset V := {p, q, s, t}
  have hB : #B ≤ 4 := card_le_four
  have hc := gcard_good (lab := refLab col β) (k, r) B hdeg
  have hlt := hcls (k, r)
  have : 0 < #((univ.filter fun w => refLab col β w = (k, r)) \ (B ∪ B.biUnion (nbL L))) := by
    have : #B * (Δ + 1) ≤ 4 * (Δ + 1) := Nat.mul_le_mul_right _ hB
    omega
  obtain ⟨w, hw⟩ := card_pos.mp this
  obtain ⟨hl, ha⟩ := gmem_good hw
  simp only [refLab, Prod.mk.injEq] at hl
  exact ⟨w, hl.1, hl.2, ha p (by simp [B]), ha q (by simp [B]), ha s (by simp [B]),
    ha t (by simp [B])⟩

end CDRBicolour.Absorption.Refined