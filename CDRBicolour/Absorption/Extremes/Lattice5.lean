/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Extremes.Comb
public import CDRBicolour.Absorption.AACCount
public import CDRBicolour.Absorption.ResidualLattice
public import CDRBicolour.Absorption.ResidualHinge

/-!
# H2 for the five-type residual host (item 3, extremes)

`F5` = bicoloured types except `AAC`.  In a dense residual host `G = K_n − L` (`Dens9`), the
`F5`-lattice is the `cdrF`-lattice cut by one parity per point of `A`:

**`physical5`**: if `𝟏_{E(G)}` is in the `cdrF`-lattice of `G` and every `u ∈ A` has an even
number of `C`-neighbours in `G`, then `𝟏_{E(G)}` is in the `F5`-lattice of `G`.

Proof, in the quotient `Q = ℤ^{E}/Λ₅`:
* `I1`: the class of an `AAC` triangle `uvw` does not depend on `w` — call it `ρ(uv)`;
* `I2`: `2ρ(uv) = 0`;
* `I3`: `ρ(xy) + ρ(yz) + ρ(xz) = 0` on triangles of `G[A]`;
* hence a potential: `ρ(uv) = φ(u) + φ(v)`, `φ(u) = ρ(r y) + ρ(y u)` (`pot`);
* the class of any `cdrF`-combination `y` is `Σ_u k_u φ(u)` with `k_u ≡ #{w ∈ C : y(uw)}`
  (mod 2) (`decomp`); for `y = 𝟏_{E(G)}` every `k_u` is even and `2φ(u) = 0`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Extremes

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact

/-- The five bicoloured types other than `AAC`. -/
def F5 : Set (Multiset (Fin 3)) := {m | m ∈ cdrF ∧ m ≠ aac}

theorem F5_sub : F5 ⊆ cdrF := fun _ h => h.1

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

/-- Density: for every class and every set of at most nine points there is a new point of that
class adjacent in `G` to all of them. -/
def Dens9 (lab : V → Fin 3) (L : Finset (Sym2 V)) : Prop :=
  ∀ (k : Fin 3) (B : Finset V), B.card ≤ 9 → ∃ w, lab w = k ∧ w ∉ B ∧ ∀ p ∈ B, (rG L).Adj w p

/-- The `F5`-lattice of the residual host. -/
abbrev Lam5 (lab : V → Fin 3) (L : Finset (Sym2 V)) := lattice (rHost lab L) F5

theorem okTri_F5 {k na nb : ℕ} {T : Finset (Fin k)} (h : okTri na nb T) :
    T.val.map (mlab na nb) ∈ F5 := by
  obtain ⟨h3, hne, h2⟩ := h
  refine ⟨⟨by simp [h3], ?_⟩, hne⟩
  rw [← h2]; rfl

/-- An image combination of `F5`-triangles all of whose edges lie in `G` is in `Λ₅`. -/
theorem combV_mem {k na nb : ℕ} (φ : Fin k ↪ V) (l : List (ℤ × Finset (Fin k)))
    (hok : ∀ p ∈ l, okTri na nb p.2) (hlab : ∀ i, lab (φ i) = mlab na nb i)
    (hadj : ∀ p ∈ l, ∀ x ∈ p.2, ∀ y ∈ p.2, x ≠ y → (rG L).Adj (φ x) (φ y)) :
    combV φ l ∈ Lam5 lab L := by
  induction l with
  | nil => simp [combV, Submodule.zero_mem]
  | cons p l ih =>
    have hrest := ih (fun q hq => hok q (List.mem_cons_of_mem _ hq))
      (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    have hcomb : combV φ (p :: l) = p.1 • ind (triEdges (p.2.map φ)) + combV φ l := by
      simp [combV]
    rw [hcomb]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)) hrest
    have hp := hok p List.mem_cons_self
    refine ⟨by rw [card_map]; exact hp.1, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [mem_map] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hadj p List.mem_cons_self x' hx' y' hy' (fun h => hxy (by rw [h]))
    · show (p.2.map φ).val.map (rHost lab L).lab ∈ F5
      have : (p.2.map φ).val.map (rHost lab L).lab = p.2.val.map (mlab na nb) := by
        rw [map_val, Multiset.map_map]
        exact Multiset.map_congr rfl fun i _ => hlab i
      rw [this]; exact okTri_F5 hp

/-! ### The quotient and the three relations -/

/-- The class of a triangle in `ℤ^E / Λ₅`. -/
def cl (lab : V → Fin 3) (L : Finset (Sym2 V)) (T : Finset V) :
    (Sym2 V → ℤ) ⧸ Lam5 lab L :=
  Submodule.Quotient.mk (ind (triEdges T))

/-- Build an embedding of `Fin k` from an injective function. -/
def embOf {k : ℕ} (f : Fin k → V) (hf : Function.Injective f) : Fin k ↪ V := ⟨f, hf⟩

theorem mk_eq_of_comb {k : ℕ} (φ : Fin k ↪ V) {l₁ l₂ : List (ℤ × Finset (Fin k))}
    (h : combZ l₁ = combZ l₂) (hmem : combV φ l₁ ∈ Lam5 lab L) :
    (Submodule.Quotient.mk (combV φ l₂) : (Sym2 V → ℤ) ⧸ Lam5 lab L) = 0 := by
  rw [← comb_transport φ h]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hmem

/-- Pick a fresh point of class `k` adjacent to a list of at most nine points. -/
theorem pick (hD : Dens9 lab L) (k : Fin 3) (l : List V) (hl : l.length ≤ 9) :
    ∃ w, lab w = k ∧ l.Forall (fun p => w ≠ p) ∧ l.Forall (fun p => (rG L).Adj w p) := by
  obtain ⟨w, h1, h2, h3⟩ := hD k l.toFinset ((List.toFinset_card_le l).trans hl)
  refine ⟨w, h1, List.forall_iff_forall_mem.mpr fun p hp h => h2 ?_,
    List.forall_iff_forall_mem.mpr fun p hp => h3 p (List.mem_toFinset.mpr hp)⟩
  rw [h]; exact List.mem_toFinset.mpr hp

theorem adj_table {k : ℕ} (f : Fin k → V) (need : Fin k → Fin k → Bool)
    (hneed : ∀ x y, x ≠ y → need x y = true → (rG L).Adj (f x) (f y))
    (l : List (ℤ × Finset (Fin k))) (hl : ∀ p ∈ l, ∀ x ∈ p.2, ∀ y ∈ p.2, x ≠ y → need x y = true) :
    ∀ p ∈ l, ∀ x ∈ p.2, ∀ y ∈ p.2, x ≠ y → (rG L).Adj (f x) (f y) :=
  fun p hp x hx y hy hxy => hneed x y hxy (hl p hp x hx y hy hxy)

/-- Pairs used by `I1`: all but `{0,1}` and `{4,5}`. -/
def need1 (x y : Fin 7) : Bool := !((x = 0 ∧ y = 1) || (x = 1 ∧ y = 0) || (x = 4 ∧ y = 5) || (x = 5 ∧ y = 4))

set_option maxRecDepth 100000 in
theorem I1_need : ∀ p ∈ I1L, ∀ x ∈ p.2, ∀ y ∈ p.2, x ≠ y → need1 x y = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem I3_need : ∀ p ∈ I3L, ∀ x ∈ p.2, ∀ y ∈ p.2, x ≠ y →
    (fun (_ _ : Fin 9) => true) x y = true := by decide +kernel

theorem ne_of_lab {x y : V} (h : lab x ≠ lab y) : x ≠ y := fun e => h (by rw [e])

theorem inj_of_list {k : ℕ} (f : Fin k → V) (h : (List.ofFn f).Nodup) : Function.Injective f :=
  List.nodup_ofFn.mp h

/-- **I1 in `G`**: the class of an `AAC` triangle does not depend on its `C` point. -/
theorem rel1 (hD : Dens9 lab L) {u v w w' : V} (hu : lab u = 0) (hv : lab v = 0) (hw : lab w = 2)
    (hw' : lab w' = 2) (huv : u ≠ v) (hww : w ≠ w') (a1 : (rG L).Adj u w) (a2 : (rG L).Adj v w)
    (a3 : (rG L).Adj u w') (a4 : (rG L).Adj v w') :
    cl lab L {u, v, w} = cl lab L {u, v, w'} := by
  obtain ⟨b2, hb2, nb2, ab2⟩ := pick hD 1 [u, v, w, w'] (by simp)
  obtain ⟨b3, hb3, nb3, ab3⟩ := pick hD 1 [u, v, w, w', b2] (by simp)
  obtain ⟨c6, hc6, nc6, ac6⟩ := pick hD 2 [u, v, w, w', b2, b3] (by simp)
  simp only [List.forall_cons, List.Forall] at nb2 nb3 nc6 ab2 ab3 ac6
  obtain ⟨n1, n2, n3, n4⟩ := nb2
  obtain ⟨n5, n6, n7, n8, n9⟩ := nb3
  obtain ⟨n10, n11, n12, n13, n14, n15⟩ := nc6
  obtain ⟨d1, d2, d3, d4⟩ := ab2
  obtain ⟨d5, d6, d7, d8, d9⟩ := ab3
  obtain ⟨d10, d11, d12, d13, d14, d15⟩ := ac6
  set f : Fin 7 → V := ![u, v, b2, b3, w, w', c6] with hf_def
  have hf : Function.Injective f := by
    apply inj_of_list
    simp only [hf_def, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    have := a1.ne; have := a2.ne; have := a3.ne; have := a4.ne
    have h1 : u ≠ b2 := ne_of_lab (lab := lab) (by rw [hu, hb2]; decide)
    have h2 : v ≠ b2 := ne_of_lab (lab := lab) (by rw [hv, hb2]; decide)
    have h3 : u ≠ b3 := ne_of_lab (lab := lab) (by rw [hu, hb3]; decide)
    have h4 : v ≠ b3 := ne_of_lab (lab := lab) (by rw [hv, hb3]; decide)
    have h5 : u ≠ c6 := ne_of_lab (lab := lab) (by rw [hu, hc6]; decide)
    have h6 : v ≠ c6 := ne_of_lab (lab := lab) (by rw [hv, hc6]; decide)
    have h7 : b2 ≠ w := ne_of_lab (lab := lab) (by rw [hb2, hw]; decide)
    have h8 : b2 ≠ w' := ne_of_lab (lab := lab) (by rw [hb2, hw']; decide)
    have h9 : b3 ≠ w := ne_of_lab (lab := lab) (by rw [hb3, hw]; decide)
    have h10 : b3 ≠ w' := ne_of_lab (lab := lab) (by rw [hb3, hw']; decide)
    have h11 : b2 ≠ c6 := ne_of_lab (lab := lab) (by rw [hb2, hc6]; decide)
    have h12 : b3 ≠ c6 := ne_of_lab (lab := lab) (by rw [hb3, hc6]; decide)
    refine ⟨⟨huv, ?_⟩, ?_⟩ <;> simp_all [Ne.symm, eq_comm]
  have hlab : ∀ i, lab (f i) = mlab 2 2 i := by
    intro i; fin_cases i <;> simp [hf_def, mlab, hu, hv, hb2, hb3, hw, hw', hc6]
  have hneed : ∀ x y, x ≠ y → need1 x y = true → (rG L).Adj (f x) (f y) := by
    intro x y hxy hn
    fin_cases x <;> fin_cases y <;> simp (config := { decide := true }) [need1] at hxy hn ⊢ <;>
      simp only [hf_def, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val] <;>
      first | assumption | exact SimpleGraph.Adj.symm (by assumption)
  have hmem := combV_mem (embOf f hf) I1L I1L_ok hlab (adj_table f need1 hneed I1L I1_need)
  have h0 := mk_eq_of_comb (L := L) (embOf f hf) I1_model hmem
  have hR : combV (embOf f hf) I1R = ind (triEdges {u, v, w}) - ind (triEdges {u, v, w'}) := by
    simp [combV, I1R, embOf, hf_def, sub_eq_add_neg]
  unfold cl
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← hR]
  exact h0

/-- **I2 in `G`**: twice the class of an `AAC` triangle of `G` vanishes. -/
theorem rel2 (hD : Dens9 lab L) {u v w : V} (hu : lab u = 0) (hv : lab v = 0) (hw : lab w = 2)
    (huv : (rG L).Adj u v) (a1 : (rG L).Adj u w) (a2 : (rG L).Adj v w) :
    (2 : ℤ) • cl lab L {u, v, w} = 0 := by
  obtain ⟨b2, hb2, nb2, ab2⟩ := pick hD 1 [u, v, w] (by simp)
  obtain ⟨b3, hb3, nb3, ab3⟩ := pick hD 1 [u, v, w, b2] (by simp)
  obtain ⟨c5, hc5, nc5, ac5⟩ := pick hD 2 [u, v, w, b2, b3] (by simp)
  obtain ⟨c6, hc6, nc6, ac6⟩ := pick hD 2 [u, v, w, b2, b3, c5] (by simp)
  simp only [List.forall_cons, List.Forall] at nb2 nb3 nc5 nc6 ab2 ab3 ac5 ac6
  obtain ⟨n1, n2, n3⟩ := nb2
  obtain ⟨n4, n5, n6, n7⟩ := nb3
  obtain ⟨n8, n9, n10, n11, n12⟩ := nc5
  obtain ⟨n13, n14, n15, n16, n17, n18⟩ := nc6
  obtain ⟨d1, d2, d3⟩ := ab2
  obtain ⟨d4, d5, d6, d7⟩ := ab3
  obtain ⟨d8, d9, d10, d11, d12⟩ := ac5
  obtain ⟨d13, d14, d15, d16, d17, d18⟩ := ac6
  set f : Fin 7 → V := ![u, v, b2, b3, w, c5, c6] with hf_def
  have hf : Function.Injective f := by
    apply inj_of_list
    simp only [hf_def, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    have := huv.ne; have := a1.ne; have := a2.ne
    have h1 : u ≠ b2 := ne_of_lab (lab := lab) (by rw [hu, hb2]; decide)
    have h2 : v ≠ b2 := ne_of_lab (lab := lab) (by rw [hv, hb2]; decide)
    have h3 : u ≠ b3 := ne_of_lab (lab := lab) (by rw [hu, hb3]; decide)
    have h4 : v ≠ b3 := ne_of_lab (lab := lab) (by rw [hv, hb3]; decide)
    have h5 : u ≠ c5 := ne_of_lab (lab := lab) (by rw [hu, hc5]; decide)
    have h6 : v ≠ c5 := ne_of_lab (lab := lab) (by rw [hv, hc5]; decide)
    have h7 : u ≠ c6 := ne_of_lab (lab := lab) (by rw [hu, hc6]; decide)
    have h8 : v ≠ c6 := ne_of_lab (lab := lab) (by rw [hv, hc6]; decide)
    have h9 : b2 ≠ w := ne_of_lab (lab := lab) (by rw [hb2, hw]; decide)
    have h10 : b3 ≠ w := ne_of_lab (lab := lab) (by rw [hb3, hw]; decide)
    have h11 : b2 ≠ c5 := ne_of_lab (lab := lab) (by rw [hb2, hc5]; decide)
    have h12 : b3 ≠ c5 := ne_of_lab (lab := lab) (by rw [hb3, hc5]; decide)
    have h13 : b2 ≠ c6 := ne_of_lab (lab := lab) (by rw [hb2, hc6]; decide)
    have h14 : b3 ≠ c6 := ne_of_lab (lab := lab) (by rw [hb3, hc6]; decide)
    refine ⟨⟨huv.ne, ?_⟩, ?_⟩ <;> simp_all [Ne.symm, eq_comm]
  have hlab : ∀ i, lab (f i) = mlab 2 2 i := by
    intro i; fin_cases i <;> simp [hf_def, mlab, hu, hv, hb2, hb3, hw, hc5, hc6]
  have hneed : ∀ x y, x ≠ y → (fun (_ _ : Fin 7) => true) x y = true → (rG L).Adj (f x) (f y) := by
    intro x y hxy _
    fin_cases x <;> fin_cases y <;> simp (config := { decide := true }) at hxy ⊢ <;>
      simp only [hf_def, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val] <;>
      first | assumption | exact SimpleGraph.Adj.symm (by assumption)
  have hmem := combV_mem (embOf f hf) I2L I2L_ok hlab
    (adj_table f _ hneed I2L (fun _ _ _ _ _ _ _ => rfl))
  have h0 := mk_eq_of_comb (L := L) (embOf f hf) I2_model hmem
  have hR : combV (embOf f hf) I2R = (2 : ℤ) • ind (triEdges {u, v, w}) := by
    simp [combV, I2R, embOf, hf_def]
  unfold cl
  rw [← Submodule.Quotient.mk_smul, ← hR]
  exact h0

/-- **I3 in `G`**: the classes of three `AAC` triangles over a triangle of `G[A]` sum to zero. -/
theorem rel3 (hD : Dens9 lab L) {x y z : V} (hx : lab x = 0) (hy : lab y = 0) (hz : lab z = 0)
    (axy : (rG L).Adj x y) (ayz : (rG L).Adj y z) (axz : (rG L).Adj x z) :
    ∃ w₁ w₂ w₃ : V, lab w₁ = 2 ∧ lab w₂ = 2 ∧ lab w₃ = 2 ∧
      (rG L).Adj x w₁ ∧ (rG L).Adj y w₁ ∧ (rG L).Adj y w₂ ∧ (rG L).Adj z w₂ ∧
      (rG L).Adj x w₃ ∧ (rG L).Adj z w₃ ∧
      cl lab L {x, y, w₁} + cl lab L {y, z, w₂} + cl lab L {x, z, w₃} = 0 := by
  obtain ⟨b3, hb3, nb3, ab3⟩ := pick hD 1 [x, y, z] (by simp)
  obtain ⟨b4, hb4, nb4, ab4⟩ := pick hD 1 [x, y, z, b3] (by simp)
  obtain ⟨b5, hb5, nb5, ab5⟩ := pick hD 1 [x, y, z, b3, b4] (by simp)
  obtain ⟨c6, hc6, nc6, ac6⟩ := pick hD 2 [x, y, z, b3, b4, b5] (by simp)
  obtain ⟨c7, hc7, nc7, ac7⟩ := pick hD 2 [x, y, z, b3, b4, b5, c6] (by simp)
  obtain ⟨c8, hc8, nc8, ac8⟩ := pick hD 2 [x, y, z, b3, b4, b5, c6, c7] (by simp)
  simp only [List.forall_cons, List.Forall] at nb3 nb4 nb5 nc6 nc7 nc8 ab3 ab4 ab5 ac6 ac7 ac8
  obtain ⟨n1, n2, n3⟩ := nb3
  obtain ⟨n4, n5, n6, n7⟩ := nb4
  obtain ⟨n8, n9, n10, n11, n12⟩ := nb5
  obtain ⟨n13, n14, n15, n16, n17, n18⟩ := nc6
  obtain ⟨n19, n20, n21, n22, n23, n24, n25⟩ := nc7
  obtain ⟨n26, n27, n28, n29, n30, n31, n32, n33⟩ := nc8
  obtain ⟨d1, d2, d3⟩ := ab3
  obtain ⟨d4, d5, d6, d7⟩ := ab4
  obtain ⟨d8, d9, d10, d11, d12⟩ := ab5
  obtain ⟨d13, d14, d15, d16, d17, d18⟩ := ac6
  obtain ⟨d19, d20, d21, d22, d23, d24, d25⟩ := ac7
  obtain ⟨d26, d27, d28, d29, d30, d31, d32, d33⟩ := ac8
  set f : Fin 9 → V := ![x, y, z, b3, b4, b5, c6, c7, c8] with hf_def
  have hf : Function.Injective f := by
    apply inj_of_list
    simp only [hf_def, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    have := axy.ne; have := ayz.ne; have := axz.ne
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp_all [Ne.symm, eq_comm]
  have hlab : ∀ i, lab (f i) = mlab 3 3 i := by
    intro i; fin_cases i <;> simp [hf_def, mlab, hx, hy, hz, hb3, hb4, hb5, hc6, hc7, hc8]
  have hneed : ∀ p q, p ≠ q → (fun (_ _ : Fin 9) => true) p q = true →
      (rG L).Adj (f p) (f q) := by
    intro p q hpq _
    fin_cases p <;> fin_cases q <;> simp (config := { decide := true }) at hpq ⊢ <;>
      simp only [hf_def, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val] <;>
      first | assumption | exact SimpleGraph.Adj.symm (by assumption)
  have hmem := combV_mem (embOf f hf) I3L I3L_ok hlab (adj_table f _ hneed I3L I3_need)
  have h0 := mk_eq_of_comb (L := L) (embOf f hf) I3_model hmem
  have hR : combV (embOf f hf) I3R =
      ind (triEdges {x, y, c6}) + ind (triEdges {y, z, c7}) + ind (triEdges {x, z, c8}) := by
    simp [combV, I3R, embOf, hf_def, add_assoc]
  refine ⟨c6, c7, c8, hc6, hc7, hc8, d13.symm, d14.symm, d20.symm, d21.symm, d26.symm, d28.symm, ?_⟩
  unfold cl
  rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← hR]
  exact h0

/-! ### The edge class `ρ` and the potential -/

open Classical in
/-- A `C` point adjacent to `u` and `v`, if any. -/
def wsel (lab : V → Fin 3) (L : Finset (Sym2 V)) (u v : V) : V :=
  if h : ∃ w, lab w = 2 ∧ (rG L).Adj u w ∧ (rG L).Adj v w then h.choose else u

/-- The class of an `AA` edge: the class of any `AAC` triangle on it. -/
def rho (lab : V → Fin 3) (L : Finset (Sym2 V)) (u v : V) : (Sym2 V → ℤ) ⧸ Lam5 lab L :=
  cl lab L {u, v, wsel lab L u v}

theorem wsel_spec (hD : Dens9 lab L) (u v : V) :
    lab (wsel lab L u v) = 2 ∧ (rG L).Adj u (wsel lab L u v) ∧ (rG L).Adj v (wsel lab L u v) := by
  have h : ∃ w, lab w = 2 ∧ (rG L).Adj u w ∧ (rG L).Adj v w := by
    obtain ⟨w, hw, -, hadj⟩ := pick hD 2 [u, v] (by simp)
    simp only [List.forall_cons, List.Forall] at hadj
    exact ⟨w, hw, hadj.1.symm, hadj.2.symm⟩
  unfold wsel; rw [dif_pos h]; exact h.choose_spec

theorem rho_eq (hD : Dens9 lab L) {u v w : V} (hu : lab u = 0) (hv : lab v = 0) (hw : lab w = 2)
    (huv : u ≠ v) (a1 : (rG L).Adj u w) (a2 : (rG L).Adj v w) : rho lab L u v = cl lab L {u, v, w} := by
  obtain ⟨h1, h2, h3⟩ := wsel_spec hD u v
  unfold rho
  by_cases hww : wsel lab L u v = w
  · rw [hww]
  · exact rel1 hD hu hv h1 hw huv hww h2 h3 a1 a2

theorem rho_symm (hD : Dens9 lab L) {u v : V} (hu : lab u = 0) (hv : lab v = 0) (huv : u ≠ v) :
    rho lab L u v = rho lab L v u := by
  obtain ⟨h1, h2, h3⟩ := wsel_spec hD u v
  rw [rho_eq hD hu hv h1 huv h2 h3, rho_eq hD hv hu h1 huv.symm h3 h2, insert_comm]

theorem two_rho (hD : Dens9 lab L) {u v : V} (hu : lab u = 0) (hv : lab v = 0)
    (huv : (rG L).Adj u v) : (2 : ℤ) • rho lab L u v = 0 := by
  obtain ⟨h1, h2, h3⟩ := wsel_spec hD u v
  exact rel2 hD hu hv h1 huv h2 h3

theorem neg_rho (hD : Dens9 lab L) {u v : V} (hu : lab u = 0) (hv : lab v = 0)
    (huv : (rG L).Adj u v) : -rho lab L u v = rho lab L u v := by
  have h := two_rho hD hu hv huv
  rw [two_smul] at h
  exact (neg_eq_of_add_eq_zero_right h)

/-- `ρ(xz) = ρ(xy) + ρ(yz)` on a triangle of `G[A]`. -/
theorem tri_rho (hD : Dens9 lab L) {x y z : V} (hx : lab x = 0) (hy : lab y = 0) (hz : lab z = 0)
    (axy : (rG L).Adj x y) (ayz : (rG L).Adj y z) (axz : (rG L).Adj x z) :
    rho lab L x z = rho lab L x y + rho lab L y z := by
  obtain ⟨w₁, w₂, w₃, h1, h2, h3, a1, a2, a3, a4, a5, a6, hrel⟩ := rel3 hD hx hy hz axy ayz axz
  rw [← rho_eq hD hx hy h1 axy.ne a1 a2, ← rho_eq hD hy hz h2 ayz.ne a3 a4,
    ← rho_eq hD hx hz h3 axz.ne a5 a6] at hrel
  have : rho lab L x z = -(rho lab L x y + rho lab L y z) := eq_neg_of_add_eq_zero_right hrel
  rw [this, neg_add, neg_rho hD hx hy axy, neg_rho hD hy hz ayz]

open Classical in
/-- A point of `A` adjacent to `r` and `u`, distinct from both. -/
def ysel (lab : V → Fin 3) (L : Finset (Sym2 V)) (r u : V) : V :=
  if h : ∃ y, lab y = 0 ∧ y ≠ r ∧ y ≠ u ∧ (rG L).Adj y r ∧ (rG L).Adj y u then h.choose else r

theorem ysel_spec (hD : Dens9 lab L) (r u : V) :
    lab (ysel lab L r u) = 0 ∧ ysel lab L r u ≠ r ∧ ysel lab L r u ≠ u ∧
      (rG L).Adj (ysel lab L r u) r ∧ (rG L).Adj (ysel lab L r u) u := by
  have h : ∃ y, lab y = 0 ∧ y ≠ r ∧ y ≠ u ∧ (rG L).Adj y r ∧ (rG L).Adj y u := by
    obtain ⟨y, hy, hne, hadj⟩ := pick hD 0 [r, u] (by simp)
    simp only [List.forall_cons, List.Forall] at hne hadj
    exact ⟨y, hy, hne.1, hne.2, hadj.1, hadj.2⟩
  unfold ysel; rw [dif_pos h]; exact h.choose_spec

/-- The potential. -/
def phi (lab : V → Fin 3) (L : Finset (Sym2 V)) (r u : V) : (Sym2 V → ℤ) ⧸ Lam5 lab L :=
  if u = r then 0 else rho lab L r (ysel lab L r u) + rho lab L (ysel lab L r u) u

theorem phi_any (hD : Dens9 lab L) {r u y : V} (hr : lab r = 0) (hu : lab u = 0) (hy : lab y = 0)
    (hur : u ≠ r) (hyr : y ≠ r) (hyu : y ≠ u) (a1 : (rG L).Adj r y) (a2 : (rG L).Adj y u) :
    phi lab L r u = rho lab L r y + rho lab L y u := by
  obtain ⟨g0, g1, g2, g3, g4⟩ := ysel_spec hD r u
  set y₀ := ysel lab L r u
  have key : ∀ t, lab t = 0 → t ≠ r → t ≠ u → (rG L).Adj r t → (rG L).Adj t u →
      ∀ z, lab z = 0 → (rG L).Adj z r → (rG L).Adj z u → (rG L).Adj z t →
        rho lab L r t + rho lab L t u = rho lab L r z + rho lab L z u := by
    intro t ht htr htu b1 b2 z hz c1 c2 c3
    rw [tri_rho hD hr hz ht c1.symm c3 b1, tri_rho hD ht hz hu c3.symm c2 b2,
      rho_symm hD hz ht c3.ne]
    have := two_rho hD ht hz c3.symm
    rw [two_smul] at this
    calc rho lab L r z + rho lab L t z + (rho lab L t z + rho lab L z u)
        = rho lab L r z + rho lab L z u + (rho lab L t z + rho lab L t z) := by abel
      _ = rho lab L r z + rho lab L z u := by rw [this, add_zero]
  obtain ⟨z, hz, -, hadj⟩ := pick hD 0 [r, u, y, y₀] (by simp)
  simp only [List.forall_cons, List.Forall] at hadj
  obtain ⟨c1, c2, c3, c4⟩ := hadj
  unfold phi; rw [if_neg hur]
  rw [key y₀ g0 g1 g2 g3.symm g4 z hz c1 c2 c4, key y hy hyr hyu a1 a2 z hz c1 c2 c3]

theorem two_phi (hD : Dens9 lab L) {r u : V} (hr : lab r = 0) (hu : lab u = 0) :
    (2 : ℤ) • phi lab L r u = 0 := by
  unfold phi
  split_ifs with h
  · simp
  · obtain ⟨g0, g1, g2, g3, g4⟩ := ysel_spec hD r u
    rw [smul_add, two_rho hD hr g0 g3.symm, two_rho hD g0 hu g4, add_zero]

/-- **The potential**: `ρ(uv) = φ(u) + φ(v)` on the edges of `G[A]`. -/
theorem pot (hD : Dens9 lab L) {r u v : V} (hr : lab r = 0) (hu : lab u = 0) (hv : lab v = 0)
    (huv : (rG L).Adj u v) : rho lab L u v = phi lab L r u + phi lab L r v := by
  by_cases hur : u = r
  · subst hur
    obtain ⟨g0, g1, g2, g3, g4⟩ := ysel_spec hD u v
    unfold phi; rw [if_pos rfl, if_neg huv.ne.symm, zero_add]
    exact tri_rho hD hu g0 hv g3.symm g4 huv
  by_cases hvr : v = r
  · subst hvr
    obtain ⟨g0, g1, g2, g3, g4⟩ := ysel_spec hD v u
    rw [rho_symm hD hu hv huv.ne]
    unfold phi; rw [if_pos rfl, if_neg hur, add_zero]
    exact tri_rho hD hv g0 hu g3.symm g4 huv.symm
  obtain ⟨z, hz, hne, hadj⟩ := pick hD 0 [r, u, v] (by simp)
  simp only [List.forall_cons, List.Forall] at hne hadj
  obtain ⟨n1, n2, n3⟩ := hne
  obtain ⟨c1, c2, c3⟩ := hadj
  rw [phi_any hD hr hu hz hur n1 n2 c1.symm c2, phi_any hD hr hv hz hvr n1 n3 c1.symm c3,
    tri_rho hD hu hz hv c2.symm c3 huv, rho_symm hD hz hu n2]
  have := two_rho hD hr hz c1.symm
  rw [two_smul] at this
  calc rho lab L u z + rho lab L z v
      = rho lab L r z + rho lab L r z + (rho lab L u z + rho lab L z v) := by rw [this, zero_add]
    _ = rho lab L r z + rho lab L u z + (rho lab L r z + rho lab L z v) := by abel

/-! ### Decomposition of the `cdrF`-lattice modulo `Λ₅` -/

/-- Number of `C` neighbours of `u` counted by an edge function. -/
def piC (lab : V → Fin 3) (u : V) (y : Sym2 V → ℤ) : ℤ :=
  ∑ w ∈ univ.filter (fun w => lab w = 2), y s(u, w)

theorem piC_add (u : V) (y y' : Sym2 V → ℤ) : piC lab u (y + y') = piC lab u y + piC lab u y' := by
  simp [piC, sum_add_distrib]

theorem piC_smul (u : V) (r : ℤ) (y : Sym2 V → ℤ) : piC lab u (r • y) = r * piC lab u y := by
  simp [piC, mul_sum]

theorem mem_triEdges_pair {T : Finset V} {u w : V} :
    s(u, w) ∈ triEdges T ↔ u ∈ T ∧ w ∈ T ∧ u ≠ w := by
  simp [triEdges, Sym2.mk_isDiag_iff, and_assoc]

theorem piC_tri {u : V} (hu : lab u = 0) (T : Finset V) :
    piC lab u (ind (triEdges T)) =
      if u ∈ T then ((T.filter fun w => lab w = 2).card : ℤ) else 0 := by
  unfold piC ind
  calc _ = ∑ w ∈ univ.filter (fun w => lab w = 2), (if u ∈ T ∧ w ∈ T then (1 : ℤ) else 0) := by
        refine sum_congr rfl fun w hw => ?_
        have hw2 : lab w = 2 := (mem_filter.mp hw).2
        have huw : u ≠ w := fun h => by rw [h, hw2] at hu; exact absurd hu (by decide)
        by_cases h : u ∈ T ∧ w ∈ T
        · rw [if_pos (mem_triEdges_pair.mpr ⟨h.1, h.2, huw⟩), if_pos h]
        · rw [if_neg (fun h' => h ⟨(mem_triEdges_pair.mp h').1, (mem_triEdges_pair.mp h').2.1⟩),
            if_neg h]
    _ = _ := by
        split_ifs with hT
        · simp only [hT, true_and]
          rw [sum_boole, filter_filter]
          congr 2
          ext w; simp [and_comm]
        · simp [hT]

theorem aac_shape {T : Finset V} (hT : IsAllowed (rHost lab L) cdrF T)
    (haac : T.val.map lab = aac) :
    ∃ u v w, T = {u, v, w} ∧ lab u = 0 ∧ lab v = 0 ∧ lab w = 2 ∧ (rG L).Adj u v ∧
      (rG L).Adj u w ∧ (rG L).Adj v w := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp hT.1
  have adj : ∀ x ∈ ({p, q, r} : Finset V), ∀ y ∈ ({p, q, r} : Finset V), x ≠ y →
      (rG L).Adj x y := hT.2.1
  have apq := adj p (by simp) q (by simp) hpq
  have apr := adj p (by simp) r (by simp) hpr
  have aqr := adj q (by simp) r (by simp) hqr
  rw [show ({p, q, r} : Finset V).val.map lab = ({lab p, lab q, lab r} : Multiset (Fin 3)) from
    val_map_triple lab hpq hpr.symm hqr.symm] at haac
  have key : ∀ x y z : Fin 3, ({x, y, z} : Multiset (Fin 3)) = aac →
      (x = 0 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 2 ∧ z = 0) ∨ (x = 2 ∧ y = 0 ∧ z = 0) := by
    unfold aac; decide
  rcases key _ _ _ haac with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨p, q, r, rfl, h1, h2, h3, apq, apr, aqr⟩
  · exact ⟨p, r, q, by ext; simp; tauto, h1, h3, h2, apr, apq, aqr.symm⟩
  · exact ⟨q, r, p, by ext; simp; tauto, h2, h3, h1, aqr, apq.symm, apr.symm⟩

theorem count_two_even {T : Finset V} {u : V} (hu : lab u = 0) (huT : u ∈ T)
    (hT : T.val.map lab ∈ cdrF) (hne : T.val.map lab ≠ aac) :
    Even ((T.filter fun w => lab w = 2).card : ℤ) := by
  have hc : (T.filter fun w => lab w = 2).card = (T.val.map lab).count 2 := by
    rw [Multiset.count_map, card_def, filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  have h0 : 0 < (T.val.map lab).count 0 :=
    Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨u, huT, hu⟩)
  rw [hc]
  rcases type_cases hT with ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ |
    ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩
  · rw [a2]; decide
  · exfalso; apply hne
    ext k; fin_cases k <;> simp [aac, a0, a1, a2]
  · omega
  · rw [a2]; decide
  · rw [a2]; decide
  · omega

/-- **Decomposition**: the class of any element `y` of the `cdrF`-lattice of `G` is
`Σ_x k_x φ(x)`, with `k` supported on `A` and `k_x ≡ piC x y` (mod 2) on `A`. -/
theorem decomp (hD : Dens9 lab L) {r : V} (hr : lab r = 0) {y : Sym2 V → ℤ}
    (hy : y ∈ lattice (rHost lab L) cdrF) :
    ∃ k : V → ℤ, (Submodule.Quotient.mk y : (Sym2 V → ℤ) ⧸ Lam5 lab L) =
      ∑ x, k x • phi lab L r x ∧ (∀ x, lab x ≠ 0 → k x = 0) ∧
        ∀ x, lab x = 0 → Even (k x - piC lab x y) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨T, hT, rfl⟩ := hz
    by_cases haac : T.val.map lab = aac
    · obtain ⟨u, v, w, rfl, hu, hv, hw, auv, auw, avw⟩ := aac_shape hT haac
      refine ⟨Pi.single u 1 + Pi.single v 1, ?_, ?_, ?_⟩
      · simp only [Pi.add_apply, add_smul, sum_add_distrib]
        rw [sum_eq_single u (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp),
          sum_eq_single v (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp)]
        simp only [Pi.single_eq_same, one_smul]
        rw [← pot hD hr hu hv auv, rho_eq hD hu hv hw auv.ne auw avw]
        rfl
      · intro x hx
        have hxu : x ≠ u := fun h => hx (h ▸ hu)
        have hxv : x ≠ v := fun h => hx (h ▸ hv)
        simp [Pi.single_apply, hxu, hxv]
      · intro x hx
        rw [piC_tri hx]
        have hfil : (({u, v, w} : Finset V).filter fun w => lab w = 2) = {w} := by
          ext t
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨h | h | h, ht⟩
            · rw [h, hu] at ht; exact absurd ht (by decide)
            · rw [h, hv] at ht; exact absurd ht (by decide)
            · exact h
          · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hw⟩
        rw [hfil, card_singleton]
        have hxw : x ≠ w := fun h => by rw [h, hw] at hx; exact absurd hx (by decide)
        by_cases hxu : x = u
        · subst hxu
          simp [Pi.single_apply, auv.ne.symm]
        by_cases hxv : x = v
        · subst hxv
          simp [Pi.single_apply, hxu]
        · simp [Pi.single_apply, hxu, hxv, hxw]
    · refine ⟨0, ?_, fun _ _ => rfl, ?_⟩
      · simp only [Pi.zero_apply, zero_smul, sum_const_zero]
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨T, ⟨hT.1, hT.2.1, hT.2.2, haac⟩, rfl⟩
      · intro x hx
        rw [piC_tri hx]
        split_ifs with hxT
        · simpa using (count_two_even hx hxT hT.2.2 haac).neg
        · simp
  | zero => exact ⟨0, by simp, fun _ _ => rfl, fun x _ => by simp [piC]⟩
  | add z z' _ _ ih ih' =>
    obtain ⟨k, hk, hk0, hkp⟩ := ih
    obtain ⟨k', hk', hk0', hkp'⟩ := ih'
    refine ⟨k + k', ?_, fun x hx => by simp [hk0 x hx, hk0' x hx], fun x hx => ?_⟩
    · rw [Submodule.Quotient.mk_add, hk, hk', ← sum_add_distrib]
      simp [add_smul]
    · rw [piC_add, Pi.add_apply]
      have := (hkp x hx).add (hkp' x hx)
      convert this using 1; ring
  | smul t z _ ih =>
    obtain ⟨k, hk, hk0, hkp⟩ := ih
    refine ⟨t • k, ?_, fun x hx => by simp [hk0 x hx], fun x hx => ?_⟩
    · rw [Submodule.Quotient.mk_smul, hk, smul_sum]
      simp [mul_smul]
    · rw [piC_smul, Pi.smul_apply, smul_eq_mul, ← mul_sub]
      exact (hkp x hx).mul_left t

/-- **H2 for the five-type residual host**: if `𝟏_{E(G)}` is `cdrF`-physical and every point of
`A` has an even number of `C` neighbours in `G`, then it is `F5`-physical. -/
theorem physical5 [DecidableRel (rG L).Adj] (hD : Dens9 lab L) {r : V} (hr : lab r = 0)
    (hcdr : IsPhysical (rHost lab L) cdrF (edges (rHost lab L)))
    (hpar : ∀ u, lab u = 0 → Even ((univ.filter fun w => lab w = 2 ∧ (rG L).Adj u w).card)) :
    IsPhysical (rHost lab L) F5 (edges (rHost lab L)) := by
  obtain ⟨k, hk, hk0, hkp⟩ := decomp hD hr hcdr
  have hpi : ∀ x, lab x = 0 → Even (piC lab x (ind (edges (rHost lab L)))) := by
    intro x hx
    have : piC lab x (ind (edges (rHost lab L))) =
        ((univ.filter fun w => lab w = 2 ∧ (rG L).Adj x w).card : ℤ) := by
      unfold piC ind
      calc _ = ∑ w ∈ univ.filter (fun w => lab w = 2), (if (rG L).Adj x w then (1 : ℤ) else 0) :=
            sum_congr rfl fun w _ => by
              by_cases h : (rG L).Adj x w
              · rw [if_pos (mem_edges_rHost.mpr h), if_pos h]
              · rw [if_neg (fun h' => h (mem_edges_rHost.mp h')), if_neg h]
        _ = _ := by
            rw [sum_boole, filter_filter]
    rw [this]; exact_mod_cast (hpar x hx).natCast
  have hzero : ∀ x, k x • phi lab L r x = 0 := by
    intro x
    by_cases hx : lab x = 0
    · obtain ⟨j, hj⟩ := (hkp x hx).add (hpi x hx)
      have : k x = 2 * j := by rw [sub_add_cancel] at hj; rw [hj]; ring
      rw [this, mul_comm, mul_smul, two_phi hD hr hx, smul_zero]
    · rw [hk0 x hx, zero_smul]
  have : (Submodule.Quotient.mk (ind (edges (rHost lab L))) : (Sym2 V → ℤ) ⧸ Lam5 lab L) = 0 := by
    rw [hk]; exact sum_eq_zero fun x _ => hzero x
  exact (Submodule.Quotient.mk_eq_zero _).mp this

end CDRBicolour.Absorption.Extremes
