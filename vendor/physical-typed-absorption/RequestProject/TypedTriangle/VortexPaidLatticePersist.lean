/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexEdgeVertexCommute
public import RequestProject.TypedTriangle.VortexRestrictedEdgeLoad
public import RequestProject.TypedTriangle.CertDispersal
public import RequestProject.TypedTriangle.RestrictedVertexBounds
@[expose] public section

/-! Reticular portion of PreparedCore on the actual paid child. The two
sparse-edge contracts are supplied here to isolate the integer transport;
their quantitative discharge belongs to the H3/H4 and degree lemmas. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem paid_lattice_persist_of_sparse_contracts {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V))
    (α : ℝ) (h N₀ : ℕ) (β : ℝ)
    (P : Dispersal.PreparedCore H.G H.lab F α h N₀ β)
    (hFull : ∀ y : Sym2 V → ℤ,
      y ∈ lattice (subHost H (edges H \ B)) F ↔
        y ∈ lattice H F ∧ ∀ e ∈ B, y e = 0)
    (hRestricted : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
      ∀ z : Sym2 (Survivors Z) → ℤ,
        z ∈ lattice (subHost (restrictedHost H Z)
            (edges (restrictedHost H Z) \ restrictEdgeSet Z B)) F ↔
          z ∈ lattice (restrictedHost H Z) F ∧
            ∀ e ∈ restrictEdgeSet Z B, z e = 0) :
    ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
      ∀ y ∈ lattice (subHost H (edges H \ B)) F,
        (∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) →
          Dispersal.restr Z y ∈ lattice
            (restrictedHost (subHost H (edges H \ B)) Z) F := by
  intro Z hZ y hy hvan
  obtain ⟨hyRaw, hyB⟩ := (hFull y).mp hy
  have hRaw : Dispersal.restr Z y ∈ lattice (restrictedHost H Z) F :=
    P.lattice_persist Z hZ y hyRaw hvan
  have hZero := restricted_edge_zero Z B y hyB
  rw [restricted_paid_child_eq_paid_restricted H Z B]
  exact (hRestricted Z hZ (Dispersal.restr Z y)).mpr ⟨hRaw, hZero⟩

set_option backward.isDefEq.respectTransparency false in
theorem paid_lattice_persist_after_sparse_edge_deletion (α : ℝ) (h : ℕ)
    (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ (V I : Type) [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (β : ℝ),
        β ≤ 1 / 2 →
        n₀ ≤ Fintype.card V →
        CommonNbrCond H F α → HingeCond H F α h →
        Dispersal.PreparedCore H.G H.lab F α h n₀ β →
        ∀ B : Finset (Sym2 V),
          (∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤
            η / 2 * Fintype.card V) →
          ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
            ∀ y ∈ lattice (subHost H (edges H \ B)) F,
              (∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) →
                Dispersal.restr Z y ∈ lattice
                  (restrictedHost (subHost H (edges H \ B)) Z) F := by
  obtain ⟨η, hη, n₀, hSparse⟩ := sparse_edge_deletion_host α h hα
  refine ⟨η, hη, n₀, ?_⟩
  intro V I _ H F β hβ hn h3 h4 P B hB Z hZ y hy hvan
  have hRawDeg : ∀ x,
      (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤ η * Fintype.card V := by
    intro x
    have hx := hB x
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  have hFull := hSparse V I H F hn h3 h4 B hRawDeg
  have hRestricted : ∀ Z' : Finset V,
      (Z'.card : ℝ) ≤ β * Fintype.card V →
      ∀ z : Sym2 (Survivors Z') → ℤ,
        z ∈ lattice (subHost (restrictedHost H Z')
            (edges (restrictedHost H Z') \ restrictEdgeSet Z' B)) F ↔
          z ∈ lattice (restrictedHost H Z') F ∧
            ∀ e ∈ restrictEdgeSet Z' B, z e = 0 := by
    intro Z' hZ' z
    letI : DecidableEq (Survivors Z') := Classical.decEq _
    have hCard : (Fintype.card (Survivors Z') : ℝ) + Z'.card = Fintype.card V := by
      exact_mod_cast card_survivors_add_card Z'
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hZN : (Z'.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hβ hn0
      nlinarith
    have hHalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors Z') := by
      linarith
    convert hSparse (Survivors Z') I (restrictedHost H Z') F
      (P.order Z' hZ') (P.h3 Z' hZ') (P.h4 Z' hZ') (restrictEdgeSet Z' B)
      (by
        intro x
        have hprod : 0 ≤ η * ((Fintype.card (Survivors Z') : ℝ) - Fintype.card V / 2) :=
          mul_nonneg hη.le (sub_nonneg.mpr hHalf)
        calc
          _ ≤ ((B.filter (fun e => x.1 ∈ e)).card : ℝ) := by
            norm_cast
            apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
            · intro e he
              obtain ⟨heB, hxe⟩ := Finset.mem_filter.mp he
              exact Finset.mem_filter.mpr ⟨(mem_restrictEdgeSet Z' B e).mp heB,
                Sym2.mem_map.mpr ⟨x, hxe, rfl⟩⟩
            · exact (Sym2.map.injective Subtype.val_injective).injOn
          _ ≤ η / 2 * Fintype.card V := hB x.1
          _ ≤ η * Fintype.card (Survivors Z') := by nlinarith) z using 1
    constructor <;> intro hz <;> convert hz using 1 <;>
      (congr 2 <;> apply Finset.ext <;> intro e <;> simp only [Finset.mem_sdiff])
  exact paid_lattice_persist_of_sparse_contracts H F B α h n₀ β P hFull
    hRestricted Z hZ y hy hvan

#print axioms paid_lattice_persist_of_sparse_contracts
#print axioms paid_lattice_persist_after_sparse_edge_deletion

end TypedTriangle.Vortex
