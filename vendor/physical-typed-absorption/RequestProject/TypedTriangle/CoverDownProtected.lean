/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CoverDown
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# Cover-down con grafo protegido (guía V5, §8)

Adaptador sobre `cover_down`: dado un grafo protegido `P` (conjunto de aristas de grado
máximo `≤ f`) disjunto del input `U`, se filtran los candidatos

`Cand_P(e) = Cand(e) ∖ (N_P(u) ∪ N_P(v))`,   `e = uv`,

perdiendo a lo sumo `2f` centros por arista. De `|U| + q(2d + 4q + 2f) < q|Cand(e)|` se
obtiene la ventana del lema existente para `Cand_P`. Se conservan el packing, la cobertura
de `U` y la cota de grado `≤ 2d + 2q`; ahora además todas las aristas del packing evitan `P`.
La hipótesis `U ∩ P = ∅` es una condición de la operación (no se puede cubrir una base
protegida y a la vez evitarla), no una hipótesis nueva de T.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Candidatos que no crean un ala protegida. -/
def candProt (P : Finset (Sym2 V)) (Cand : Sym2 V → Finset V) (e : Sym2 V) : Finset V :=
  (Cand e).filter (fun w => ∀ x ∈ e, s(x, w) ∉ P)

/-- Centros perdidos: a lo sumo `2f`. -/
lemma card_cand_sub_candProt_le (P : Finset (Sym2 V)) (Cand : Sym2 V → Finset V) {f : ℕ}
    (hP : ∀ x, (P.filter (x ∈ ·)).card ≤ f) (e : Sym2 V) :
    (Cand e).card ≤ (candProt P Cand e).card + 2 * f := by
  have hsub : Cand e ⊆ candProt P Cand e ∪
      e.toFinset.biUnion (fun x => univ.filter (fun w => s(x, w) ∈ P)) := by
    intro w hw
    by_cases h : ∀ x ∈ e, s(x, w) ∉ P
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, h⟩)
    · push_neg at h
      obtain ⟨x, hx, hxw⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨x, Sym2.mem_toFinset.2 hx, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxw⟩⟩)
  have hx : ∀ x, (univ.filter (fun w => s(x, w) ∈ P)).card ≤ f := by
    intro x
    refine le_trans ?_ (hP x)
    refine Finset.card_le_card_of_injOn (fun w => s(x, w)) ?_ ?_
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw
      simp [hw]
    · intro w _ w' _ h
      exact Sym2.congr_right.1 h
  have hb : (e.toFinset.biUnion (fun x => univ.filter (fun w => s(x, w) ∈ P))).card ≤
      2 * f := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ x ∈ e.toFinset, (univ.filter (fun w => s(x, w) ∈ P)).card
        ≤ ∑ _x ∈ e.toFinset, f := Finset.sum_le_sum fun x _ => hx x
      _ = e.toFinset.card * f := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 * f := by
          apply Nat.mul_le_mul_right
          rw [Sym2.card_toFinset]; split_ifs <;> omega
  calc (Cand e).card ≤ (candProt P Cand e ∪
        e.toFinset.biUnion (fun x => univ.filter (fun w => s(x, w) ∈ P))).card :=
        Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (candProt P Cand e).card + 2 * f := by omega

/-- **Cover-down protegido.** Además de las conclusiones de `cover_down`, todas las aristas
del packing (bases y alas) evitan el grafo protegido `P`. -/
theorem cover_down_protected (H : Host V I) (F : Set (Multiset I)) (U X P : Finset (Sym2 V))
    (hUX : Disjoint U X) (hUP : Disjoint U P) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x, w) ∈ X)
    {d q f : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hPdeg : ∀ x, (P.filter (x ∈ ·)).card ≤ f)
    (hcand : ∀ e ∈ U, U.card + q * (2 * d + 4 * q + 2 * f) < q * (Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ U ⊆ C.biUnion triEdges ∧
      C.biUnion triEdges ⊆ U ∪ X ∧ Disjoint (C.biUnion triEdges) P ∧
      ∀ v, ((C.biUnion triEdges).filter (v ∈ ·)).card ≤ 2 * d + 2 * q := by
  set X' := X.filter (· ∉ P)
  have hUX' : Disjoint U X' := Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hUX
  have hCand' : ∀ e ∈ U, ∀ w ∈ candProt P Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x, w) ∈ X' := by
    intro e he w hw
    obtain ⟨hw, hwP⟩ := Finset.mem_filter.1 hw
    obtain ⟨h1, h2, h3⟩ := hCand e he w hw
    exact ⟨h1, h2, fun x hx => Finset.mem_filter.2 ⟨h3 x hx, hwP x hx⟩⟩
  have hcand' : ∀ e ∈ U, U.card + q * (2 * (d + 2 * q)) < q * (candProt P Cand e).card := by
    intro e he
    have h1 := hcand e he
    have h2 := card_cand_sub_candProt_le P Cand hPdeg e
    have h3 : q * (Cand e).card ≤ q * (candProt P Cand e).card + q * (2 * f) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left q h2
    nlinarith
  obtain ⟨C, hC, hcov, hsub, hdegC⟩ := cover_down H F U X' hUX' hU (candProt P Cand) hCand'
    hdeg hcand'
  refine ⟨C, hC, hcov, hsub.trans (Finset.union_subset_union (subset_refl U) (Finset.filter_subset _ _)),
    ?_, hdegC⟩
  rw [Finset.disjoint_left]
  intro e he heP
  rcases Finset.mem_union.1 (hsub he) with h | h
  · exact Finset.disjoint_left.1 hUP h heP
  · exact (Finset.mem_filter.1 h).2 heP

end TypedTriangle
