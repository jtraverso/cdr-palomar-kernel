/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertBoundary
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 — Soporte residual del núcleo de dos niveles y caso `δ_T`

* `kcert_support`: `cert_T(S) ≠ 0 ⇒ S` es un triángulo permitido de `J = E ∖ B`;
* `kcert_delta`: si `T` no toca `B`, `cert_T = δ_T`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma exists_ne_zero_of_avgOver_ne_zero {α : Type*} {s : Finset α} {g : α → ℝ}
    (h : avgOver s g ≠ 0) : ∃ x ∈ s, g x ≠ 0 := by
  by_contra hc; push_neg at hc; exact h (avgOver_eq_zero hc)

section supp

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}

/-- Un triángulo de una descomposición de `J ∪ W` con `J`, `W` disjuntos de `B` es un
triángulo permitido del residual. -/
lemma residual_of_mem_dec {J W : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomposition H F (J ∪ W) D) (hJB : Disjoint J B) (hWB : Disjoint W B)
    {S : Finset V} (hS : S ∈ D) : IsAllowed (residual H B) F S := by
  have hSA := hD.1 S hS
  refine isAllowed_subHost_of hSA fun e he => ?_
  rw [mem_sdiff]
  refine ⟨triEdges_subset_edges hSA he, fun heB => ?_⟩
  rcases mem_union.1 (hD.subset hS he) with h | h
  · exact disjoint_left.1 hJB h heB
  · exact disjoint_left.1 hWB h heB

omit [Fintype V] in
lemma wedge_disjoint_of {u v c : V} (hu : s(u, c) ∉ B) (hv : s(v, c) ∉ B) :
    Disjoint (wedge u v c) B := by
  rw [disjoint_left]; intro e he heB
  simp only [wedge, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact hu heB
  · exact hv heB

lemma hcQ_ne_zero {u v a c : V} {J : Finset (Sym2 V)} {S : Finset V}
    (h : hcQ H F B u v a c J S ≠ 0) :
    (S ∈ hdec1 H F u v a c J ∧ Disjoint (triEdges S) B) ∨ S ∈ hdec2 H F u v a c J := by
  unfold hcQ hingeCert badQ at h
  by_cases h2 : S ∈ hdec2 H F u v a c J
  · exact Or.inr h2
  · left
    by_cases h1 : S ∈ hdec1 H F u v a c J
    · refine ⟨h1, ?_⟩
      by_contra hd
      simp [h1, h2, hd] at h
    · simp [h1, h2] at h

/-- Soporte residual del certificado de dos niveles. -/
theorem Rfun_support (hK : KHyp H F B K) {u v a : V} (huvB : s(u, v) ∈ B)
    (hTa : IsAllowed H F {u, v, a}) {S : Finset V} (hS : Rfun H F B K u v a S ≠ 0) :
    IsAllowed (residual H B) F S := by
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_avgOver_ne_zero hS
  obtain ⟨c, hc, hc0⟩ := exists_ne_zero_of_avgOver_ne_zero hb0
  obtain ⟨-, -, -, hucB, hvcB⟩ := hK.cs_ok u v a huvB hTa b hb c hc
  have hWc := wedge_disjoint_of (B := B) hucB hvcB
  have hpb := (hK.piv_ok _ huvB b hb).2.2
  have hWb : Disjoint (wedge u v b) B :=
    wedge_disjoint_of (hpb u (Sym2.mem_mk_left u v)) (hpb v (Sym2.mem_mk_right u v))
  by_cases h1 : avgOver (K.fam u v a c) (fun J => hcQ H F B u v a c J S) = 0
  · rw [h1, zero_add] at hc0
    obtain ⟨J, hJ, hJ0⟩ := exists_ne_zero_of_avgOver_ne_zero hc0
    obtain ⟨hJh, hJB⟩ := hK.fam2_ok u v a huvB hTa b hb c hc J hJ
    rcases hingeCert_ne_zero hJ0 with h | h
    · exact residual_of_mem_dec (hdec1_spec hJh) hJB hWc h
    · exact residual_of_mem_dec (hdec2_spec hJh) hJB hWb h
  · obtain ⟨J, hJ, hJ0⟩ := exists_ne_zero_of_avgOver_ne_zero h1
    obtain ⟨hJh, hJB⟩ := hK.fam1_ok u v a huvB hTa b hb c hc J hJ
    rcases hcQ_ne_zero hJ0 with ⟨h, hd⟩ | h
    · have hSA := (hdec1_spec hJh).1 S h
      refine isAllowed_subHost_of hSA fun e he => ?_
      exact mem_sdiff.2 ⟨triEdges_subset_edges hSA he, fun heB => disjoint_left.1 hd he heB⟩
    · exact residual_of_mem_dec (hdec2_spec hJh) hJB hWc h

lemma RQ_support (hK : KHyp H F B K) {Q S : Finset V} (hQ : IsAllowed H F Q)
    (hS : RQ H F B K Q S ≠ 0) : IsAllowed (residual H B) F S := by
  by_cases h : ∃ x, IsTouch B Q x
  · rw [RQ_eq h] at hS
    have hx : IsTouch B Q (Classical.choose h) := Classical.choose_spec h
    exact Rfun_support hK hx.2.2.2.2 (hx.1 ▸ hQ) hS
  · exact absurd (by unfold RQ; rw [dif_neg h]) hS

/-- **Soporte residual del certificado final.** -/
theorem kcert_support (hK : KHyp H F B K) {T : Finset V} (hT : IsAllowed H F T) {S : Finset V}
    (hS : kcert H F B K T S ≠ 0) : IsAllowed (residual H B) F S := by
  unfold kcert at hS
  by_cases h : ∃ x, IsTouch B T x
  · rw [dif_pos h] at hS
    set x := Classical.choose h
    have hx : IsTouch B T x := Classical.choose_spec h
    have hTa : IsAllowed H F {x.1, x.2.1, x.2.2} := hx.1 ▸ hT
    have huvB : s(x.1, x.2.1) ∈ B := hx.2.2.2.2
    by_cases h1 : Rfun H F B K x.1 x.2.1 x.2.2 S = 0
    · rw [h1, zero_add] at hS
      obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_avgOver_ne_zero hS
      obtain ⟨c, hc, hc0⟩ := exists_ne_zero_of_avgOver_ne_zero hb0
      obtain ⟨J, hJ, hJ0⟩ := exists_ne_zero_of_avgOver_ne_zero hc0
      obtain ⟨Q, hQ, hQ0⟩ := exists_ne_zero_of_sum_ne_zero hJ0
      obtain ⟨hJh, -⟩ := hK.fam1_ok _ _ _ huvB hTa b hb c hc J hJ
      exact RQ_support hK ((hdec1_spec hJh).1 Q (badQ_subset hQ)) hQ0
    · exact Rfun_support hK huvB hTa h1
  · rw [dif_neg h] at hS
    have hST : S = T := by by_contra hne; exact hS (if_neg hne)
    subst hST
    refine isAllowed_subHost_of hT fun e he => mem_sdiff.2 ⟨triEdges_subset_edges hT he, ?_⟩
    intro heB
    obtain ⟨x, hx, -⟩ := isTouch_of_mem hT he heB
    exact h ⟨x, hx⟩

/-- Si `T` no toca `B`, su certificado es `δ_T`. -/
theorem kcert_delta {T : Finset V} (hT : Disjoint (triEdges T) B) (S : Finset V) :
    kcert H F B K T S = if S = T then 1 else 0 := by
  unfold kcert
  rw [dif_neg]
  rintro ⟨x, hx⟩
  obtain ⟨hTe, -⟩ := triEdges_touch hx
  exact disjoint_left.1 hT (by rw [hTe]; exact mem_insert_self _ _) hx.2.2.2.2

end supp

end TypedTriangle
