/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ZigzagCells

@[expose] public section

/-!
# Ciclos de entrada del zigzag (V13, S26 §5)

A partir de la descomposición de V12 (`local_profile_active_ordered_cycles`) se obtiene la
lista de ciclos ordenados de longitud `≥ 3` (`OrdCycle`) que alimenta el zigzag:

* los ciclos de un arco no existen (`card_ne_one`, no hay lazos) y los de dos arcos se
  proyectan a cero (`proj_eq_zero_of_card_two`), así que se descartan sin cambiar la suma;
* `exists_ordCycles` — para todo perfil local `x`: las proyecciones físicas de los ciclos
  suman `x`; la longitud total es `≤ 2‖x‖₁`; todos los estados son activos; y el número total
  de posiciones de ciclos cuyo estado tiene raíz física `v` es `≤ d_abs(x)(v)`
  (`= Σ_{e ∋ v} |x e|`). Varios estados pueden tener la misma raíz; se cuentan todas las
  posiciones, no raíces distintas.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation
open TypedTriangle.Zigzag

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

variable (G) in
/-- `‖x‖₁` sobre las aristas del host. -/
def norm1 (x : Sym2 V → ℤ) : ℤ := ∑ e : Col G, |x e.1|

variable (G) in
/-- `d_abs(x)(v) = Σ_{e ∋ v} |x e|`. -/
def dabs (x : Sym2 V → ℤ) (v : V) : ℤ := ∑ e : Col G, if v ∈ e.1 then |x e.1| else 0

lemma card_filter_root_eq (S : Finset (St V)) (v : V) :
    (S.filter (fun X => X.1.1 = v)).card =
      ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
        ((if (j, true) ∈ S then 1 else 0) + (if (j, false) ∈ S then 1 else 0)) := by
  rw [Finset.card_filter]
  have : ∑ X ∈ S, (if X.1.1 = v then 1 else 0) =
      ∑ X ∈ (univ.filter (fun j : Row V => j.1 = v)) ×ˢ (univ : Finset Bool),
        (if X ∈ S then 1 else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext X
    simp [and_comm]
  rw [this, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

namespace OrdCycle

variable (c : OrdCycle G lab F)

/-- Las posiciones de raíz `v` de un ciclo ordenado se cuentan por los estados del ciclo. -/
lemma count_root_le (v : V) :
    ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card ≤
      ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
        ((if (j, true) ∈ c.arcs.toFinset.image (src _) then 1 else 0) +
          (if (j, false) ∈ c.arcs.toFinset.image (src _) then 1 else 0)) := by
  rw [← card_filter_root_eq]
  refine card_le_card_of_injOn c.st (fun p hp => ?_) (fun p hp p' hp' h => ?_)
  · rw [Finset.mem_coe] at hp
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hp1' := mem_range.mp hp1
    refine Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_image.mpr ⟨c.arcs[p], ?_, (c.st_of_lt hp1').symm⟩, hp2⟩)
    exact List.mem_toFinset.mpr (List.getElem_mem _)
  · rw [Finset.mem_coe] at hp hp'
    have hp1 := mem_range.mp (mem_filter.mp hp).1
    have hp1' := mem_range.mp (mem_filter.mp hp').1
    rw [c.st_of_lt hp1, c.st_of_lt hp1'] at h
    have h' : (c.arcs.map (src _))[p]'(by simpa using hp1) =
        (c.arcs.map (src _))[p']'(by simpa using hp1') := by simpa using h
    exact c.src_nodup.getElem_inj_iff.mp h'

end OrdCycle

/-- Construcción de los ciclos ordenados a partir de una lista de ciclos simples con orden. -/
lemma ordCycles_of_list (L : List (Finset (Arc (rowSys G lab F))))
    (h1 : ∀ C ∈ L, IsSimpleCycle (src _) (tgt _) C)
    (hact : ∀ C ∈ L, ∀ α ∈ C, IsActiveRow G lab F (src _ α).1)
    (hord : ∀ C ∈ L, ∃ l : List (Arc (rowSys G lab F)), l.Nodup ∧ l.toFinset = C ∧
      l.length = C.card ∧ (l.map (src _)).Nodup ∧
      ∀ (i : ℕ) (hi : i < l.length),
        tgt _ l[i] = src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))) :
    ∃ cs : List (OrdCycle G lab F),
      (∀ e : Col G, (cs.map (fun c => flowP _ (Circulation.ind c.arcs.toFinset) e)).sum =
        (L.map (fun C => flowP _ (Circulation.ind C) e)).sum) ∧
      (cs.map (fun c => c.arcs.length)).sum ≤ (L.map Finset.card).sum ∧
      (∀ c ∈ cs, ∀ i, IsActiveRow G lab F (c.st i).1) ∧
      ∀ v, (cs.map (fun c =>
          ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card)).sum ≤
        ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
          (L.countP (fun C => (j, true) ∈ C.image (src (rowSys G lab F))) +
            L.countP (fun C => (j, false) ∈ C.image (src (rowSys G lab F)))) := by
  induction L with
  | nil => exact ⟨[], by simp, by simp, by simp, by simp⟩
  | cons C L ih =>
    obtain ⟨cs, hs1, hs2, hs3, hs4⟩ := ih (fun C' h => h1 C' (List.mem_cons_of_mem _ h))
      (fun C' h => hact C' (List.mem_cons_of_mem _ h))
      (fun C' h => hord C' (List.mem_cons_of_mem _ h))
    have hC := h1 C (by simp)
    have hcountP : ∀ v, ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
        ((C :: L).countP (fun C => (j, true) ∈ C.image (src (rowSys G lab F))) +
          (C :: L).countP (fun C => (j, false) ∈ C.image (src (rowSys G lab F)))) =
        ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
          ((if (j, true) ∈ C.image (src (rowSys G lab F)) then 1 else 0) +
            (if (j, false) ∈ C.image (src (rowSys G lab F)) then 1 else 0)) +
        ∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
          (L.countP (fun C => (j, true) ∈ C.image (src (rowSys G lab F))) +
            L.countP (fun C => (j, false) ∈ C.image (src (rowSys G lab F)))) := by
      intro v
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [List.countP_cons, decide_eq_true_eq]
      split_ifs <;> omega
    by_cases h3 : 3 ≤ C.card
    · obtain ⟨l, hl1, hl2, hl3, hl4, hl5⟩ := hord C (by simp)
      let c : OrdCycle G lab F := ⟨l, hl1, hl4, by omega, hl5⟩
      have hcC : c.arcs.toFinset = C := hl2
      refine ⟨c :: cs, fun e => ?_, ?_, ?_, fun v => ?_⟩
      · simp only [List.map_cons, List.sum_cons, hs1 e, hcC]
      · simp only [List.map_cons, List.sum_cons]
        have : c.arcs.length = C.card := hl3
        omega
      · intro c' hc' i
        rcases List.mem_cons.mp hc' with rfl | hc'
        · have hmem : c.arcs[i % c.arcs.length]'(Nat.mod_lt _ c.len_pos) ∈ C := by
            rw [← hcC]; exact List.mem_toFinset.mpr (List.getElem_mem _)
          exact hact C (by simp) _ hmem
        · exact hs3 c' hc' i
      · simp only [List.map_cons, List.sum_cons]
        rw [hcountP]
        have := c.count_root_le v
        rw [hcC] at this
        exact add_le_add this (hs4 v)
    · have hcard : C.card = 2 := by
        have h0 : C.card ≠ 0 := Finset.card_ne_zero.mpr hC.nonempty
        have h1' := card_ne_one hC
        omega
      have hz := (proj_eq_zero_of_card_two hC hcard).1
      refine ⟨cs, fun e => ?_, ?_, hs3, fun v => ?_⟩
      · simp only [List.map_cons, List.sum_cons, hs1 e, hz, Pi.zero_apply, zero_add]
      · simp only [List.map_cons, List.sum_cons]; omega
      · rw [hcountP]; exact (hs4 v).trans (Nat.le_add_left _ _)

/-- **Ciclos de entrada del zigzag.** Todo perfil local `x` es la suma de las proyecciones
físicas de una lista de ciclos ordenados de longitud `≥ 3` de la cubierta activa, con
longitud total `≤ 2‖x‖₁`, estados activos y, para cada vértice físico `v`, a lo sumo
`d_abs(x)(v)` posiciones (contadas con multiplicidad) cuyo estado tiene raíz `v`. -/
theorem exists_ordCycles (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) :
    ∃ cs : List (OrdCycle G lab F),
      (∀ e : Col G, (cs.map (fun c => flowP _ (Circulation.ind c.arcs.toFinset) e)).sum =
        x e.1) ∧
      (((cs.map (fun c => c.arcs.length)).sum : ℕ) : ℤ) ≤ 2 * norm1 G x ∧
      (∀ c ∈ cs, ∀ i, IsActiveRow G lab F (c.st i).1) ∧
      ∀ v, (((cs.map (fun c =>
          ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card)).sum : ℕ) : ℤ) ≤
        dabs G x v := by
  obtain ⟨-, -, -, hz, L, h1, -, h3, -, h5, h6, -, h9, h10⟩ :=
    local_profile_active_ordered_cycles x hx
  obtain ⟨cs, hs1, hs2, hs3, hs4⟩ := ordCycles_of_list L h1
    (fun C hC α hα => (h9 C hC α hα).1)
    (fun C hC => by
      obtain ⟨l, a, b, c', d, e⟩ := h10 C hC
      exact ⟨l, a, by ext; simp [← b], c', d, e⟩)
  refine ⟨cs, fun e => (hs1 e).trans (h3 e), ?_, hs3, fun v => ?_⟩
  · have : ((L.map Finset.card).sum : ℤ) ≤ 2 * norm1 G x := by
      rw [h5]; unfold norm1; linarith
    exact (Nat.cast_le.mpr hs2).trans this
  · exact (Nat.cast_le.mpr (hs4 v)).trans (h6 v)

end TypedTriangle.ActiveCover
