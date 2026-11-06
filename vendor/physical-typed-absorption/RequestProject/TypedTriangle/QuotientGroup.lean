/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Lattice
public import RequestProject.TypedTriangle.Robust

@[expose] public section

/-!
# El grupo `Q_G = M_G / Λ_G`: finitud y funtorialidad (P02/P04, parte algebraica)

* `localGroup_mono`: `M_H ⊆ M_{H'}` si `H ≤ H'` (las estrellas de un enlace menor están en
  la imagen de la incidencia del enlace mayor);
* `quotMap`: el morfismo inducido `Q_H → Q_{H'}` por la inclusión de hosts (el de (L9));
* `physQuot_finite`, `physQuot_torsion_finite`: `Q_G` es un grupo abeliano finitamente
  generado con torsión finita, de modo que `TypedTriangle.Robust.chain_strict_count` se
  aplica a cadenas de cocientes físicos `Q_{J_k}` en cuanto se disponga de la sobreyectividad
  (L9) y de las cotas uniformes de rango y torsión (L8).

La sobreyectividad de `quotMap` tras un borrado pequeño de vértices (S16) y las cotas
uniformes (G1-Z, S01) NO están formalizadas.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Monotonía del grupo local respecto del host. -/
theorem localGroup_mono {H H' : Host V I} {F : Set (Multiset I)} (hG : H.G ≤ H'.G)
    (hl : H.lab = H'.lab) : localGroup H F ≤ localGroup H' F := by
  rintro x ⟨hx0, hx⟩
  refine ⟨fun e he => hx0 e fun h => he ?_, fun v => ?_⟩
  · simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    induction e using Sym2.ind with
    | _ a b => exact hG h
  · obtain ⟨c, hc⟩ := hx v
    refine ⟨fun T => if IsAllowed H F T then c T else 0, fun w hw => ?_⟩
    rw [hc w hw]
    have hsub : (triAt H F v).filter (w ∈ ·) ⊆ (triAt H' F v).filter (w ∈ ·) := by
      intro T hT
      simp only [triAt, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact ⟨⟨isAllowed_mono hG hl hT.1.1, hT.1.2⟩, hT.2⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun T hT => ?_
      simp only [triAt, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rw [if_pos hT.1.1]
    · intro T _ hT
      rw [if_neg]
      intro hA
      apply hT
      simp only [triAt, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at *
      tauto

/-- Morfismo inducido `Q_H → Q_{H'}` por una inclusión de hosts con las mismas etiquetas. -/
def quotMap {H H' : Host V I} {F : Set (Multiset I)} (hG : H.G ≤ H'.G) (hl : H.lab = H'.lab) :
    physQuot H F →ₗ[ℤ] physQuot H' F :=
  Submodule.mapQ _ _ (Submodule.inclusion (localGroup_mono hG hl)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    exact lattice_mono hG hl hx)

instance physQuot_finite (H : Host V I) (F : Set (Multiset I)) :
    Module.Finite ℤ (physQuot H F) := by
  have : Module.Finite ℤ (localGroup H F) := Module.IsNoetherian.finite ℤ _
  infer_instance

instance physQuot_torsion_finite (H : Host V I) (F : Set (Multiset I)) :
    Finite (Submodule.torsion ℤ (physQuot H F)) := by
  have : Module.Finite ℤ (Submodule.torsion ℤ (physQuot H F)) :=
    Module.IsNoetherian.finite ℤ _
  exact Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion)

/-- **Cadena física (L8)–(L10), forma condicional.** Para una cadena decreciente de hosts
`H 0 ≥ H 1 ≥ ⋯` cuyos morfismos inducidos `Q_{H (k+1)} → Q_{H k}` son sobreyectivos (esto es
(L9), NO demostrado aquí) y con rango `≤ d` y torsión `≤ T` (esto es (L8), NO demostrado
aquí), a lo sumo `d + (d+1) ⌊log₂ T⌋` pasos no son isomorfismos, es decir, a lo sumo esos
pasos violan (L10). -/
theorem physical_chain_strict_count (H : ℕ → Host V I) (F : Set (Multiset I))
    (hG : ∀ k, (H (k + 1)).G ≤ (H k).G) (hl : ∀ k, (H (k + 1)).lab = (H k).lab)
    (m d T : ℕ) (hsurj : ∀ k < m, Function.Surjective (quotMap (F := F) (hG k) (hl k)))
    (hd : ∀ k ≤ m, Module.finrank ℤ (physQuot (H k) F) ≤ d)
    (hT : ∀ k ≤ m, Nat.card (Submodule.torsion ℤ (physQuot (H k) F)) ≤ T) :
    ((Finset.range m).filter fun k =>
        ¬ Function.Injective (quotMap (F := F) (hG k) (hl k))).card ≤
      d + (d + 1) * Nat.log 2 T :=
  Robust.chain_strict_count (fun k => physQuot (H k) F) (fun k => quotMap (hG k) (hl k))
    m d T hsurj hd hT

end TypedTriangle

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- **Injectividad de `Q_H → Q_{H'}` y (L10).** El morfismo inducido es inyectivo si y sólo
si todo vector de `M_H` que es físico en `H'` ya es físico en `H`; es decir,
`Λ_H = Λ_{H'} ∩ M_H`. -/
theorem quotMap_injective_iff {H H' : Host V I} {F : Set (Multiset I)} (hG : H.G ≤ H'.G)
    (hl : H.lab = H'.lab) :
    Function.Injective (quotMap (F := F) hG hl) ↔
      ∀ x ∈ localGroup H F, x ∈ lattice H' F → x ∈ lattice H F := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx hx'
    have := h (Submodule.Quotient.mk ⟨x, hx⟩) (by
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx')
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.Quotient.mk_eq_zero]
      exact h x.1 x.2 hy

end TypedTriangle
