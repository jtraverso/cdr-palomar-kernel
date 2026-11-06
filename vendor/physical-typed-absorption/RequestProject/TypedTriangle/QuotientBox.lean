/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Caja finita: cotas uniformes de rango y torsión de un cociente comprimido (V8, §2 de la guía V7)

Parte algebraica de §2 de `GUIA_COCIENTE_Y_ROBUSTEZ_V7.md`, enunciada para submódulos
`Λ ≤ M` de un `ℤ`-módulo arbitrario `N`, con el cociente escrito EXACTAMENTE como
`physQuot` (`M ⧸ Λ.comap M.subtype`). Al instanciar `N := Sym2 V → ℤ`,
`M := localGroup H F`, `Λ := lattice H F` (que es `span` de los indicadores de triángulos
permitidos) se obtiene `physQuot H F`.

* `torBound d D`: constante explícita que depende SÓLO de `d` y `D`: el máximo de
  `|Tor(ℤ^d / span S)|` sobre los subconjuntos `S` de la caja `[-D, D]^d`.
* `quotient_bounds_of_coord`: si `q : M → ℤ^d` es lineal, `ker q ⊆ Λ` y los generadores de
  `Λ` caen en la caja, entonces `rank (M/Λ) ≤ d` y `|Tor(M/Λ)| ≤ torBound d D`.
* `mapQ_surjective_of_reduce`: forma algebraica de la sobreyección (8) `Q_(J−Z) → Q_J`.
* `quotient_bounds_of_compression`: misma conclusión a partir de datos con la forma de
  `Compression` (`x - P x = A (C₀ x)`, `range A ≤ Λ`, `P x` recuperable desde sus
  coordenadas) y una cota de caja para las coordenadas de `P` en los generadores.

Nota: el núcleo usa la composición `q = coord ∘ P`, no las coordenadas de `x` mismo:
de `coord (x) = coord (λ)` no se sigue `P (x - λ) = 0`.

El adaptador a `Compression H F s H₀ D₀` de `G1ZSplice.lean` y la exportación (1) de la
compresión desde `SampleConstruct` NO están en este archivo.
-/

open Submodule Module

noncomputable section
open Classical

namespace TypedTriangle.QuotientBox

/-- La caja `[-D, D]^d ⊆ ℤ^d`. -/
def box (d D : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(D : ℤ)) D

lemma mem_box {d D : ℕ} {z : Fin d → ℤ} : z ∈ box d D ↔ ∀ i, |z i| ≤ D := by
  simp [box, Fintype.mem_piFinset, abs_le]

/-- La torsión de `ℤ^d / Γ` es finita. -/
instance torsion_quot_finite (d : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) :
    Finite (torsion ℤ ((Fin d → ℤ) ⧸ Γ)) := by
  have : Module.Finite ℤ (torsion ℤ ((Fin d → ℤ) ⧸ Γ)) :=
    Module.IsNoetherian.finite ℤ _
  exact Module.finite_of_fg_torsion _ torsion_isTorsion

/-- `|Tor(ℤ^d / Γ)|`. -/
def torCard (d : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) : ℕ :=
  Nat.card (torsion ℤ ((Fin d → ℤ) ⧸ Γ))

/-- **Constante uniforme (5)**: máximo de `|Tor(ℤ^d / Γ_S)|` sobre `S ⊆ [-D,D]^d`. -/
def torBound (d D : ℕ) : ℕ :=
  (box d D).powerset.sup fun S => torCard d (span ℤ (S : Set (Fin d → ℤ)))

lemma card_torsion_le_torBound {d D : ℕ} {S : Set (Fin d → ℤ)} (hS : ∀ z ∈ S, z ∈ box d D) :
    Nat.card (torsion ℤ ((Fin d → ℤ) ⧸ span ℤ S)) ≤ torBound d D := by
  have hSeq : span ℤ S = span ℤ (((box d D).filter (· ∈ S) : Finset _) : Set (Fin d → ℤ)) := by
    congr 1
    ext z; simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨hS z h, h⟩, fun h => h.2⟩
  change torCard d (span ℤ S) ≤ _
  rw [hSeq]
  have hmem : (box d D).filter (· ∈ S) ∈ (box d D).powerset :=
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have := Finset.le_sup (f := fun S : Finset (Fin d → ℤ) => torCard d (span ℤ (S : Set _))) hmem
  unfold torBound
  exact this

/-- Rango y torsión se controlan a través de una inyección lineal en un cociente finitamente
generado. -/
lemma bounds_of_injective {Q Q' : Type*} [AddCommGroup Q] [AddCommGroup Q']
    [Module.Finite ℤ Q'] [Finite (torsion ℤ Q')] (f : Q →ₗ[ℤ] Q') (hf : Function.Injective f) :
    finrank ℤ Q ≤ finrank ℤ Q' ∧ Nat.card (torsion ℤ Q) ≤ Nat.card (torsion ℤ Q') := by
  refine ⟨LinearMap.finrank_le_finrank_of_injective hf, ?_⟩
  let g : torsion ℤ Q → torsion ℤ Q' := fun x => ⟨f x, by
    obtain ⟨a, ha⟩ := x.2
    exact ⟨a, by
      show (a : ℤ) • f x = 0
      rw [← map_smul]
      have : (a : ℤ) • (x : Q) = 0 := ha
      rw [this, map_zero]⟩⟩
  exact Nat.card_le_card_of_injective g fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))

variable {N : Type*} [AddCommGroup N]

/-- **Cotas uniformes (6) por coordenadas.** `q : M → ℤ^d` lineal con núcleo dentro de `Λ`;
los generadores de `Λ = span G` tienen coordenadas en `[-D,D]`. Entonces el cociente
`M ⧸ Λ.comap M.subtype` (la forma de `physQuot`) tiene rango `≤ d` y torsión
`≤ torBound d D`. Ni `M = Λ`, ni idempotencia, ni sobreyectividad de `q` se suponen. -/
theorem quotient_bounds_of_coord (d D : ℕ) (M Λ : Submodule ℤ N) (G : Set N)
    (hΛ : Λ = span ℤ G) (hΛM : Λ ≤ M) (q : M →ₗ[ℤ] (Fin d → ℤ))
    (hker : ∀ x : M, q x = 0 → (x : N) ∈ Λ)
    (hbox : ∀ g ∈ G, ∀ hg : g ∈ M, ∀ i, |q ⟨g, hg⟩ i| ≤ D) :
    finrank ℤ (M ⧸ Λ.comap M.subtype) ≤ d ∧
      Nat.card (torsion ℤ (M ⧸ Λ.comap M.subtype)) ≤ torBound d D := by
  set Λ' := Λ.comap M.subtype
  set S : Set (Fin d → ℤ) := {z | ∃ g ∈ G, ∃ hg : g ∈ M, q ⟨g, hg⟩ = z}
  -- `q(Λ') = span S`.
  have hΓ : Λ'.map q = span ℤ S := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : N) ∈ span ℤ G := hΛ ▸ hx
      have key : ∀ y (hy : y ∈ span ℤ G), ∀ hM : y ∈ M, q ⟨y, hM⟩ ∈ span ℤ S := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem g hg => exact fun hM => subset_span ⟨g, hg, hM, rfl⟩
        | zero =>
          intro hM
          have : (⟨0, hM⟩ : M) = 0 := rfl
          rw [this, map_zero]; exact zero_mem _
        | add a b ha hb iha ihb =>
          intro hM
          have haM : a ∈ M := hΛM (hΛ ▸ ha)
          have hbM : b ∈ M := hΛM (hΛ ▸ hb)
          have : (⟨a + b, hM⟩ : M) = ⟨a, haM⟩ + ⟨b, hbM⟩ := rfl
          rw [this, map_add]
          exact add_mem (iha haM) (ihb hbM)
        | smul c a ha iha =>
          intro hM
          have haM : a ∈ M := hΛM (hΛ ▸ ha)
          have : (⟨c • a, hM⟩ : M) = c • ⟨a, haM⟩ := rfl
          rw [this, map_smul]
          exact smul_mem _ _ (iha haM)
      exact key x hx' x.2
    · rw [span_le]
      rintro _ ⟨g, hg, hgM, rfl⟩
      refine ⟨⟨g, hgM⟩, ?_, rfl⟩
      show g ∈ Λ
      rw [hΛ]; exact subset_span hg
  -- La aplicación inducida `M/Λ' → ℤ^d / q(Λ')` es inyectiva (isomorfía (3) sobre su imagen).
  let φ := Λ'.mapQ (Λ'.map q) q (le_comap_map q Λ')
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨l, hl, hlx⟩ := hy
      rw [Submodule.Quotient.mk_eq_zero]
      have h0 : q (x - l) = 0 := by rw [map_sub, hlx, sub_self]
      have h1 := hker _ h0
      have h2 : (l : N) ∈ Λ := hl
      have : (x : N) = ((x - l : M) : N) + l := by simp
      show (x : N) ∈ Λ
      rw [this]; exact add_mem h1 h2
  obtain ⟨hr, ht⟩ := bounds_of_injective φ hφ
  refine ⟨hr.trans ?_, ht.trans ?_⟩
  · calc finrank ℤ ((Fin d → ℤ) ⧸ Λ'.map q) ≤ finrank ℤ (Fin d → ℤ) :=
          LinearMap.finrank_range_le (Λ'.map q).mkQ |>.trans_eq' (by
            rw [LinearMap.range_eq_top.2 (Submodule.mkQ_surjective _), finrank_top])
      _ = d := by simp
  · rw [hΓ]
    refine card_torsion_le_torBound ?_
    rintro _ ⟨g, hg, hgM, rfl⟩
    exact mem_box.2 (hbox g hg hgM)

/-- **Cotas uniformes (6) desde datos con la forma de `Compression`.**
`x - P x = A (C₀ x)` con `range A ≤ Λ`; las coordenadas `coord : N → ℤ^d` recuperan `P x`
(`emb (coord (P x)) = P x`, que en `G1ZSplice` es `eEmb_eProj` aplicado a `supp`); y las
coordenadas de `P` en los generadores de `Λ` están en `[-D, D]` (en `G1ZSplice`,
`l1_eProj_le`, `costP` y `l1E_ind_triEdges` dan `D = 3 D₀`). -/
theorem quotient_bounds_of_compression (d D : ℕ) {X : Type*} [AddCommGroup X]
    (M Λ : Submodule ℤ N) (G : Set N) (hΛ : Λ = span ℤ G) (hΛM : Λ ≤ M)
    (A : X →ₗ[ℤ] N) (hA : ∀ c, A c ∈ Λ) (C₀ : M →ₗ[ℤ] X) (P : M →ₗ[ℤ] N)
    (decomp : ∀ x : M, (x : N) - P x = A (C₀ x))
    (coord : N →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] N)
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ G, ∀ hg : g ∈ M, ∀ i, |coord (P ⟨g, hg⟩) i| ≤ D) :
    finrank ℤ (M ⧸ Λ.comap M.subtype) ≤ d ∧
      Nat.card (torsion ℤ (M ⧸ Λ.comap M.subtype)) ≤ torBound d D := by
  refine quotient_bounds_of_coord d D M Λ G hΛ hΛM (coord ∘ₗ P) (fun x hx => ?_) hbox
  have hP : P x = 0 := by
    rw [← hrec x]; simp only [LinearMap.comp_apply] at hx; rw [hx, map_zero]
  have := decomp x
  rw [hP, sub_zero] at this
  rw [this]; exact hA _

/-- **Forma algebraica de la sobreyección (8).** Sean `Λ₁ ≤ Λ₂` y `M₁ ≤ M₂` (en `N`). Si todo `x ∈ M₂` difiere en un elemento de `Λ₂` de algún `y ∈ M₁` (la
reducción `x' = x - A c` soportada fuera de `Z`), entonces el morfismo inducido
`M₁/Λ₁ → M₂/Λ₂` (la forma de `quotMap`) es sobreyectivo. No se exige `x ∈ Λ₂`. -/
theorem mapQ_surjective_of_reduce (M₁ M₂ Λ₁ Λ₂ : Submodule ℤ N) (hM : M₁ ≤ M₂) (hΛ : Λ₁ ≤ Λ₂)
    (hred : ∀ x ∈ M₂, ∃ y ∈ M₁, x - y ∈ Λ₂) :
    Function.Surjective ((Λ₁.comap M₁.subtype).mapQ (Λ₂.comap M₂.subtype)
      (Submodule.inclusion hM) (fun _ hx => hΛ hx)) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨y, hy, hxy⟩ := hred x.1 x.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    show ((Submodule.inclusion hM ⟨y, hy⟩ - x : M₂) : N) ∈ Λ₂
    have : ((Submodule.inclusion hM ⟨y, hy⟩ - x : M₂) : N) = -(x.1 - y) := by
      simp [Submodule.coe_inclusion]
    rw [this]; exact neg_mem hxy

end TypedTriangle.QuotientBox
