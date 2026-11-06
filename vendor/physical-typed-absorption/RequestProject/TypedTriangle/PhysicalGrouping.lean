/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SignedGrouping

@[expose] public section

/-!
# V14 (S26 §6): adaptador físico de la agrupación

`M, Λ ≤ N` (un `ℤ`-módulo), `q : M →ₗ ℤ^d` con `ker q ⊆ Λ`, `q(Λ)` generado por vectores de
`[-R,R]^d`; fichas `b i ∈ M` con coordenadas `q (b i)` en `[-B,B]^d` y `∑ b i ∈ Λ`.
Se construye una partición de los índices en bloques de cardinal `≤ groupBound d B R` con
`∑_{i∈J} b i ∈ Λ`. La prueba usa `q(bloque) ∈ q(Λ)` y `ker q ⊆ Λ`; NUNCA `M = Λ`.

Tres formas:
* `physical_grouping`: `q(Λ ∩ M) = span G` con `G ⊆ [-R,R]^d`.
* `physical_grouping_of_gens`: `Λ = span G₀`, `Λ ≤ M`, cotas de `q` en los generadores.
* `physical_grouping_of_compression`: `q = coord ∘ P` con datos de la forma de `Compression`
  (como `QuotientBox.quotient_bounds_of_compression`), junto con las cotas uniformes de rango y
  torsión del cociente físico. Es CONDICIONAL a esos datos de compresión; no prueba T.
-/

open Submodule Finset

noncomputable section
open Classical

namespace TypedTriangle.Grouping

open TypedTriangle.QuotientBox

variable {N : Type*} [AddCommGroup N]

/-- **Adaptador físico (forma general).** -/
theorem physical_grouping (d B R : ℕ) (M Λ : Submodule ℤ N) (q : M →ₗ[ℤ] (Fin d → ℤ))
    (hker : ∀ x : M, q x = 0 → (x : N) ∈ Λ)
    (G : Set (Fin d → ℤ)) (hG : (Λ.comap M.subtype).map q = span ℤ G)
    (hGR : ∀ g ∈ G, ∀ k, |g k| ≤ R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → M) (hb : ∀ i k, |q (b i) k| ≤ B)
    (hsum : ∑ i, (b i : N) ∈ Λ) :
    ∃ P : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ P.parts, #J ≤ groupBound d B R ∧ ∑ i ∈ J, (b i : N) ∈ Λ := by
  have hsumq : ∑ i, q (b i) ∈ span ℤ G := by
    rw [← hG, ← map_sum]
    refine ⟨∑ i, b i, ?_, rfl⟩
    show ((∑ i, b i : M) : N) ∈ Λ
    rw [Submodule.coe_sum]; exact hsum
  obtain ⟨P, hP⟩ := uniform_grouping d B R (span ℤ G) G rfl hGR (fun i => q (b i)) hb hsumq
  refine ⟨P, fun J hJ => ⟨(hP J hJ).1, ?_⟩⟩
  have hJ : q (∑ i ∈ J, b i) ∈ (Λ.comap M.subtype).map q := by
    rw [hG, map_sum]; exact (hP J hJ).2
  obtain ⟨l, hl, hlq⟩ := hJ
  have h0 : q (∑ i ∈ J, b i - l) = 0 := by rw [map_sub, hlq, sub_self]
  have h1 := hker _ h0
  have h2 : (l : N) ∈ Λ := hl
  have : ∑ i ∈ J, (b i : N) = ((∑ i ∈ J, b i - l : M) : N) + l := by
    simp
  rw [this]; exact add_mem h1 h2

/-- `q(Λ ∩ M) = span {q g : g ∈ G₀ ∩ M}` cuando `Λ = span G₀ ≤ M`. -/
lemma map_comap_eq_span (d : ℕ) (M Λ : Submodule ℤ N) (G₀ : Set N) (hΛ : Λ = span ℤ G₀)
    (hΛM : Λ ≤ M) (q : M →ₗ[ℤ] (Fin d → ℤ)) :
    (Λ.comap M.subtype).map q = span ℤ {z | ∃ g ∈ G₀, ∃ hg : g ∈ M, q ⟨g, hg⟩ = z} := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : N) ∈ span ℤ G₀ := hΛ ▸ hx
    have key : ∀ y (hy : y ∈ span ℤ G₀), ∀ hM : y ∈ M,
        q ⟨y, hM⟩ ∈ span ℤ {z | ∃ g ∈ G₀, ∃ hg : g ∈ M, q ⟨g, hg⟩ = z} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact fun hM => subset_span ⟨g, hg, hM, rfl⟩
      | zero =>
        intro hM
        have : (⟨0, hM⟩ : M) = 0 := rfl
        rw [this, map_zero]; exact zero_mem _
      | add a c ha hc iha ihc =>
        intro hM
        have haM : a ∈ M := hΛM (hΛ ▸ ha)
        have hcM : c ∈ M := hΛM (hΛ ▸ hc)
        have : (⟨a + c, hM⟩ : M) = ⟨a, haM⟩ + ⟨c, hcM⟩ := rfl
        rw [this, map_add]
        exact add_mem (iha haM) (ihc hcM)
      | smul r a ha iha =>
        intro hM
        have haM : a ∈ M := hΛM (hΛ ▸ ha)
        have : (⟨r • a, hM⟩ : M) = r • ⟨a, haM⟩ := rfl
        rw [this, map_smul]
        exact smul_mem _ _ (iha haM)
    exact key x hx' x.2
  · rw [span_le]
    rintro _ ⟨g, hg, hgM, rfl⟩
    refine ⟨⟨g, hgM⟩, ?_, rfl⟩
    show g ∈ Λ
    rw [hΛ]; exact subset_span hg

/-- **Adaptador físico (generadores de `Λ`).** -/
theorem physical_grouping_of_gens (d B R : ℕ) (M Λ : Submodule ℤ N) (G₀ : Set N)
    (hΛ : Λ = span ℤ G₀) (hΛM : Λ ≤ M) (q : M →ₗ[ℤ] (Fin d → ℤ))
    (hker : ∀ x : M, q x = 0 → (x : N) ∈ Λ)
    (hbox : ∀ g ∈ G₀, ∀ hg : g ∈ M, ∀ k, |q ⟨g, hg⟩ k| ≤ R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → M) (hb : ∀ i k, |q (b i) k| ≤ B)
    (hsum : ∑ i, (b i : N) ∈ Λ) :
    ∃ P : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ P.parts, #J ≤ groupBound d B R ∧ ∑ i ∈ J, (b i : N) ∈ Λ :=
  physical_grouping d B R M Λ q hker _ (map_comap_eq_span d M Λ G₀ hΛ hΛM q)
    (by rintro _ ⟨g, hg, hgM, rfl⟩; exact hbox g hg hgM) b hb hsum

/-- **Adaptador con datos de la forma de `Compression` (condicional a esos datos).**
`x - P x = A (C₀ x)`, `range A ≤ Λ`, `emb (coord (P x)) = P x`, y coordenadas de `P` en los
generadores de `Λ` en `[-R,R]`; fichas `b i ∈ M` con `coord (P (b i)) ∈ [-B,B]^d` y
`∑ b i ∈ Λ`. Se obtienen a la vez: (i) las cotas uniformes de rango y torsión del cociente
físico `M ⧸ (Λ ∩ M)` (la torsión se conserva, no se cociente por ella), y (ii) la partición en
bloques de cardinal `≤ groupBound d B R` con suma en `Λ`. -/
theorem physical_grouping_of_compression (d B R : ℕ) {X : Type*} [AddCommGroup X]
    (M Λ : Submodule ℤ N) (G₀ : Set N) (hΛ : Λ = span ℤ G₀) (hΛM : Λ ≤ M)
    (A : X →ₗ[ℤ] N) (hA : ∀ c, A c ∈ Λ) (C₀ : M →ₗ[ℤ] X) (P : M →ₗ[ℤ] N)
    (decomp : ∀ x : M, (x : N) - P x = A (C₀ x))
    (coord : N →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] N)
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ G₀, ∀ hg : g ∈ M, ∀ k, |coord (P ⟨g, hg⟩) k| ≤ R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → M)
    (hb : ∀ i k, |coord (P (b i)) k| ≤ B) (hsum : ∑ i, (b i : N) ∈ Λ) :
    (Module.finrank ℤ (M ⧸ Λ.comap M.subtype) ≤ d ∧
      Nat.card (Submodule.torsion ℤ (M ⧸ Λ.comap M.subtype)) ≤ torBound d R) ∧
    ∃ Q : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ Q.parts, #J ≤ groupBound d B R ∧ ∑ i ∈ J, (b i : N) ∈ Λ := by
  have hker : ∀ x : M, (coord ∘ₗ P) x = 0 → (x : N) ∈ Λ := by
    intro x hx
    have hP : P x = 0 := by
      rw [← hrec x]; simp only [LinearMap.comp_apply] at hx; rw [hx, map_zero]
    have := decomp x
    rw [hP, sub_zero] at this
    rw [this]; exact hA _
  exact ⟨quotient_bounds_of_compression d R M Λ G₀ hΛ hΛM A hA C₀ P decomp coord emb hrec hbox,
    physical_grouping_of_gens d B R M Λ G₀ hΛ hΛM (coord ∘ₗ P) hker hbox b hb hsum⟩

end TypedTriangle.Grouping
