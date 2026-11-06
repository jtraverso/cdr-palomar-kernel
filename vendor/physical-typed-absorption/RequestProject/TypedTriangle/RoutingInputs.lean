/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ComponentCount
public import RequestProject.TypedTriangle.PreparedComposition

@[expose] public section

/-!
# Endpoint reutilizable de las entradas de enrutamiento (V17, §3)

* `routing_inputs_endpoint` — elige `C, D, δ, n₀` (sólo de `α, h`) y luego, sobre todo host
  finito nativo `(G, lab, F)` con la cota inferior de componentes activas
  `α · card V ≤ |K|` y `card V ≥ n₀`, DERIVA `card V > 0`, `hrows`, `hdeg` y las dos
  ventanas numéricas en `n = card V`. `hrows`, `hdeg` no son hipótesis.
* `routing_inputs_host` — la misma conclusión con las constantes explícitas
  `compConst α`, `routeD α`, `routeδ α h`, `routeN0 α h`.
* `routing_budget_of_lower` — consumidor: `routing_budget_real` con esas constantes; queda
  como entrada sólo `hdel` (el teorema local de borrado).
* `prepared_core_composed_certificate_of_lower` — consumidor: el endpoint V16 con `hn`,
  `hδ`, `hδC`, `hrows`, `hdeg`, `hD1`, `hD` descargados; quedan `UniformCertOn`,
  `PreparedCore`, `hdel` y los datos de compresión V14.

Esto NO construye `DeletionHyp` ni `PreparedCore`, y no prueba T.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.RoutingInputs

open TypedTriangle.ComponentRows TypedTriangle.ActiveCover TypedTriangle.RoutingConstants
  TypedTriangle.ComponentCount TypedTriangle.SparseEdge TypedTriangle.Dispersal
open TypedTriangle.Grouping TypedTriangle.QuotientBox TypedTriangle.Composition

universe u v

/-- **Entradas del enrutamiento en un host**, con las constantes explícitas fijadas antes
del host. -/
theorem routing_inputs_host {α : ℝ} (hα : 0 < α) (h : ℕ)
    {V : Type u} {I : Type v} [Fintype V] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I))
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card)
    (hn₀ : routeN0 α h ≤ Fintype.card V) :
    0 < Fintype.card V ∧
      (∀ a, (univ.filter (fun j : Row V => j.1 = a ∧ IsActiveRow G lab F j)).card ≤
        compConst α) ∧
      (∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ compConst α * j.2.card) ∧
      ∀ a : ℕ, (a : ℝ) ≤ routeδ α h * Fintype.card V →
        (a : ℝ) + 2 < α * Fintype.card V ∧
          ((a : ℝ) + h) * (2 : ℝ) ^ (h.choose 2) ≤ α / 2 * Fintype.card V :=
  ⟨lt_of_lt_of_le (routeN0_pos α h) hn₀, hrows_of_lower G lab F hα hlow,
    hdeg_of_lower G lab F hα hlow, fun _ ha => routeWindows hα h hn₀ ha⟩

/-- **Endpoint reutilizable**: `C, D, δ, n₀` se eligen primero (de `α, h` solamente);
después, para todo host finito nativo con la cota inferior de componentes activas y
`card V ≥ n₀`, se derivan `card V > 0`, `hrows`, `hdeg` y las dos ventanas. -/
theorem routing_inputs_endpoint {α : ℝ} (hα : 0 < α) (h : ℕ) :
    ∃ C D : ℕ, ∃ δ : ℝ, ∃ n₀ : ℕ,
      1 ≤ C ∧ 0 < δ ∧ (C : ℝ) * δ ≤ 4 ∧ 1 ≤ D ∧ 12 * C ^ 2 ≤ D + 1 ∧
      ∀ {V : Type u} {I : Type v} [Fintype V] (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)),
        (∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card) →
        n₀ ≤ Fintype.card V →
        0 < Fintype.card V ∧
          (∀ a, (univ.filter (fun j : Row V => j.1 = a ∧ IsActiveRow G lab F j)).card ≤ C) ∧
          (∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card) ∧
          ∀ a : ℕ, (a : ℝ) ≤ δ * Fintype.card V →
            (a : ℝ) + 2 < α * Fintype.card V ∧
              ((a : ℝ) + h) * (2 : ℝ) ^ (h.choose 2) ≤ α / 2 * Fintype.card V :=
  ⟨compConst α, routeD α, routeδ α h, routeN0 α h, one_le_compConst α, routeδ_pos hα h,
    compConst_mul_routeδ_le α h, one_le_routeD α, routeD_spec α,
    fun G lab F hlow hn₀ => routing_inputs_host hα h G lab F hlow hn₀⟩

/-- **Consumidor V13**: `routing_budget_real` con `C = compConst α`, `D = routeD α`,
`δ = routeδ α h`; `hrows`, `hdeg`, `hn`, `hδ`, `hδC`, `hD1`, `hD` derivados. Queda `hdel`
(teorema local de borrado) como única entrada geométrica. -/
theorem routing_budget_of_lower {α : ℝ} (hα : 0 < α) (h : ℕ)
    {V : Type u} {I : Type v} [Fintype V] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I))
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card)
    (hn₀ : routeN0 α h ≤ Fintype.card V)
    (hdel : ∀ A : Finset V, (A.card : ℝ) ≤ routeδ α h * Fintype.card V →
      ActiveCover.DeletionHyp G lab F A)
    (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (he : 0 < norm1 G x) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * routeD α) ∧
      (cells.map (norm1 G)).sum ≤ 6 * routeD α * norm1 G x ∧
      ∀ v, (cells.countP (fun b => decide (InSupp G v b)) : ℤ) <
        3 * dabs G x v + ⌈32 * routeD α * (norm1 G x : ℝ) /
          (routeδ α h * Fintype.card V)⌉₊ + 2 * routeD α := by
  obtain ⟨hn, hrows, hdeg, -⟩ := routing_inputs_host hα h G lab F hlow hn₀
  exact routing_budget_real x hx (routeδ α h) (routeδ_pos hα h) (compConst_mul_routeδ_le α h)
    he hn hrows hdeg hdel (one_le_routeD α) (routeD_spec α)

/-- **Consumidor V16**: `prepared_core_composed_certificate` con las constantes de
enrutamiento `C = compConst γ`, `D = routeD γ`, `δ = routeδ γ hw` fijadas antes del host y
`hn`, `hδ`, `hδC`, `hrows`, `hdeg`, `hD1`, `hD` DERIVADOS de la cota inferior de componentes
activas `γ · card V ≤ |K|` y de `card V ≥ routeN0 γ hw`. Siguen siendo entradas:
`UniformCertOn`, `PreparedCore`, `hdel` y los datos de compresión V14. (`γ, hw` son los
parámetros de enrutamiento; no se identifican con `α, h` de `PreparedCore`.) -/
theorem prepared_core_composed_certificate_of_lower
    {α : ℝ} {h N₀ K : ℕ} {β : ℝ} {γ : ℝ} (hγ : 0 < γ) (hw : ℕ) (d R B : ℕ)
    {V : Type u} {I : Type v} [Fintype V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)}
    (hU : UniformCertOn.{u} F α h N₀ (3 * routeD γ * groupBound d B R) K)
    (Pc : PreparedCore G lab F α h N₀ β) (hβ : 0 < β)
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → γ * Fintype.card V ≤ j.2.card)
    (hn₀ : routeN0 γ hw ≤ Fintype.card V)
    (hdel : ∀ A : Finset V, (A.card : ℝ) ≤ routeδ γ hw * Fintype.card V →
      DeletionHyp G lab F A)
    {X : Type*} [AddCommGroup X]
    (A : X →ₗ[ℤ] (Sym2 V → ℤ)) (hA : ∀ c, A c ∈ lattice G lab F)
    (C₀ : localProfile G lab F →ₗ[ℤ] X) (P : localProfile G lab F →ₗ[ℤ] (Sym2 V → ℤ))
    (decomp : ∀ x : localProfile G lab F, (x : Sym2 V → ℤ) - P x = A (C₀ x))
    (coord : (Sym2 V → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (Sym2 V → ℤ))
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ latGens G lab F, ∀ hg : g ∈ localProfile G lab F, ∀ k,
      |coord (P ⟨g, hg⟩) k| ≤ R)
    (hcoord : ∀ b : localProfile G lab F, l1E (b : Sym2 V → ℤ) ≤ 3 * routeD γ → ∀ k,
      |coord (P b) k| ≤ B)
    (x : Sym2 V → ℤ) (hx : x ∈ lattice G lab F) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ 2 * K * norm1 G x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * ((4 * routeD γ + 3) * dabs G x v +
          (32 * routeD γ / routeδ γ hw + 12 * K / β) * (norm1 G x / Fintype.card V) +
            2 * routeD γ + 2) := by
  obtain ⟨hn, hrows, hdeg, -⟩ := routing_inputs_host hγ hw G lab F hlow hn₀
  exact prepared_core_composed_certificate (routeδ γ hw) d R B hU Pc hβ (routeδ_pos hγ hw)
    (compConst_mul_routeδ_le γ hw) hn hrows hdeg hdel (one_le_routeD γ) (routeD_spec γ)
    A hA C₀ P decomp coord emb hrec hbox hcoord x hx

end TypedTriangle.RoutingInputs
