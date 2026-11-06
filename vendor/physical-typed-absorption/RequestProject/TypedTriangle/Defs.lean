/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Descomposiciones triangulares tipadas: definiciones

Formalización de las definiciones (D1)–(D7) del texto
"Descomposiciones triangulares tipadas mediante absorción y retículo físico".
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

/-- Un host: un grafo simple finito junto con un etiquetado `lab : V → I`. -/
structure Host (V I : Type*) where
  G : SimpleGraph V
  lab : V → I

variable {V I : Type*} [Fintype V]

/-- `E(T)`: las aristas (pares no diagonales) de un conjunto de vértices `T`. -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- Las aristas del host como `Finset`. -/
def edges (H : Host V I) : Finset (Sym2 V) := univ.filter (fun e => e ∈ H.G.edgeSet)

/-- Triángulo permitido: tres vértices distintos, mutuamente adyacentes, cuyo multiconjunto
de etiquetas está en `F`. -/
def IsAllowed (H : Host V I) (F : Set (Multiset I)) (T : Finset V) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → H.G.Adj x y) ∧ T.val.map H.lab ∈ F

/-- `𝒯(G)`: la familia de triángulos permitidos. -/
def allowed (H : Host V I) (F : Set (Multiset I)) : Finset (Finset V) :=
  univ.filter (IsAllowed H F)

/-- (D1) `D` es una descomposición permitida del conjunto de aristas `J`. -/
def IsDecomposition (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V))
    (D : Finset (Finset V)) : Prop :=
  (∀ T ∈ D, IsAllowed H F T) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
    D.biUnion triEdges = J

/-- Indicador entero `𝟏_J` de un conjunto de aristas. -/
def ind (J : Finset (Sym2 V)) : Sym2 V → ℤ := fun e => if e ∈ J then 1 else 0

/-- (D2) Retículo físico `Λ_G`: combinaciones enteras de indicadores de triángulos permitidos. -/
def lattice (H : Host V I) (F : Set (Multiset I)) : Submodule ℤ (Sym2 V → ℤ) :=
  Submodule.span ℤ ((fun T => ind (triEdges T)) '' {T | IsAllowed H F T})

/-- `J` es físico en `G`: `𝟏_J ∈ Λ_G`. -/
def IsPhysical (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V)) : Prop :=
  ind J ∈ lattice H F

/-- (D3) Semilla exacta difusa de constante `C`. -/
def IsDiffuseSeed (H : Host V I) (F : Set (Multiset I)) (C : ℝ) (φ : Finset V → ℝ) : Prop :=
  (∀ T, IsAllowed H F T →
      1 / (C * Fintype.card V) ≤ φ T ∧ φ T ≤ C / Fintype.card V) ∧
    ∀ e ∈ H.G.edgeSet, ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T = 1

/-- (D4) Vecinos comunes de `u, v` con etiqueta `k`. -/
def commonNbrs (H : Host V I) (k : I) (u v : V) : Finset V :=
  univ.filter (fun w => H.G.Adj u w ∧ H.G.Adj v w ∧ H.lab w = k)

/-- (D5) Condición de vecinos comunes (para todos los pares distintos, sean o no aristas). -/
def CommonNbrCond (H : Host V I) (F : Set (Multiset I)) (α : ℝ) : Prop :=
  ∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
    α * Fintype.card V ≤ (commonNbrs H k u v).card

/-- Vértices incidentes con alguna arista de `J` (soporte). -/
def support (J : Finset (Sym2 V)) : Finset V := univ.filter (fun x => ∃ e ∈ J, x ∈ e)

/-- (D6) La cuña `W_a = {ua, va}`. -/
def wedge (u v a : V) : Finset (Sym2 V) := {s(u, a), s(v, a)}

/-- Bisagra física para el par `T_a = {u,v,a}`, `T_b = {u,v,b}`. -/
def IsHinge (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (J : Finset (Sym2 V)) :
    Prop :=
  J ⊆ edges H ∧ Disjoint J (triEdges {u, v, a} ∪ triEdges {u, v, b}) ∧
    (∃ D, IsDecomposition H F (J ∪ wedge u v a) D) ∧
    (∃ D, IsDecomposition H F (J ∪ wedge u v b) D)

/-- `𝓗_i(T_a,T_b)`: bisagras (como conjuntos de aristas) de orden exactamente `i`. -/
def hinges (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (i : ℕ) :
    Finset (Finset (Sym2 V)) :=
  univ.filter (fun J => IsHinge H F u v a b J ∧ (support J).card = i)

/-- (D7) Condición de bisagras. -/
def HingeCond (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) : Prop :=
  ∀ u v a b : V, a ≠ b → IsAllowed H F {u, v, a} → IsAllowed H F {u, v, b} →
    ∃ i, 6 ≤ i ∧ i ≤ h ∧
      α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a b i).card

end TypedTriangle
