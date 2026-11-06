/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.Group.Nat

/-! # Compatibilidad del corte histórico con Lean/Mathlib 4.35.0-rc3

Este módulo conserva la ruta de importación del corte originado en 4.28.
Las seis declaraciones auxiliares de aquella versión ya existen en Mathlib
4.35.0-rc3; se reutilizan directamente, sin redeclararlas.
-/
