/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.DispersalAssembly

@[expose] public section

/-!
# V16: ensamblaje con la frontera de TRES términos (la forma real de V13)

`assembled_certificate` (V15) supone `F(v) ≤ A·d(v)`, que V13 NO da: el enrutamiento real
sólo da `F(v) ≤ (4D+3)·d_abs(x)(v) + ⌈32De/(δn)⌉ + 2D`, con vértices auxiliares en los que
`d_abs(x)(v) = 0` y `F(v) > 0`. Aquí se sustituye esa premisa por el contrato genuino de tres
términos `F(v) ≤ a·d(v) + b·e/n + c` (`a, b, c ≥ 0`, `e = ‖x‖₁`); V15 queda intacto.

* `assembled_certificate_three_term`: cota exacta
  `vload ≤ K(a·d(v) + (b + 6KA/β)·e/n + c + 1)` y `‖c‖₁ ≤ KA·e`.
* `assembled_certificate_three_term_uniform`: una constante común
  `K' = K(A + a + b + 6KA/β + c + 1)` con `‖c‖₁ ≤ K'e` y congestión `≤ K'(d(v) + e/n + 1)`.
* `assembled_certificate_V13_frontier`: con la expresión EXACTA de V13 (techo incluido) y
  `J ≤ 2e`: congestión `≤ K((4D+3)d(v) + (32D/δ + 12K/β)e/n + 2D + 2)`.

El caso `e = 0` está incluido (entonces `J = 0`, `x = 0` y el certificado es el nulo: la
cota sigue valiendo porque todos los términos son `≥ 0`). Nada de esto es T.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Dispersal

open TypedTriangle.SparseEdge

universe u v

variable {V : Type u} {I : Type v} [Fintype V]

lemma l1E_nonneg (x : Sym2 V → ℤ) : 0 ≤ l1E x := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- **Ensamblaje con frontera de tres términos.** Entradas: `x = ∑_i y_i` (demandas físicas
de norma `≤ k`), `|ι| ≤ A‖x‖₁`, y el contrato de frontera de tres términos
`#{i : v ∈ front y_i} ≤ a·d(v) + b·‖x‖₁/n + c`. Salida: certificado con signo de borde exacto
`x`, norma `≤ KA‖x‖₁` y congestión `≤ K(a·d(v) + (b + 6KA/β)·‖x‖₁/n + c + 1)`. -/
theorem assembled_certificate_three_term {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (x : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hdec : ∑ i, y i = x) (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k)
    (A : ℕ) (hJ : (Fintype.card ι : ℤ) ≤ A * l1E x)
    (a b c : ℝ) (d : V → ℝ)
    (hF : ∀ v, ((univ.filter (fun i => v ∈ front (y i))).card : ℝ) ≤
      a * d v + b * l1E x / Fintype.card V + c) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ K * A * l1E x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * (a * d v + (b + 6 * K * A / β) * (l1E x / Fintype.card V) + c + 1) := by
  obtain ⟨cf, hc, hsum, -, hload⟩ := prepared_core_dispersal_fintype hU P hβ hn y hy hk
  set n := Fintype.card V
  set J := Fintype.card ι
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJR : (J : ℝ) ≤ A * l1E x := by exact_mod_cast hJ
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  refine ⟨fun T => ∑ i, cf i T, ⟨fun T hT => ?_, ?_⟩, ?_, fun v => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    exact (hc i).1.1 T hi
  · rw [triBd_sum, ← hdec]
    exact Finset.sum_congr rfl (fun i _ => (hc i).1.2)
  · have h1 : (l1T (fun T => ∑ i, cf i T) : ℝ) ≤ K * J := by
      have := (l1T_sum_le cf).trans hsum
      exact_mod_cast this
    calc _ ≤ (K : ℝ) * J := h1
      _ ≤ K * (A * l1E x) := mul_le_mul_of_nonneg_left hJR hK0
      _ = K * A * l1E x := by ring
  · have h1 : (vload (fun T => ∑ i, cf i T) v : ℝ) ≤
        K * ((univ.filter (fun i => v ∈ front (y i))).card + qStar K J β n) := by
      have := (vload_sum_le cf v).trans (hload v)
      exact_mod_cast this
    have hq := qStar_le K J hβ hn
    have hq' : (qStar K J β n : ℝ) ≤ 6 * K * A / β * (l1E x / n) + 1 := by
      refine hq.trans ?_
      have : 6 * K * J / (β * n) ≤ 6 * K * A / β * (l1E x / n) := by
        rw [div_mul_div_comm]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (6 * K : ℝ) * J ≤ 6 * K * (A * l1E x) :=
          mul_le_mul_of_nonneg_left hJR (by positivity)
        linarith
      linarith
    have hFv := hF v
    calc _ ≤ (K : ℝ) * ((univ.filter (fun i => v ∈ front (y i))).card + qStar K J β n) := h1
      _ ≤ K * ((a * d v + b * l1E x / n + c) + (6 * K * A / β * (l1E x / n) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK0; linarith
      _ = K * (a * d v + (b + 6 * K * A / β) * (l1E x / n) + c + 1) := by ring

/-- **Constante común.** Bajo las mismas entradas, con `a, b, c ≥ 0` y `d ≥ 0`, existe un
certificado con `‖cert‖₁ ≤ K'‖x‖₁` y congestión `≤ K'(d(v) + ‖x‖₁/n + 1)`, donde
`K' = K(A + a + b + 6KA/β + c + 1)` depende sólo de `K, A, a, b, c, β` (no de `n`, `x`). -/
theorem assembled_certificate_three_term_uniform {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (x : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hdec : ∑ i, y i = x) (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k)
    (A : ℕ) (hJ : (Fintype.card ι : ℤ) ≤ A * l1E x)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (d : V → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hF : ∀ v, ((univ.filter (fun i => v ∈ front (y i))).card : ℝ) ≤
      a * d v + b * l1E x / Fintype.card V + c) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ K * (A + a + b + 6 * K * A / β + c + 1) * l1E x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * (A + a + b + 6 * K * A / β + c + 1) * (d v + l1E x / Fintype.card V + 1) := by
  obtain ⟨cert, hcert, hl1, hload⟩ :=
    assembled_certificate_three_term hU P hβ hn x y hdec hy hk A hJ a b c d hF
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ l1E x := by exact_mod_cast l1E_nonneg x
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ 6 * K * A / β := by positivity
  have hxn : (0 : ℝ) ≤ l1E x / Fintype.card V := by positivity
  refine ⟨cert, hcert, ?_, fun v => ?_⟩
  · refine hl1.trans ?_
    have : (K : ℝ) * A ≤ K * (A + a + b + 6 * K * A / β + c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    exact mul_le_mul_of_nonneg_right this hx0
  · refine (hload v).trans ?_
    set S : ℝ := A + a + b + 6 * K * A / β + c + 1
    have hdv := hd v
    have key : a * d v + (b + 6 * K * A / β) * (l1E x / Fintype.card V) + c + 1 ≤
        S * (d v + l1E x / Fintype.card V + 1) := by
      have e1 : a * d v ≤ S * d v := mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hdv
      have e2 : (b + 6 * K * A / β) * (l1E x / Fintype.card V) ≤
          S * (l1E x / Fintype.card V) :=
        mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hxn
      have e3 : c + 1 ≤ S := by simp only [S]; linarith
      nlinarith
    calc (K : ℝ) * (a * d v + (b + 6 * K * A / β) * (l1E x / Fintype.card V) + c + 1)
        ≤ K * (S * (d v + l1E x / Fintype.card V + 1)) := mul_le_mul_of_nonneg_left key hK0
      _ = K * S * (d v + l1E x / Fintype.card V + 1) := by ring

/-- `⌈t⌉₊ ≤ t + 1` para `t ≥ 0`, en la forma usada por V13. -/
lemma ceil_V13_le (D : ℕ) {δ : ℝ} (hδ : 0 < δ) (e : ℝ) (he : 0 ≤ e) (n : ℕ) :
    (⌈32 * D * e / (δ * n)⌉₊ : ℝ) ≤ 32 * D / δ * (e / n) + 1 := by
  have h0 : (0 : ℝ) ≤ 32 * D * e / (δ * n) := by
    apply div_nonneg (by positivity) (mul_nonneg hδ.le (Nat.cast_nonneg _))
  have := (Nat.ceil_lt_add_one h0).le
  have heq : 32 * D * e / (δ * n) = 32 * D / δ * (e / n) := by
    rw [div_mul_div_comm]
  linarith

/-- **La frontera EXACTA de V13** (`routing_budget_weak`/`routing_budget_real`):
`F(v) ≤ (4D+3)·d(v) + ⌈32De/(δn)⌉ + 2D` con `e = ‖x‖₁`, y `J ≤ 2e`. Resultado: congestión
`≤ K((4D+3)d(v) + (32D/δ + 12K/β)e/n + 2D + 2)` (la cota segura pedida) y norma `≤ 2Ke`.
Se conservan los términos `e/n` y constante. -/
theorem assembled_certificate_V13_frontier {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (x : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hdec : ∑ i, y i = x) (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k)
    (hJ : (Fintype.card ι : ℤ) ≤ 2 * l1E x)
    (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (d : V → ℤ)
    (hF : ∀ v, ((univ.filter (fun i => v ∈ front (y i))).card : ℤ) ≤
      (4 * D + 3) * d v + ⌈32 * D * (l1E x : ℝ) / (δ * Fintype.card V)⌉₊ + 2 * D) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ 2 * K * l1E x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * ((4 * D + 3) * d v + (32 * D / δ + 12 * K / β) * (l1E x / Fintype.card V) +
          2 * D + 2) := by
  have hx0 : (0 : ℝ) ≤ l1E x := by exact_mod_cast l1E_nonneg x
  have hF' : ∀ v, ((univ.filter (fun i => v ∈ front (y i))).card : ℝ) ≤
      (4 * D + 3) * (d v : ℝ) + (32 * D / δ) * l1E x / Fintype.card V + (2 * D + 1) := by
    intro v
    have h1 : (((univ.filter (fun i => v ∈ front (y i))).card : ℤ) : ℝ) ≤
        (((4 * D + 3) * d v + ⌈32 * D * (l1E x : ℝ) / (δ * Fintype.card V)⌉₊ + 2 * D : ℤ) : ℝ) :=
      by exact_mod_cast hF v
    push_cast at h1
    have h2 := ceil_V13_le D hδ (l1E x) hx0 (Fintype.card V)
    have h3 : (32 * D / δ) * (l1E x : ℝ) / Fintype.card V = 32 * D / δ * (l1E x / Fintype.card V) :=
      by ring
    linarith
  obtain ⟨cert, hcert, hl1, hload⟩ := assembled_certificate_three_term hU P hβ hn x y hdec hy hk
    2 (by exact_mod_cast hJ) (4 * D + 3) (32 * D / δ) (2 * D + 1) (fun v => (d v : ℝ)) hF'
  refine ⟨cert, hcert, by push_cast at hl1; linarith, fun v => ?_⟩
  refine (hload v).trans (le_of_eq ?_)
  push_cast
  ring

/-- **Constante común para la frontera de V13**: `K' = K(4D+3 + 32D/δ + 12K/β + 2D + 2)`
(independiente de `n`, `x`), con `d ≥ 0`: norma `≤ K'e` y congestión `≤ K'(d(v) + e/n + 1)`. -/
theorem assembled_certificate_V13_frontier_uniform {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (x : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hdec : ∑ i, y i = x) (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k)
    (hJ : (Fintype.card ι : ℤ) ≤ 2 * l1E x)
    (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (d : V → ℤ) (hd : ∀ v, 0 ≤ d v)
    (hF : ∀ v, ((univ.filter (fun i => v ∈ front (y i))).card : ℤ) ≤
      (4 * D + 3) * d v + ⌈32 * D * (l1E x : ℝ) / (δ * Fintype.card V)⌉₊ + 2 * D) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ K * (4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2) * l1E x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * (4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2) *
          (d v + l1E x / Fintype.card V + 1) := by
  obtain ⟨cert, hcert, hl1, hload⟩ :=
    assembled_certificate_V13_frontier hU P hβ hn x y hdec hy hk hJ D δ hδ d hF
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ l1E x := by exact_mod_cast l1E_nonneg x
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have p1 : (0 : ℝ) ≤ 32 * D / δ := by positivity
  have p2 : (0 : ℝ) ≤ 12 * K / β := by positivity
  have hxn : (0 : ℝ) ≤ l1E x / Fintype.card V := by positivity
  set S : ℝ := 4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2
  refine ⟨cert, hcert, hl1.trans ?_, fun v => (hload v).trans ?_⟩
  · have : (2 : ℝ) * K ≤ K * S := by
      have : (2 : ℝ) ≤ S := by simp only [S]; linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right this hx0
  · have hdv : (0 : ℝ) ≤ d v := by exact_mod_cast hd v
    have key : (4 * D + 3) * (d v : ℝ) + (32 * D / δ + 12 * K / β) * (l1E x / Fintype.card V) +
        2 * D + 2 ≤ S * (d v + l1E x / Fintype.card V + 1) := by
      have e1 : (4 * D + 3) * (d v : ℝ) ≤ S * d v :=
        mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hdv
      have e2 : (32 * D / δ + 12 * K / β) * (l1E x / Fintype.card V) ≤
          S * (l1E x / Fintype.card V) :=
        mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hxn
      have e3 : (2 * D + 2 : ℝ) ≤ S := by simp only [S]; linarith
      nlinarith
    calc _ ≤ (K : ℝ) * (S * (d v + l1E x / Fintype.card V + 1)) :=
          mul_le_mul_of_nonneg_left key hK0
      _ = _ := by ring

end TypedTriangle.Dispersal
