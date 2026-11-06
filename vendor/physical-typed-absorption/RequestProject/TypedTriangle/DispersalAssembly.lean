/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertDispersal

@[expose] public section

/-!
# Ensamblaje condicional del certificado compuesto (V15, opcional)

Suma de los certificados dispersados. Las entradas de V13/V14 (descomposición de `x` en
demandas físicas pequeñas, número de demandas `≤ A‖x‖₁`, conteo de frontera `≤ A·d(v)`) se
CONSERVAN como hipótesis explícitas: su instanciación requiere los adaptadores locales
(Compression real, H3/H4 → `PreparedRouting`) que no están en este espacio de trabajo.
Esto NO es T.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Dispersal

open TypedTriangle.SparseEdge

universe u v

variable {V : Type u} {I : Type v} [Fintype V]

lemma triBd_sum {ι : Type*} [Fintype ι] (c : ι → Finset V → ℤ) :
    triBd (fun T => ∑ i, c i T) = ∑ i, triBd (c i) := by
  funext e
  simp only [triBd, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma l1T_sum_le {ι : Type*} [Fintype ι] (c : ι → Finset V → ℤ) :
    l1T (fun T => ∑ i, c i T) ≤ ∑ i, l1T (c i) := by
  unfold l1T
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun T _ => Finset.abs_sum_le_sum_abs _ _)

lemma vload_sum_le {ι : Type*} [Fintype ι] (c : ι → Finset V → ℤ) (v : V) :
    vload (fun T => ∑ i, c i T) v ≤ ∑ i, vload (c i) v := by
  unfold vload
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun T _ => Finset.abs_sum_le_sum_abs _ _)

lemma qStar_le (K J : ℕ) {β : ℝ} {n : ℕ} (hβ : 0 < β) (hn : 0 < n) :
    (qStar K J β n : ℝ) ≤ 6 * K * J / (β * n) + 1 := by
  have hpos : (0 : ℝ) < β * n := mul_pos hβ (by exact_mod_cast hn)
  have h0 : (0 : ℝ) ≤ 6 * K * J / (β * n) := by positivity
  unfold qStar
  rcases le_total 1 ⌈(6 * K * J : ℝ) / (β * n)⌉₊ with h | h
  · rw [max_eq_right h]
    exact (Nat.ceil_lt_add_one h0).le
  · rw [max_eq_left h]
    push_cast
    linarith

/-- **Certificado compuesto** (condicional a las entradas de agrupación/frontera retenidas).
Si `x = ∑_i y_i` con `y_i` físicas de norma `≤ k`, `|ι| ≤ A‖x‖₁` y
`#{i : v ∈ front y_i} ≤ A·d(v)`, entonces existe un certificado con signo `c` de `x` con
`‖c‖₁ ≤ K'‖x‖₁` y congestión `∑_{T∋v}|c T| ≤ K'(d(v) + ‖x‖₁/n + 1)`, donde
`K' = KA + 6K²A/β + K`. -/
theorem assembled_certificate {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (x : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hdec : ∑ i, y i = x) (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k)
    (A : ℕ) (d : V → ℕ) (hJ : (Fintype.card ι : ℤ) ≤ A * l1E x)
    (hF : ∀ v, (univ.filter (fun i => v ∈ front (y i))).card ≤ A * d v) :
    ∃ c : Finset V → ℤ, IsCert G lab F c x ∧
      (l1T c : ℝ) ≤ (K * A + 6 * K ^ 2 * A / β + K) * l1E x ∧
      ∀ v, (vload c v : ℝ) ≤
        (K * A + 6 * K ^ 2 * A / β + K) * (d v + l1E x / Fintype.card V + 1) := by
  obtain ⟨c, hc, hsum, -, hload⟩ := prepared_core_dispersal_fintype hU P hβ hn y hy hk
  set n := Fintype.card V
  set J := Fintype.card ι
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ l1E x := by exact_mod_cast Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hJR : (J : ℝ) ≤ A * l1E x := by exact_mod_cast hJ
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hKp : (0 : ℝ) ≤ 6 * K ^ 2 * A / β := by positivity
  refine ⟨fun T => ∑ i, c i T, ⟨fun T hT => ?_, ?_⟩, ?_, fun v => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    exact (hc i).1.1 T hi
  · rw [triBd_sum, ← hdec]
    exact Finset.sum_congr rfl (fun i _ => (hc i).1.2)
  · have h1 : (l1T (fun T => ∑ i, c i T) : ℝ) ≤ K * J := by
      have := (l1T_sum_le c).trans hsum
      exact_mod_cast this
    calc _ ≤ (K : ℝ) * J := h1
      _ ≤ K * (A * l1E x) := mul_le_mul_of_nonneg_left hJR hK0
      _ = (K * A) * l1E x := by ring
      _ ≤ _ := by nlinarith
  · have h1 : (vload (fun T => ∑ i, c i T) v : ℝ) ≤
        K * ((univ.filter (fun i => v ∈ front (y i))).card + qStar K J β n) := by
      have := (vload_sum_le c v).trans (hload v)
      exact_mod_cast this
    have hFv : ((univ.filter (fun i => v ∈ front (y i))).card : ℝ) ≤ A * d v := by
      exact_mod_cast hF v
    have hq := qStar_le K J hβ hn
    have hq' : (qStar K J β n : ℝ) ≤ 6 * K * A * l1E x / (β * n) + 1 := by
      refine hq.trans ?_
      have : 6 * K * J / (β * n) ≤ 6 * K * A * l1E x / (β * n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (6 * K : ℝ) * J ≤ 6 * K * (A * l1E x) :=
          mul_le_mul_of_nonneg_left hJR (by positivity)
        linarith
      linarith
    have hd0 : (0 : ℝ) ≤ d v := Nat.cast_nonneg _
    have hxn : (0 : ℝ) ≤ l1E x / n := by positivity
    have key : (6 * K * A * l1E x / (β * n)) * K = (6 * K ^ 2 * A / β) * (l1E x / n) := by
      field_simp
    calc _ ≤ (K : ℝ) * ((univ.filter (fun i => v ∈ front (y i))).card + qStar K J β n) := h1
      _ ≤ K * (A * d v + (6 * K * A * l1E x / (β * n) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK0; linarith
      _ = (K * A) * d v + (6 * K ^ 2 * A / β) * (l1E x / n) + K := by
          rw [← key]; ring
      _ ≤ _ := by
          have e1 : (K * A : ℝ) * d v ≤ (K * A + 6 * K ^ 2 * A / β + K) * d v :=
            mul_le_mul_of_nonneg_right (by linarith) hd0
          have e2 : (6 * K ^ 2 * A / β) * (l1E x / n) ≤
              (K * A + 6 * K ^ 2 * A / β + K) * (l1E x / n) :=
            mul_le_mul_of_nonneg_right (by nlinarith) hxn
          nlinarith

end TypedTriangle.Dispersal
