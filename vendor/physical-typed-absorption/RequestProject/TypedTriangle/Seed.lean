/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Lattice

@[expose] public section

/-!
# Semillas: grados de enlace (P01, primer paso) e identidad exacta del transporte (P06)

* `card_triOn_ge`, `card_triOn_le`: de (H1), cada arista está en al menos `n / C` y a lo
  sumo `C n` triángulos permitidos (§1 del ledger: cada vértice de cada enlace tiene grado
  al menos `n / C`).
* `bdry`: el operador de bordes `A_G` sobre pesos reales de triángulos.
* `transport_identity`: identidad exacta (L13) del transporte de semillas con un único
  pivote por arista borrada, compartido entre los certificados (S05 §4, S06). Se demuestra
  para certificados reales arbitrarios que satisfacen la ecuación de borde (4) de S05; las
  cotas de positividad (L14) dependen de la construcción aleatoria de esos certificados y
  NO se demuestran aquí.
* `transport_exact`: caso `ε = 0` (conservación exacta de la carga uno al borrar un grafo
  basal).
* `transport_error_bound`: el error se multiplica por `1 + P`, donde `P` acota la masa de
  pivotes en cada arista: no aparece un término aditivo debido al stock.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Triángulos permitidos que contienen la arista `e`. -/
def triOn (H : Host V I) (F : Set (Multiset I)) (e : Sym2 V) : Finset (Finset V) :=
  (allowed H F).filter (fun T => e ∈ triEdges T)

/-- **P01, primer paso.** Si `φ` es una semilla exacta difusa de constante `C > 0`, cada
arista está en al menos `n / C` triángulos permitidos. -/
theorem card_triOn_ge {H : Host V I} {F : Set (Multiset I)} {C : ℝ} {φ : Finset V → ℝ}
    (hφ : IsDiffuseSeed H F C φ) (hC : 0 < C) {e : Sym2 V} (he : e ∈ H.G.edgeSet) :
    (Fintype.card V : ℝ) / C ≤ (triOn H F e).card := by
  have hsum := hφ.2 e he
  have hn : (0 : ℝ) < Fintype.card V := by
    induction e using Sym2.ind with
    | _ x y => exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  have hle : ∑ T ∈ triOn H F e, φ T ≤ ∑ _T ∈ triOn H F e, C / Fintype.card V := by
    refine Finset.sum_le_sum fun T hT => ?_
    have hTA : IsAllowed H F T := by
      simp only [triOn, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact hT.1
    exact (hφ.1 T hTA).2
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  unfold triOn at hle
  rw [hsum] at hle
  rw [div_le_iff₀ hC]
  have : (1 : ℝ) * Fintype.card V ≤ ((allowed H F).filter (fun T => e ∈ triEdges T)).card *
      (C / Fintype.card V) * Fintype.card V := by
    exact mul_le_mul_of_nonneg_right hle hn.le
  rw [mul_assoc, div_mul_cancel₀ _ hn.ne'] at this
  unfold triOn
  linarith

/-- Cota superior simétrica: cada arista está en a lo sumo `C n` triángulos permitidos. -/
theorem card_triOn_le {H : Host V I} {F : Set (Multiset I)} {C : ℝ} {φ : Finset V → ℝ}
    (hφ : IsDiffuseSeed H F C φ) (hC : 0 < C) {e : Sym2 V} (he : e ∈ H.G.edgeSet) :
    ((triOn H F e).card : ℝ) ≤ C * Fintype.card V := by
  have hsum := hφ.2 e he
  have hn : (0 : ℝ) < Fintype.card V := by
    induction e using Sym2.ind with
    | _ x y => exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  have hge : ∑ _T ∈ triOn H F e, 1 / (C * Fintype.card V) ≤ ∑ T ∈ triOn H F e, φ T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have hTA : IsAllowed H F T := by
      simp only [triOn, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact hT.1
    exact (hφ.1 T hTA).1
  rw [Finset.sum_const, nsmul_eq_mul] at hge
  unfold triOn at hge
  rw [hsum] at hge
  have hCn : 0 < C * Fintype.card V := mul_pos hC hn
  rw [mul_one_div, div_le_one hCn] at hge
  unfold triOn
  exact hge

/-! ## Operador de bordes y transporte -/

/-- Indicador real de un conjunto de aristas. -/
def indR (J : Finset (Sym2 V)) (e : Sym2 V) : ℝ := if e ∈ J then 1 else 0

/-- Operador de bordes `A_G w` para pesos reales `w` de triángulos permitidos. -/
def bdry (H : Host V I) (F : Set (Multiset I)) (w : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ T ∈ allowed H F, w T * indR (triEdges T) e

lemma bdry_eq_sum_triOn (H : Host V I) (F : Set (Multiset I)) (w : Finset V → ℝ)
    (e : Sym2 V) : bdry H F w e = ∑ T ∈ triOn H F e, w T := by
  unfold bdry triOn
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : e ∈ triEdges T <;> simp [indR, h]

/-- Una semilla exacta difusa tiene borde uno en cada arista. -/
lemma IsDiffuseSeed.bdry_eq_one {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : IsDiffuseSeed H F C φ) {e : Sym2 V} (he : e ∈ H.G.edgeSet) :
    bdry H F φ e = 1 := by
  rw [bdry_eq_sum_triOn]; exact hφ.2 e he

lemma bdry_eq_zero_of_not_mem (H : Host V I) (F : Set (Multiset I)) (w : Finset V → ℝ)
    {e : Sym2 V} (he : e ∉ edges H) : bdry H F w e = 0 := by
  unfold bdry
  refine Finset.sum_eq_zero fun T hT => ?_
  have hTA : IsAllowed H F T := by
    simpa [allowed] using hT
  have : e ∉ triEdges T := fun h => he (triEdges_subset_edges hTA h)
  simp [indR, this]

omit [Fintype V] in
/-- Una descomposición cubre cada arista de `J` exactamente una vez. -/
lemma sum_indR_of_isDecomposition {H : Host V I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F J D)
    (e : Sym2 V) : ∑ T ∈ D, indR (triEdges T) e = indR J e := by
  by_cases he : e ∈ J
  · obtain ⟨T, hT, heT⟩ := hD.exists_mem he
    rw [Finset.sum_eq_single T]
    · simp [indR, heT, he]
    · intro T' hT' hne
      simp only [indR]; rw [if_neg]; intro h'; exact hne (hD.unique hT' hT h' heT)
    · intro h; exact absurd hT h
  · simp only [indR, if_neg he]
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [if_neg]; intro h'; exact he (hD.subset hT h')

/-- Contribución de los pivotes de las aristas borradas de `T`. -/
def pivotTerm (Fst : Finset (Sym2 V)) (piv : Sym2 V → Finset V) (T : Finset V)
    (e : Sym2 V) : ℝ :=
  ∑ f ∈ Fst, indR (triEdges T) f * indR (triEdges (piv f)) e

/-- El peso transportado `ν = ∑_T μ_T c_T − ∑_{T ∈ D} c_T` de S05 (11). -/
def transported (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (D : Finset (Finset V)) (cert : Finset V → Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ T ∈ allowed H F, μ T * cert T S - ∑ T ∈ D, cert T S

/-- **Identidad exacta del transporte (L13).** Sea `Fst` un grafo basal con descomposición
`D`, `piv f` un único pivote por arista borrada, y para cada triángulo permitido `T` un
certificado real `cert T` con `∂ cert T = 1_T − ∑_{f ∈ E(T) ∩ Fst} 1_{piv f}`. Entonces el
peso transportado `ν` satisfece, en cada coordenada `e`,
`∂ν e = ∂μ e − 1_{Fst} e − ∑_{f ∈ Fst} (∂μ f − 1) 1_{piv f} e`.
El carácter basal de `Fst` es el que cancela los pivotes. -/
theorem transport_identity {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (piv : Sym2 V → Finset V) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTerm Fst piv T e)
    (e : Sym2 V) :
    bdry H F (transported H F μ D cert) e =
      bdry H F μ e - indR Fst e -
        ∑ f ∈ Fst, (bdry H F μ f - 1) * indR (triEdges (piv f)) e := by
  have hDA : ∀ T ∈ D, T ∈ allowed H F := fun T hT => by
    simpa [allowed] using hD.1 T hT
  -- linealidad del borde
  have hlin : bdry H F (transported H F μ D cert) e =
      ∑ T ∈ allowed H F, μ T * bdry H F (cert T) e - ∑ T ∈ D, bdry H F (cert T) e := by
    unfold bdry transported
    simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun S _ => by ring
    · rw [Finset.sum_comm]
  rw [hlin]
  have h1 : ∑ T ∈ allowed H F, μ T * bdry H F (cert T) e =
      bdry H F μ e - ∑ f ∈ Fst, bdry H F μ f * indR (triEdges (piv f)) e := by
    rw [Finset.sum_congr rfl fun T hT => by rw [hcert T hT e]]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    unfold pivotTerm bdry
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun T _ => by ring
  have h2 : ∑ T ∈ D, bdry H F (cert T) e =
      indR Fst e - ∑ f ∈ Fst, indR (triEdges (piv f)) e := by
    rw [Finset.sum_congr rfl fun T hT => by rw [hcert T (hDA T hT) e]]
    rw [Finset.sum_sub_distrib, sum_indR_of_isDecomposition hD e]
    congr 1
    unfold pivotTerm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [← Finset.sum_mul, sum_indR_of_isDecomposition hD f]
    simp [indR, hf]
  rw [h1, h2]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

/-- **(L13), forma del ledger.** Si `∂μ = 1 + r` en las aristas de `G`, entonces en cada
arista superviviente `e ∉ Fst`,
`∂ν e − 1 = r e − ∑_{f ∈ Fst} r f · 1_{piv f}(e)`. -/
theorem transport_error_identity {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {r : Sym2 V → ℝ} (hμ : ∀ f ∈ edges H, bdry H F μ f = 1 + r f)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H)
    (piv : Sym2 V → Finset V) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTerm Fst piv T e)
    {e : Sym2 V} (he : e ∈ edges H) (heF : e ∉ Fst) :
    bdry H F (transported H F μ D cert) e - 1 =
      r e - ∑ f ∈ Fst, r f * indR (triEdges (piv f)) e := by
  rw [transport_identity hD piv cert hcert e, hμ e he]
  rw [Finset.sum_congr rfl fun f hf => by rw [hμ f (hFst hf)]]
  simp only [indR, if_neg heF, add_sub_cancel_left]
  ring

/-- **Conservación exacta (S05, caso `ε = 0`).** Si `μ` es exacta (`∂μ = 1` en `E`) y los
pivotes son triángulos permitidos, entonces `∂ν = 1_{E ∖ Fst}` en todas las coordenadas. -/
theorem transport_exact {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    (hμ : ∀ f ∈ edges H, bdry H F μ f = 1)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H)
    (piv : Sym2 V → Finset V) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTerm Fst piv T e)
    (e : Sym2 V) :
    bdry H F (transported H F μ D cert) e = indR (edges H \ Fst) e := by
  rw [transport_identity hD piv cert hcert e]
  rw [Finset.sum_congr rfl fun f hf => by rw [hμ f (hFst hf)]]
  simp only [sub_self, zero_mul, Finset.sum_const_zero, sub_zero]
  by_cases he : e ∈ edges H
  · rw [hμ e he]
    by_cases heF : e ∈ Fst <;> simp [indR, he, heF]
  · rw [bdry_eq_zero_of_not_mem H F μ he]
    have : e ∉ Fst := fun h => he (hFst h)
    simp [indR, he, this]

/-- **Error multiplicativo (L14, parte de cargas).** Si `|r| ≤ ε` en las aristas y cada
arista superviviente está en a lo sumo `P` pivotes de aristas borradas, entonces
`|∂ν e − 1| ≤ (1 + P) ε`: el stock no añade un término aditivo. -/
theorem transport_error_bound {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {r : Sym2 V → ℝ} (hμ : ∀ f ∈ edges H, bdry H F μ f = 1 + r f) {ε P : ℝ}
    (hr : ∀ f ∈ edges H, |r f| ≤ ε)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H)
    (piv : Sym2 V → Finset V) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTerm Fst piv T e)
    {e : Sym2 V} (he : e ∈ edges H) (heF : e ∉ Fst)
    (hP : ((Fst.filter (fun f => e ∈ triEdges (piv f))).card : ℝ) ≤ P) :
    |bdry H F (transported H F μ D cert) e - 1| ≤ (1 + P) * ε := by
  rw [transport_error_identity hμ hD hFst piv cert hcert he heF]
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hr e he)
  have hsum : |∑ f ∈ Fst, r f * indR (triEdges (piv f)) e| ≤ P * ε := by
    calc |∑ f ∈ Fst, r f * indR (triEdges (piv f)) e|
        ≤ ∑ f ∈ Fst, |r f * indR (triEdges (piv f)) e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f ∈ Fst, ε * indR (triEdges (piv f)) e := by
          refine Finset.sum_le_sum fun f hf => ?_
          by_cases h : e ∈ triEdges (piv f)
          · simp [indR, h, hr f (hFst hf)]
          · simp [indR, h]
      _ = ε * (Fst.filter (fun f => e ∈ triEdges (piv f))).card := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun f _ => ?_
          by_cases h : e ∈ triEdges (piv f) <;> simp [indR, h]
      _ ≤ ε * P := mul_le_mul_of_nonneg_left hP hε
      _ = P * ε := mul_comm _ _
  calc |r e - ∑ f ∈ Fst, r f * indR (triEdges (piv f)) e|
      ≤ |r e| + |∑ f ∈ Fst, r f * indR (triEdges (piv f)) e| := abs_sub _ _
    _ ≤ ε + P * ε := add_le_add (hr e he) hsum
    _ = (1 + P) * ε := by ring

end TypedTriangle
