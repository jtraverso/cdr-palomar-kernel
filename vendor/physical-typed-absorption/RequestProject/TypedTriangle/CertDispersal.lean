/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SubtypeCert

@[expose] public section

/-!
# Dispersión secuencial de certificados físicos (V15, S26 §6)

1. `greedy_dispersal`: invariante del contador voraz, paramétrico en los candidatos
   (para cada demanda y cada conjunto prohibido `Z` pequeño y disjunto de su frontera, un
   certificado que evita `Z`). Cuenta UN uso auxiliar por certificado y por vértice fuera de
   la frontera de su demanda (ocurrencias de índices `j`, no raíces distintas).
2. `PreparedCore`: propiedades del núcleo preparado (H3/H4/orden en cada host borrado
   `Surv Z` con `|Z| ≤ βn`, y persistencia ENTERA del retículo físico).
   `UniformCertOn`: el enunciado de `uniformCert_of_H3H4` (no presente en este espacio de
   trabajo) para hosts finitos arbitrarios, con constantes fijadas antes del host.
3. `cert_avoiding`: el candidato se CONSTRUYE en el host borrado `Surv Z` y se extiende por
   cero; `prepared_core_dispersal`, `prepared_core_dispersal_fintype`: el consumidor final.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Dispersal

open TypedTriangle.SparseEdge

universe u v

variable {V : Type u} {I : Type v} [Fintype V]

/-! ### 1. Invariante voraz paramétrico -/

/-- Usos auxiliares de `v` por los certificados `j < t`: `v` usado por `c j` y fuera de la
frontera de `y j`. Se cuentan índices `j` (ocurrencias). -/
def aux (c : ℕ → Finset V → ℤ) (y : ℕ → Sym2 V → ℤ) (t : ℕ) (v : V) : ℕ :=
  ((range t).filter (fun j => v ∈ verts (c j) ∧ v ∉ front (y j))).card

/-- Usos de frontera: `F(v) = #{j < J : v ∈ front (y j)}`. -/
def frontCount (y : ℕ → Sym2 V → ℤ) (J : ℕ) (v : V) : ℕ :=
  ((range J).filter (fun j => v ∈ front (y j))).card

lemma sum_aux (c : ℕ → Finset V → ℤ) (y : ℕ → Sym2 V → ℤ) (t : ℕ) :
    ∑ v, aux c y t v = ∑ j ∈ range t, (univ.filter
      (fun v => v ∈ verts (c j) ∧ v ∉ front (y j))).card := by
  unfold aux
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma sum_aux_le {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (c : ℕ → Finset V → ℤ) (y : ℕ → Sym2 V → ℤ) (t K : ℕ)
    (hc : ∀ j < t, (∀ T, c j T ≠ 0 → IsAllowed G lab F T) ∧ l1T (c j) ≤ K) :
    ((∑ v, aux c y t v : ℕ) : ℤ) ≤ 3 * K * t := by
  rw [sum_aux]
  push_cast
  have : ∀ j ∈ range t, (((univ.filter
      (fun v => v ∈ verts (c j) ∧ v ∉ front (y j))).card : ℕ) : ℤ) ≤ 3 * K := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h1 : (univ.filter (fun v => v ∈ verts (c j) ∧ v ∉ front (y j))).card ≤
        (verts (c j)).card :=
      Finset.card_le_card (fun v hv => (Finset.mem_filter.1 hv).2.1)
    have h2 := card_verts_le (c j) (hc j hj').1
    have h3 := (hc j hj').2
    have : (((univ.filter (fun v => v ∈ verts (c j) ∧ v ∉ front (y j))).card : ℕ) : ℤ) ≤
        (verts (c j)).card := by exact_mod_cast h1
    linarith
  calc _ ≤ ∑ j ∈ range t, (3 * K : ℤ) := Finset.sum_le_sum this
    _ = 3 * K * t := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- El conjunto saturado `{v : q ≤ aux v}` tiene tamaño `≤ B` si `3KJ ≤ qB`. -/
lemma card_saturated_le {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (c : ℕ → Finset V → ℤ) (y : ℕ → Sym2 V → ℤ) (t J K q : ℕ) (B : ℝ)
    (htJ : t ≤ J) (hq : 1 ≤ q) (hB : (3 * K * J : ℝ) ≤ q * B)
    (hc : ∀ j < t, (∀ T, c j T ≠ 0 → IsAllowed G lab F T) ∧ l1T (c j) ≤ K) :
    ((univ.filter (fun v => q ≤ aux c y t v)).card : ℝ) ≤ B := by
  set S := univ.filter (fun v => q ≤ aux c y t v)
  have h1 : q * S.card ≤ ∑ v, aux c y t v := by
    calc q * S.card = ∑ v ∈ S, q := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ S, aux c y t v := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.1 hv).2)
      _ ≤ ∑ v, aux c y t v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 := sum_aux_le (G := G) (lab := lab) (F := F) c y t K hc
  have h3 : ((q * S.card : ℕ) : ℝ) ≤ 3 * K * t := by
    have : ((q * S.card : ℕ) : ℤ) ≤ 3 * K * t := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast this
  push_cast at h3
  have ht : (t : ℝ) ≤ J := by exact_mod_cast htJ
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have : (q : ℝ) * S.card ≤ q * B := by nlinarith
  exact le_of_mul_le_mul_left this (by linarith)

/-- **Invariante voraz** (paramétrico en candidatos): procesando las demandas `j < J` en
orden, prohibiendo los saturados fuera de la frontera de la demanda actual, todo contador
auxiliar acaba `≤ q`. -/
theorem greedy_dispersal (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (y : ℕ → Sym2 V → ℤ) (J K q : ℕ) (B : ℝ) (hq : 1 ≤ q) (hB : (3 * K * J : ℝ) ≤ q * B)
    (cand : ∀ t < J, ∀ Z : Finset V, (Z.card : ℝ) ≤ B → Disjoint Z (front (y t)) →
      ∃ c, IsCert G lab F c (y t) ∧ l1T c ≤ K ∧ Disjoint (verts c) Z) :
    ∃ c : ℕ → Finset V → ℤ, (∀ j < J, IsCert G lab F (c j) (y j) ∧ l1T (c j) ≤ K) ∧
      ∀ v, aux c y J v ≤ q := by
  suffices H : ∀ t ≤ J, ∃ c : ℕ → Finset V → ℤ,
      (∀ j < t, IsCert G lab F (c j) (y j) ∧ l1T (c j) ≤ K) ∧ ∀ v, aux c y t v ≤ q from
    H J le_rfl
  intro t
  induction t with
  | zero => intro _; exact ⟨fun _ _ => 0, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun v => by simp [aux]⟩
  | succ t ih =>
    intro ht
    obtain ⟨c, hc, haux⟩ := ih (Nat.le_of_succ_le ht)
    have htJ : t < J := ht
    set S := univ.filter (fun v => q ≤ aux c y t v)
    have hS := card_saturated_le (G := G) (lab := lab) (F := F) c y t J K q B htJ.le hq hB
      (fun j hj => ⟨(hc j hj).1.1, (hc j hj).2⟩)
    set Z := S \ front (y t)
    have hZ : (Z.card : ℝ) ≤ B :=
      le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) hS
    have hZd : Disjoint Z (front (y t)) := Finset.sdiff_disjoint
    obtain ⟨ct, hct, hctK, hctZ⟩ := cand t htJ Z hZ hZd
    let c' : ℕ → Finset V → ℤ := fun j => if j = t then ct else c j
    have hc'old : ∀ j < t, c' j = c j := fun j hj => by simp [c', hj.ne]
    have hc't : c' t = ct := by simp [c']
    have haux_eq : ∀ v, aux c' y t v = aux c y t v := by
      intro v
      unfold aux
      congr 1
      refine Finset.filter_congr (fun j hj => ?_)
      rw [hc'old j (Finset.mem_range.1 hj)]
    refine ⟨c', fun j hj => ?_, fun v => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hc'old j hj]; exact hc j hj
      · rw [hc't]; exact ⟨hct, hctK⟩
    · have hsplit : aux c' y (t + 1) v = aux c' y t v +
          (if v ∈ verts ct ∧ v ∉ front (y t) then 1 else 0) := by
        unfold aux
        rw [Finset.range_add_one, Finset.filter_insert, hc't]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]
        · rfl
      rw [hsplit, haux_eq]
      split_ifs with h
      · have hvZ : v ∉ Z := fun hvZ => Finset.disjoint_left.1 hctZ h.1 hvZ
        have hvS : v ∉ S := fun hvS => hvZ (Finset.mem_sdiff.2 ⟨hvS, h.2⟩)
        have : aux c y t v < q := by
          by_contra hh
          exact hvS (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hh⟩)
        omega
      · simpa using haux v

/-- Masa total: `∑_{j<J} ‖c_j‖₁ ≤ K J`. -/
lemma sum_l1T_le (c : ℕ → Finset V → ℤ) (J K : ℕ) (hc : ∀ j < J, l1T (c j) ≤ K) :
    ∑ j ∈ range J, l1T (c j) ≤ K * J := by
  calc _ ≤ ∑ j ∈ range J, (K : ℤ) := Finset.sum_le_sum (fun j hj => hc j (Finset.mem_range.1 hj))
    _ = K * J := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- Congestión absoluta: `∑_{j<J} ∑_{T ∋ v} |c_j T| ≤ K (F(v) + aux(v))`. -/
lemma sum_vload_le (c : ℕ → Finset V → ℤ) (y : ℕ → Sym2 V → ℤ) (J K : ℕ)
    (hc : ∀ j < J, l1T (c j) ≤ K) (v : V) :
    ∑ j ∈ range J, vload (c j) v ≤ K * (frontCount y J v + aux c y J v) := by
  have hpt : ∀ j ∈ range J, vload (c j) v ≤
      K * ((if v ∈ front (y j) then 1 else 0) +
        (if v ∈ verts (c j) ∧ v ∉ front (y j) then 1 else 0)) := by
    intro j hj
    have hK := hc j (Finset.mem_range.1 hj)
    by_cases hv : v ∈ verts (c j)
    · have := vload_le_l1T (c j) v
      by_cases hf : v ∈ front (y j)
      · simp [hf]; linarith
      · simp [hf, hv]; linarith
    · rw [vload_eq_zero_of_not_mem _ hv]
      positivity
  refine le_trans (Finset.sum_le_sum hpt) (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  unfold frontCount aux
  simp only [Finset.card_filter]
  push_cast
  rfl

/-! ### 2. Núcleo preparado y enunciado del certificado uniforme -/

/-- Enunciado de `uniformCert_of_H3H4` con constantes `N₀, K` (fijadas antes del host) para
demandas físicas de norma `≤ k`, sobre CUALQUIER host finito en el universo `u`.
`uniformCert_of_H3H4` no está en este espacio de trabajo: se pasa como hipótesis explícita y
el adaptador local debe instanciarla. -/
def UniformCertOn (F : Set (Multiset I)) (α : ℝ) (h N₀ k K : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) (lab : W → I),
    CommonNbrCond G lab F α → HingeCond G lab F α h → N₀ ≤ Fintype.card W →
    ∀ y ∈ lattice G lab F, l1E y ≤ k →
      ∃ c : Finset W → ℤ, IsCert G lab F c y ∧ l1T c ≤ K

/-- **Núcleo preparado** (propiedades intermedias, NO hipótesis de T). Para todo conjunto
físico `Z` con `|Z| ≤ βn`, el host en el subtipo `Surv Z` cumple H3(α), H4(α,h), tiene orden
`≥ N₀`, y el retículo físico persiste exactamente (enteramente) bajo el borrado. -/
structure PreparedCore (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (α : ℝ)
    (h N₀ : ℕ) (β : ℝ) : Prop where
  h3 : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
    CommonNbrCond (subG G Z) (subLab lab Z) F α
  h4 : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
    HingeCond (subG G Z) (subLab lab Z) F α h
  order : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V → N₀ ≤ Fintype.card (Surv Z)
  lattice_persist : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
    ∀ y ∈ lattice G lab F, (∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) →
      restr Z y ∈ lattice (subG G Z) (subLab lab Z) F

/-! ### 3. Construcción del candidato y consumidor final -/

/-- Una demanda se anula en las aristas que tocan un conjunto disjunto de su frontera. -/
lemma vanish_of_disjoint_front {y : Sym2 V → ℤ} {Z : Finset V}
    (hZ : Disjoint Z (front y)) : ∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0 := by
  rintro e ⟨z, hz, hze⟩
  by_contra hne
  exact Finset.disjoint_left.1 hZ hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hne, hze⟩)

/-- **Certificado que evita `Z`, construido en el host borrado.** La demanda se restringe a
`Surv Z` (persistencia del retículo), se aplica el certificado uniforme en `Surv Z`
(H3/H4/orden del núcleo preparado) y se extiende por cero. -/
theorem cert_avoiding {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ}
    {h N₀ k K : ℕ} {β : ℝ} (hU : UniformCertOn.{u} F α h N₀ k K)
    (P : PreparedCore G lab F α h N₀ β) {y : Sym2 V → ℤ} (hy : y ∈ lattice G lab F)
    (hk : l1E y ≤ k) (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V)
    (hZd : Disjoint Z (front y)) :
    ∃ c, IsCert G lab F c y ∧ l1T c ≤ K ∧ Disjoint (verts c) Z := by
  have hvan := vanish_of_disjoint_front hZd
  obtain ⟨c0, hc0, hc0K⟩ := hU (Surv Z) (subG G Z) (subLab lab Z) (P.h3 Z hZ) (P.h4 Z hZ)
    (P.order Z hZ) (restr Z y) (P.lattice_persist Z hZ y hy hvan)
    (le_trans (l1E_restr_le y) hk)
  exact ⟨extC Z c0, isCert_extC c0 y hc0 hvan, by rw [l1T_extC]; exact hc0K,
    verts_extC_disjoint c0⟩

/-- **Consumidor del núcleo preparado** (familia indexada por `j < J`). Para todo `q ≥ 1`
con `6KJ ≤ q·βn`: certificados con signo `c_j`, borde exacto `y_j`, `‖c_j‖₁ ≤ K`,
`∑ ‖c_j‖₁ ≤ KJ`, usos auxiliares `≤ q` y congestión `∑_j ∑_{T∋v} |c_j T| ≤ K(F(v)+q)`. -/
theorem prepared_core_dispersal {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α : ℝ} {h N₀ k K : ℕ} {β : ℝ} (hU : UniformCertOn.{u} F α h N₀ k K)
    (P : PreparedCore G lab F α h N₀ β) (y : ℕ → Sym2 V → ℤ) (J : ℕ)
    (hy : ∀ j < J, y j ∈ lattice G lab F) (hk : ∀ j < J, l1E (y j) ≤ k)
    (q : ℕ) (hq : 1 ≤ q) (hqB : (6 * K * J : ℝ) ≤ q * (β * Fintype.card V)) :
    ∃ c : ℕ → Finset V → ℤ,
      (∀ j < J, IsCert G lab F (c j) (y j) ∧ l1T (c j) ≤ K) ∧
      ∑ j ∈ range J, l1T (c j) ≤ K * J ∧
      (∀ v, aux c y J v ≤ q) ∧
      ∀ v, ∑ j ∈ range J, vload (c j) v ≤ K * (frontCount y J v + q) := by
  have hB : (3 * K * J : ℝ) ≤ q * (β * Fintype.card V) := by
    have : (0 : ℝ) ≤ 3 * K * J := by positivity
    linarith
  obtain ⟨c, hc, haux⟩ := greedy_dispersal G lab F y J K q (β * Fintype.card V) hq hB
    (fun t ht Z hZ hZd => cert_avoiding hU P (hy t ht) (hk t ht) Z hZ hZd)
  refine ⟨c, hc, sum_l1T_le c J K (fun j hj => (hc j hj).2), haux, fun v => ?_⟩
  refine le_trans (sum_vload_le c y J K (fun j hj => (hc j hj).2) v) ?_
  have := haux v
  have : (aux c y J v : ℤ) ≤ q := by exact_mod_cast this
  have hK : (0 : ℤ) ≤ K := Nat.cast_nonneg _
  nlinarith

/-- La elección explícita `q = max 1 ⌈6KJ/(βn)⌉`. -/
def qStar (K J : ℕ) (β : ℝ) (n : ℕ) : ℕ := max 1 ⌈(6 * K * J : ℝ) / (β * n)⌉₊

lemma one_le_qStar (K J : ℕ) (β : ℝ) (n : ℕ) : 1 ≤ qStar K J β n := le_max_left _ _

lemma qStar_spec (K J : ℕ) {β : ℝ} {n : ℕ} (hβ : 0 < β) (hn : 0 < n) :
    (6 * K * J : ℝ) ≤ qStar K J β n * (β * n) := by
  have hpos : (0 : ℝ) < β * n := mul_pos hβ (by exact_mod_cast hn)
  have h1 : (6 * K * J : ℝ) / (β * n) ≤ qStar K J β n := by
    refine le_trans (Nat.le_ceil _) ?_
    have : ⌈(6 * K * J : ℝ) / (β * n)⌉₊ ≤ qStar K J β n := le_max_right _ _
    exact_mod_cast this
  rwa [div_le_iff₀ hpos] at h1

/-- **Consumidor final, familia indexada finita arbitraria `ι`**, con `J = |ι|`,
`q = qStar K J β n`, `F(v) = #{i : v ∈ front (y i)}`. Incluye `J = 0` y `k = 0`. -/
theorem prepared_core_dispersal_fintype {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {α : ℝ} {h N₀ k K : ℕ} {β : ℝ}
    (hU : UniformCertOn.{u} F α h N₀ k K) (P : PreparedCore G lab F α h N₀ β)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    {ι : Type*} [Fintype ι] (y : ι → Sym2 V → ℤ)
    (hy : ∀ i, y i ∈ lattice G lab F) (hk : ∀ i, l1E (y i) ≤ k) :
    ∃ c : ι → Finset V → ℤ,
      (∀ i, IsCert G lab F (c i) (y i) ∧ l1T (c i) ≤ K) ∧
      ∑ i, l1T (c i) ≤ K * Fintype.card ι ∧
      (∀ v, (univ.filter (fun i => v ∈ verts (c i) ∧ v ∉ front (y i))).card ≤
        qStar K (Fintype.card ι) β (Fintype.card V)) ∧
      ∀ v, ∑ i, vload (c i) v ≤
        K * ((univ.filter (fun i => v ∈ front (y i))).card +
          qStar K (Fintype.card ι) β (Fintype.card V)) := by
  set J := Fintype.card ι
  let e : ι ≃ Fin J := Fintype.equivFin ι
  let y' : ℕ → Sym2 V → ℤ := fun n => if hn : n < J then y (e.symm ⟨n, hn⟩) else 0
  have hy'i : ∀ i, y' (e i) = y i := by
    intro i
    simp [y', (e i).2]
  obtain ⟨c, hc, hsum, haux, hload⟩ := prepared_core_dispersal hU P y' J
    (fun j hj => by simp only [y', dif_pos hj]; exact hy _)
    (fun j hj => by simp only [y', dif_pos hj]; exact hk _)
    _ (one_le_qStar _ _ _ _) (qStar_spec K J hβ hn)
  -- transport sums over `range J` to sums over `ι`
  have htr : ∀ f : ℕ → ℤ, ∑ j ∈ range J, f j = ∑ i, f (e i) := by
    intro f
    rw [Finset.sum_range]
    exact (Equiv.sum_comp e (fun x : Fin J => f x)).symm
  have hcard : ∀ (p : ℕ → Prop) [DecidablePred p], ((range J).filter p).card = (univ.filter (fun i => p (e i))).card := by
    intro p _
    have := htr (fun j => if p j then 1 else 0)
    simp only [← Finset.sum_filter] at this
    simpa using this
  refine ⟨fun i => c (e i), fun i => ?_, ?_, fun v => ?_, fun v => ?_⟩
  · have := hc (e i) (e i).2
    rwa [hy'i] at this
  · rw [← htr (fun j => l1T (c j))]; exact hsum
  · have := haux v
    unfold aux at this
    rw [hcard] at this
    simpa only [hy'i] using this
  · have := hload v
    rw [htr (fun j => vload (c j) v)] at this
    unfold frontCount at this
    rw [hcard] at this
    simpa only [hy'i] using this

end TypedTriangle.Dispersal
