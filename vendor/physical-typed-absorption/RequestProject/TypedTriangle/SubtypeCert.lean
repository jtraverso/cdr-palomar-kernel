/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SparseEdgeDefs

@[expose] public section

/-!
# Certificados en el host con vértices borrados y su extensión por cero (V15)

Definiciones transparentes (nuevo espacio de nombres `TypedTriangle.Dispersal`) sobre las
definiciones desplegadas `(G, lab, F)` de `SparseEdgeDefs.lean`:

* `triBd c` — borde de una función de coeficientes enteros (con signo) sobre triángulos;
* `IsCert G lab F c y` — `c` sólo es no nulo en triángulos permitidos y `triBd c = y`;
* `l1E`, `l1T` — normas `ℓ¹` de vectores de aristas y de coeficientes de triángulos;
* `Surv Z = {v // v ∉ Z}`, `subG G Z`, `subLab lab Z` — el host en el subtipo superviviente
  (un host genuino sobre el subtipo, NO el grafo ambiente con vértices aislados);
* `restr Z y` — restricción de un vector de aristas al subtipo;
* `extC Z c` — extensión por cero de coeficientes del subtipo al host ambiente.

Resultados: borde exacto (`triBd_extC`), permisibilidad (`extC_allowed`), conservación de la
norma (`l1T_extC`), evitación (`verts_extC_disjoint`), conservación de la carga por vértice,
`l1E (restr Z y) ≤ l1E y`, y `card_verts_le` (`#verts c ≤ 3‖c‖₁`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Dispersal

open TypedTriangle.SparseEdge

universe u v

variable {V : Type u} {I : Type v}

/-! ### Definiciones -/

section defs
variable [Fintype V]

/-- Borde de una función de coeficientes sobre conjuntos de vértices. -/
def triBd (c : Finset V → ℤ) : Sym2 V → ℤ := fun e => ∑ T, c T * ind (triEdges T) e

/-- `c` es un certificado (con signo) de `y`: soporte en triángulos permitidos y borde `y`. -/
def IsCert (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (c : Finset V → ℤ)
    (y : Sym2 V → ℤ) : Prop :=
  (∀ T, c T ≠ 0 → IsAllowed G lab F T) ∧ triBd c = y

/-- Norma `ℓ¹` de un vector de aristas. -/
def l1E (y : Sym2 V → ℤ) : ℤ := ∑ e, |y e|

/-- Norma `ℓ¹` de una función de coeficientes. -/
def l1T (c : Finset V → ℤ) : ℤ := ∑ T, |c T|

/-- Congestión absoluta en `v`: `∑_{T ∋ v} |c T|`. -/
def vload (c : Finset V → ℤ) (v : V) : ℤ := ∑ T ∈ univ.filter (fun T => v ∈ T), |c T|

/-- Frontera de una demanda: vértices tocados por una arista del soporte no nulo. -/
def front (y : Sym2 V → ℤ) : Finset V := univ.filter (fun v => ∃ e, y e ≠ 0 ∧ v ∈ e)

/-- Vértices usados por un certificado (vértices de triángulos con coeficiente no nulo). -/
def verts (c : Finset V → ℤ) : Finset V := univ.filter (fun v => ∃ T, c T ≠ 0 ∧ v ∈ T)

end defs

/-- Vértices supervivientes al borrar `Z`. -/
abbrev Surv (Z : Finset V) := {v : V // v ∉ Z}

/-- Grafo del host borrado: adyacencia heredada en el subtipo. -/
def subG (G : SimpleGraph V) (Z : Finset V) : SimpleGraph (Surv Z) := G.comap Subtype.val

/-- Etiquetas del host borrado. -/
def subLab (lab : V → I) (Z : Finset V) : Surv Z → I := fun x => lab x.1

/-- Restricción de un vector de aristas al subtipo. -/
def restr (Z : Finset V) (y : Sym2 V → ℤ) : Sym2 (Surv Z) → ℤ := fun e => y (e.map Subtype.val)

/-- Extensión por cero de coeficientes del subtipo al host ambiente. -/
def extC (Z : Finset V) (c : Finset (Surv Z) → ℤ) : Finset V → ℤ :=
  fun T => if Disjoint T Z then c (T.subtype (fun x => x ∉ Z)) else 0

/-! ### Lemas de la extensión -/

section lemmas

variable {Z : Finset V}

/-- La inclusión del subtipo. -/
abbrev emb (Z : Finset V) : Surv Z ↪ V := Function.Embedding.subtype _

lemma map_emb_disjoint (S : Finset (Surv Z)) : Disjoint (S.map (emb Z)) Z := by
  rw [Finset.disjoint_left]
  intro a ha
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 ha
  exact x.2

lemma subtype_map_emb (S : Finset (Surv Z)) :
    (S.map (emb Z)).subtype (fun x => x ∉ Z) = S := by
  ext x
  simp [Finset.mem_subtype, x.2]

lemma map_subtype_of_disjoint {T : Finset V} (h : Disjoint T Z) :
    (T.subtype (fun x => x ∉ Z)).map (emb Z) = T :=
  Finset.subtype_map_of_mem (fun _ hx => Finset.disjoint_left.1 h hx)

lemma extC_map (c : Finset (Surv Z) → ℤ) (S : Finset (Surv Z)) :
    extC Z c (S.map (emb Z)) = c S := by
  simp [extC, map_emb_disjoint, subtype_map_emb]

lemma extC_of_not_disjoint (c : Finset (Surv Z) → ℤ) {T : Finset V} (h : ¬ Disjoint T Z) :
    extC Z c T = 0 := by
  simp [extC, h]

lemma disjoint_of_extC_ne (c : Finset (Surv Z) → ℤ) {T : Finset V} (h : extC Z c T ≠ 0) :
    Disjoint T Z := by
  by_contra h'
  exact h (extC_of_not_disjoint c h')

/-- Transferencia de sumas: para `φ T 0 = 0`, `∑_T φ T (extC c T) = ∑_S φ (S ↦ V) (c S)`. -/
lemma sum_extC {M : Type*} [AddCommMonoid M] [Fintype V] (c : Finset (Surv Z) → ℤ)
    (φ : Finset V → ℤ → M) (hφ : ∀ T, φ T 0 = 0) :
    ∑ T, φ T (extC Z c T) = ∑ S, φ (S.map (emb Z)) (c S) := by
  have h1 : ∑ S, φ (S.map (emb Z)) (c S) =
      ∑ T ∈ univ.map (Finset.mapEmbedding (emb Z)).toEmbedding, φ T (extC Z c T) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    show _ = φ (S.map (emb Z)) (extC Z c (S.map (emb Z)))
    rw [extC_map]
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro T _ hT
  have : ¬ Disjoint T Z := by
    intro hd
    apply hT
    refine Finset.mem_map.2 ⟨T.subtype (fun x => x ∉ Z), Finset.mem_univ _, ?_⟩
    exact map_subtype_of_disjoint hd
  rw [extC_of_not_disjoint c this, hφ]

lemma mem_triEdges_map_iff (S : Finset (Surv Z)) (e : Sym2 (Surv Z)) :
    e.map Subtype.val ∈ triEdges (S.map (emb Z)) ↔ e ∈ triEdges S := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, mem_triEdges, mem_triEdges]
    simp [Subtype.ext_iff, a.2, b.2]

lemma ind_triEdges_map (S : Finset (Surv Z)) (e : Sym2 (Surv Z)) :
    ind (triEdges (S.map (emb Z))) (e.map Subtype.val) = ind (triEdges S) e := by
  by_cases h : e ∈ triEdges S <;> simp [ind, h, mem_triEdges_map_iff]

lemma ind_triEdges_map_of_touch (S : Finset (Surv Z)) {e : Sym2 V} (he : ∃ z ∈ Z, z ∈ e) :
    ind (triEdges (S.map (emb Z))) e = 0 := by
  obtain ⟨z, hz, hze⟩ := he
  rw [ind_apply, if_neg]
  intro hm
  have := mem_of_mem_triEdges hm hze
  exact Finset.disjoint_left.1 (map_emb_disjoint S) this hz

/-- Toda arista o toca `Z` o es imagen de una arista del subtipo. -/
lemma touch_or_map (e : Sym2 V) :
    (∃ z ∈ Z, z ∈ e) ∨ ∃ e' : Sym2 (Surv Z), e'.map Subtype.val = e := by
  induction e using Sym2.ind with
  | _ a b =>
    by_cases ha : a ∈ Z
    · exact Or.inl ⟨a, ha, Sym2.mem_mk_left a b⟩
    by_cases hb : b ∈ Z
    · exact Or.inl ⟨b, hb, Sym2.mem_mk_right a b⟩
    exact Or.inr ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simp⟩

variable [Fintype V]

lemma triBd_extC_eq (c : Finset (Surv Z) → ℤ) (e : Sym2 V) :
    triBd (extC Z c) e = ∑ S, c S * ind (triEdges (S.map (emb Z))) e := by
  unfold triBd
  exact sum_extC c (fun T x => x * ind (triEdges T) e) (fun T => by simp)

/-- **Borde exacto de la extensión por cero.** -/
theorem triBd_extC (c : Finset (Surv Z) → ℤ) (y : Sym2 V → ℤ)
    (hc : triBd c = restr Z y) (hy : ∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) :
    triBd (extC Z c) = y := by
  funext e
  rw [triBd_extC_eq]
  rcases touch_or_map (Z := Z) e with ht | ⟨e', rfl⟩
  · rw [hy e ht]
    exact Finset.sum_eq_zero (fun S _ => by rw [ind_triEdges_map_of_touch S ht, mul_zero])
  · have := congrFun hc e'
    simp only [triBd, restr] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [ind_triEdges_map]

omit [Fintype V] in
lemma isAllowed_map {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {S : Finset (Surv Z)} (hS : IsAllowed (subG G Z) (subLab lab Z) F S) :
    IsAllowed G lab F (S.map (emb Z)) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨by rw [Finset.card_map]; exact h1, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    have : x' ≠ y' := fun h => hxy (by rw [h])
    exact h2 x' hx' y' hy' this
  · rw [Finset.map_val, Multiset.map_map]
    exact h3

omit [Fintype V] in
/-- **Permisibilidad de la extensión.** -/
theorem extC_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (c : Finset (Surv Z) → ℤ)
    (hc : ∀ S, c S ≠ 0 → IsAllowed (subG G Z) (subLab lab Z) F S) :
    ∀ T, extC Z c T ≠ 0 → IsAllowed G lab F T := by
  intro T hT
  have hd := disjoint_of_extC_ne c hT
  have hT' : c (T.subtype (fun x => x ∉ Z)) ≠ 0 := by simpa [extC, hd] using hT
  have := isAllowed_map (hc _ hT')
  rwa [map_subtype_of_disjoint hd] at this

/-- **Certificado ambiente a partir de un certificado del host borrado.** -/
theorem isCert_extC {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (c : Finset (Surv Z) → ℤ) (y : Sym2 V → ℤ)
    (hc : IsCert (subG G Z) (subLab lab Z) F c (restr Z y))
    (hy : ∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) :
    IsCert G lab F (extC Z c) y :=
  ⟨extC_allowed c hc.1, triBd_extC c y hc.2 hy⟩

/-- **Conservación de la norma.** -/
theorem l1T_extC (c : Finset (Surv Z) → ℤ) : l1T (extC Z c) = l1T c := by
  unfold l1T
  exact sum_extC c (fun _ x => |x|) (fun _ => abs_zero)

/-- **Evitación**: la extensión no usa vértices de `Z`. -/
theorem verts_extC_disjoint (c : Finset (Surv Z) → ℤ) : Disjoint (verts (extC Z c)) Z := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨T, hT, hvT⟩ := (Finset.mem_filter.1 hv).2
  exact Finset.disjoint_left.1 (disjoint_of_extC_ne c hT) hvT hvZ

/-- Carga por vértice de la extensión: nula en `Z`, y la del subtipo fuera de `Z`. -/
theorem vload_extC (c : Finset (Surv Z) → ℤ) (x : Surv Z) :
    vload (extC Z c) x.1 = vload c x := by
  unfold vload
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_extC c (fun T a => if x.1 ∈ T then |a| else 0) (fun _ => by simp)]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp [x.2]

/-- La restricción no aumenta la norma `ℓ¹`. -/
theorem l1E_restr_le (y : Sym2 V → ℤ) : l1E (restr Z y) ≤ l1E y := by
  unfold l1E restr
  let f : Sym2 (Surv Z) ↪ Sym2 V := ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  have : ∑ e : Sym2 (Surv Z), |y (e.map Subtype.val)| = ∑ e ∈ univ.map f, |y e| := by
    rw [Finset.sum_map]; rfl
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => abs_nonneg _)

end lemmas

/-! ### Cotas generales de un certificado -/

section general
variable [Fintype V]

lemma vload_le_l1T (c : Finset V → ℤ) (v : V) : vload c v ≤ l1T c :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)

lemma vload_eq_zero_of_not_mem (c : Finset V → ℤ) {v : V} (hv : v ∉ verts c) : vload c v = 0 := by
  unfold vload
  refine Finset.sum_eq_zero (fun T hT => ?_)
  have hvT := (Finset.mem_filter.1 hT).2
  by_contra h
  exact hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, T, abs_ne_zero.1 h, hvT⟩)

lemma vload_nonneg (c : Finset V → ℤ) (v : V) : 0 ≤ vload c v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma l1T_nonneg (c : Finset V → ℤ) : 0 ≤ l1T c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- **Cada certificado usa a lo sumo `3‖c‖₁` vértices** (cuenta de ocurrencias). -/
theorem card_verts_le {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (c : Finset V → ℤ) (hc : ∀ T, c T ≠ 0 → IsAllowed G lab F T) :
    ((verts c).card : ℤ) ≤ 3 * l1T c := by
  have hsub : verts c ⊆ (univ.filter (fun T => c T ≠ 0)).biUnion id := by
    intro v hv
    obtain ⟨T, hT, hvT⟩ := (Finset.mem_filter.1 hv).2
    exact Finset.mem_biUnion.2 ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩, hvT⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ T ∈ univ.filter (fun T => c T ≠ 0), (id T).card
      = ∑ T ∈ univ.filter (fun T => c T ≠ 0), 3 := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    exact (hc T (Finset.mem_filter.1 hT).2).1
  rw [h2, Finset.sum_const, smul_eq_mul] at h1
  have h3 : ((univ.filter (fun T => c T ≠ 0)).card : ℤ) ≤ l1T c := by
    unfold l1T
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_filter_add_sum_filter_not univ
      (fun T => c T ≠ 0) (fun T => |c T|)]
    have : ∑ T ∈ univ.filter (fun T => c T ≠ 0), ((1 : ℕ) : ℤ)
        ≤ ∑ T ∈ univ.filter (fun T => c T ≠ 0), |c T| := by
      refine Finset.sum_le_sum (fun T hT => ?_)
      have := (Finset.mem_filter.1 hT).2
      have : 0 < |c T| := abs_pos.2 this
      push_cast; omega
    have h0 : 0 ≤ ∑ T ∈ univ.filter (fun T => ¬ c T ≠ 0), |c T| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have : ((verts c).card : ℤ) ≤ ((univ.filter (fun T => c T ≠ 0)).card * 3 : ℕ) := by
    exact_mod_cast h1
  push_cast at this
  linarith

end general

end TypedTriangle.Dispersal
