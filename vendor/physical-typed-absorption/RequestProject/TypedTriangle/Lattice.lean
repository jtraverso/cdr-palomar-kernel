/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Basic

@[expose] public section

/-!
# Álgebra del retículo físico, grafos basales y grupo local `M_G`

Contenido (todo demostrado):

* álgebra de indicadores y de pertenencia a `Λ_G` (uniones disjuntas, diferencias);
* *grafos basales*: unión de descomposiciones disjuntas (núcleo de P20) y retirada de
  una subdescomposición especificada (paso (L32) de P15);
* restar de un grafo físico un grafo basal deja un grafo físico (paso (L36) de P16);
* monotonía del retículo respecto del host y del soporte: `Λ_J ⊆ Λ_G` (extensión por cero),
  pero no a la inversa (eso es (L10)/(L11), que no se afirman aquí);
* el grupo local `M_G` (§2 del ledger) y la inclusión (L1) `Λ_G ⊆ M_G`, junto con las
  restricciones lineales que satisfacen sus estrellas (paridad y balances de cargas).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-! ## Indicadores -/

omit [Fintype V] in
lemma ind_union_of_disjoint {J K : Finset (Sym2 V)} (h : Disjoint J K) :
    ind (J ∪ K) = ind J + ind K := by
  funext e
  simp only [ind, Pi.add_apply, Finset.mem_union]
  by_cases hJ : e ∈ J
  · have hK : e ∉ K := Finset.disjoint_left.mp h hJ
    simp [hJ, hK]
  · by_cases hK : e ∈ K <;> simp [hJ, hK]

omit [Fintype V] in
lemma ind_sdiff_of_subset {J K : Finset (Sym2 V)} (h : K ⊆ J) :
    ind (J \ K) = ind J - ind K := by
  have := ind_union_of_disjoint (Finset.sdiff_disjoint : Disjoint (J \ K) K)
  rw [Finset.sdiff_union_of_subset h] at this
  rw [this]; abel

omit [Fintype V] in
lemma ind_empty : ind (∅ : Finset (Sym2 V)) = 0 := by
  funext e; simp [ind]

/-! ## Física -/

omit [Fintype V] in
lemma isPhysical_empty (H : Host V I) (F : Set (Multiset I)) : IsPhysical H F ∅ := by
  unfold IsPhysical; rw [ind_empty]; exact Submodule.zero_mem _

omit [Fintype V] in
lemma isPhysical_triEdges {H : Host V I} {F : Set (Multiset I)} {T : Finset V}
    (hT : IsAllowed H F T) : IsPhysical H F (triEdges T) :=
  Submodule.subset_span ⟨T, hT, rfl⟩

omit [Fintype V] in
lemma isPhysical_union {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    (hJ : IsPhysical H F J) (hK : IsPhysical H F K) (hd : Disjoint J K) :
    IsPhysical H F (J ∪ K) := by
  unfold IsPhysical at *; rw [ind_union_of_disjoint hd]; exact Submodule.add_mem _ hJ hK

omit [Fintype V] in
lemma isPhysical_sdiff {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    (hJ : IsPhysical H F J) (hK : IsPhysical H F K) (hKJ : K ⊆ J) :
    IsPhysical H F (J \ K) := by
  unfold IsPhysical at *; rw [ind_sdiff_of_subset hKJ]; exact Submodule.sub_mem _ hJ hK

omit [Fintype V] in
/-- Si `J` es físico y `K ⊆ J` es basal (tiene una descomposición permitida), entonces
`J \ K` es físico. Es el paso usado en (L36): restar packings y grafos basales de un grafo
físico conserva la física. -/
theorem isPhysical_sdiff_of_decomposition {H : Host V I} {F : Set (Multiset I)}
    {J K : Finset (Sym2 V)} {D : Finset (Finset V)} (hJ : IsPhysical H F J)
    (hD : IsDecomposition H F K D) (hKJ : K ⊆ J) : IsPhysical H F (J \ K) :=
  isPhysical_sdiff hJ (isPhysical_of_isDecomposition hD) hKJ

/-! ## Grafos basales -/

omit [Fintype V] in
/-- **Unión de grafos basales disjuntos** (núcleo del ensamblaje P20): descomposiciones de
conjuntos de aristas disjuntos se unen en una descomposición de la unión. -/
theorem IsDecomposition.union {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    {D D' : Finset (Finset V)} (hD : IsDecomposition H F J D) (hD' : IsDecomposition H F K D')
    (hd : Disjoint J K) : IsDecomposition H F (J ∪ K) (D ∪ D') := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases Finset.mem_union.mp hT with h | h
    · exact hD.1 T h
    · exact hD'.1 T h
  · intro T hT T' hT' hne
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hT hT'
    rcases hT with h1 | h1 <;> rcases hT' with h2 | h2
    · exact hD.2.1 h1 h2 hne
    · exact Finset.disjoint_of_subset_left (hD.subset h1)
        (Finset.disjoint_of_subset_right (hD'.subset h2) hd)
    · exact Finset.disjoint_of_subset_left (hD'.subset h1)
        (Finset.disjoint_of_subset_right (hD.subset h2) hd.symm)
    · exact hD'.2.1 h1 h2 hne
  · rw [Finset.union_biUnion, hD.2.2, hD'.2.2]

omit [Fintype V] in
/-- **Retirar una subdescomposición especificada** (paso (L32)): si `D` descompone `J` y
`D' ⊆ D`, entonces `D \ D'` descompone `J` menos las aristas cubiertas por `D'`. Esto NO
dice que restar un packing arbitrario de un grafo basal deje un grafo basal. -/
theorem IsDecomposition.sdiff_sub {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    {D D' : Finset (Finset V)} (hD : IsDecomposition H F J D) (hsub : D' ⊆ D) :
    IsDecomposition H F (J \ D'.biUnion triEdges) (D \ D') := by
  refine ⟨fun T hT => hD.1 T (Finset.mem_sdiff.mp hT).1, ?_, ?_⟩
  · exact hD.2.1.subset (by intro T hT; exact (Finset.mem_sdiff.mp hT).1)
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    constructor
    · rintro ⟨T, ⟨hTD, hTD'⟩, heT⟩
      refine ⟨hD.subset hTD heT, ?_⟩
      rintro ⟨T', hT', heT'⟩
      have := hD.unique hTD (hsub hT') heT heT'
      exact hTD' (this ▸ hT')
    · rintro ⟨heJ, hne⟩
      obtain ⟨T, hT, heT⟩ := hD.exists_mem heJ
      refine ⟨T, ⟨hT, fun hT' => hne ⟨T, hT', heT⟩⟩, heT⟩

omit [Fintype V] in
/-- Unión de una familia finita de grafos basales disjuntos dos a dos. -/
theorem isDecomposition_biUnion {H : Host V I} {F : Set (Multiset I)} {ι : Type*}
    (s : Finset ι) (J : ι → Finset (Sym2 V)) (D : ι → Finset (Finset V))
    (hD : ∀ i ∈ s, IsDecomposition H F (J i) (D i))
    (hdisj : (s : Set ι).PairwiseDisjoint J) :
    IsDecomposition H F (s.biUnion J) (s.biUnion D) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.biUnion_insert]
    refine (hD a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => hD i (Finset.mem_insert_of_mem hi))
        (hdisj.subset (by simp))) ?_
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hdisj (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

/-! ## Monotonía del retículo y subhosts -/

/-- El subhost con aristas `J` (intersecadas con las de `H`) y las mismas etiquetas. -/
def subHost (H : Host V I) (J : Finset (Sym2 V)) : Host V I :=
  ⟨SimpleGraph.fromEdgeSet (J : Set (Sym2 V)) ⊓ H.G, H.lab⟩

omit [Fintype V] in
lemma isAllowed_mono {H H' : Host V I} {F : Set (Multiset I)} (hG : H.G ≤ H'.G)
    (hl : H.lab = H'.lab) {T : Finset V} (hT : IsAllowed H F T) : IsAllowed H' F T :=
  ⟨hT.1, fun x hx y hy hxy => hG (hT.2.1 x hx y hy hxy), hl ▸ hT.2.2⟩

omit [Fintype V] in
/-- Monotonía: `Λ_H ⊆ Λ_{H'}` si `H ≤ H'` con las mismas etiquetas. -/
theorem lattice_mono {H H' : Host V I} {F : Set (Multiset I)} (hG : H.G ≤ H'.G)
    (hl : H.lab = H'.lab) : lattice H F ≤ lattice H' F := by
  unfold lattice
  apply Submodule.span_mono
  rintro _ ⟨T, hT, rfl⟩
  exact ⟨T, isAllowed_mono hG hl hT, rfl⟩

omit [Fintype V] in
lemma subHost_le (H : Host V I) (J : Finset (Sym2 V)) : (subHost H J).G ≤ H.G :=
  inf_le_right

omit [Fintype V] in
/-- Física en el soporte implica física en el ambiente (extensión por cero). -/
theorem isPhysical_of_subHost {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    (h : IsPhysical (subHost H J) F K) : IsPhysical H F K :=
  lattice_mono (subHost_le H J) rfl h

omit [Fintype V] in
lemma triEdges_subset_of_isAllowed_subHost {H : Host V I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {T : Finset V} (hT : IsAllowed (subHost H J) F T) :
    triEdges T ⊆ J := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_triEdges] at he
    have := hT.2.1 x he.1 y he.2.1 he.2.2
    simp only [subHost, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj] at this
    exact this.1.1

omit [Fintype V] in
/-- Una descomposición de `J` en `H` es una descomposición de `J` en el subhost con aristas
`J`, y recíprocamente: ser basal es intrínseco al soporte. -/
theorem isDecomposition_subHost_iff {H : Host V I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {D : Finset (Finset V)} :
    IsDecomposition (subHost H J) F J D ↔ IsDecomposition H F J D := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun T hT => isAllowed_mono (subHost_le H J) rfl (h1 T hT), h2, h3⟩
  · intro hD
    refine ⟨fun T hT => ?_, hD.2.1, hD.2.2⟩
    have hTA := hD.1 T hT
    refine ⟨hTA.1, fun x hx y hy hxy => ?_, hTA.2.2⟩
    simp only [subHost, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨hD.subset hT ((mem_triEdges).2 ⟨hx, hy, hxy⟩), hxy⟩, hTA.2.1 x hx y hy hxy⟩

/-! ## Grupo local `M_G` y la inclusión (L1) -/

/-- Triángulos permitidos que contienen el vértice `v` (aristas del enlace `L_v(G)`). -/
def triAt (H : Host V I) (F : Set (Multiset I)) (v : V) : Finset (Finset V) :=
  (allowed H F).filter (v ∈ ·)

/-- Grupo local `M_G`: vectores enteros soportados en las aristas de `G` cuya estrella en
cada raíz `v` está en la imagen entera de la incidencia no orientada del enlace `L_v(G)`:
existe `c` sobre las aristas del enlace (= triángulos permitidos por `v`) tal que
`x(vw) = ∑_{T ∋ v, w} c T` para todo `w ≠ v`. -/
def localGroup (H : Host V I) (F : Set (Multiset I)) : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | (∀ e, e ∉ edges H → x e = 0) ∧
    ∀ v, ∃ c : Finset V → ℤ, ∀ w, w ≠ v →
      x s(v, w) = ∑ T ∈ (triAt H F v).filter (w ∈ ·), c T}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨fun e he => by simp [hx0 e he, hy0 e he], fun v => ?_⟩
    obtain ⟨c, hc⟩ := hx v
    obtain ⟨d, hd⟩ := hy v
    exact ⟨c + d, fun w hw => by simp [hc w hw, hd w hw, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun v => ⟨0, fun w _ => by simp⟩⟩
  smul_mem' := by
    rintro k x ⟨hx0, hx⟩
    refine ⟨fun e he => by simp [hx0 e he], fun v => ?_⟩
    obtain ⟨c, hc⟩ := hx v
    exact ⟨k • c, fun w hw => by simp [hc w hw, Finset.mul_sum]⟩

omit [Fintype V] in
lemma triEdges_subset_edges {H : Host V I} {F : Set (Multiset I)} [Fintype V] {T : Finset V}
    (hT : IsAllowed H F T) : triEdges T ⊆ edges H := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_triEdges] at he
    simp [edges, hT.2.1 x he.1 y he.2.1 he.2.2]

/-- **(L1)** `Λ_G ⊆ M_G`. -/
theorem lattice_le_localGroup (H : Host V I) (F : Set (Multiset I)) :
    lattice H F ≤ localGroup H F := by
  unfold lattice
  rw [Submodule.span_le]
  rintro _ ⟨T, hT, rfl⟩
  refine ⟨fun e he => ?_, fun v => ⟨fun T' => if T' = T then 1 else 0, fun w hw => ?_⟩⟩
  · simp only [ind]
    rw [if_neg]
    exact fun h => he (triEdges_subset_edges hT h)
  · rw [Finset.sum_ite_eq']
    simp only [ind, mem_triEdges, triAt, allowed, Finset.mem_filter, Finset.mem_univ, true_and]
    have hT' : IsAllowed H F T := hT
    by_cases hv : v ∈ T <;> by_cases hw' : w ∈ T <;> simp [hv, hw', hT', Ne.symm hw]

/-- Estrella de `x` en `v`, evaluada mediante una carga `χ` sobre los vecinos. -/
def starCharge (x : Sym2 V → ℤ) (v : V) (χ : V → ℤ) : ℤ :=
  ∑ w ∈ univ.erase v, χ w * x s(v, w)

/-- **Restricciones de las estrellas de `M_G`.** Si una carga `χ` sobre los vértices anula
cada arista del enlace de `v` (es decir `∑_{w ∈ T∖{v}} χ w = 0` para cada triángulo
permitido `T ∋ v`), entonces anula la estrella en `v` de todo `x ∈ M_G`. Con `χ = ±1` en
los lados de una componente bipartita se obtiene el balance entre lados. -/
theorem starCharge_eq_zero {H : Host V I} {F : Set (Multiset I)} {x : Sym2 V → ℤ}
    (hx : x ∈ localGroup H F) (v : V) (χ : V → ℤ)
    (hχ : ∀ T ∈ triAt H F v, ∑ w ∈ T.erase v, χ w = 0) : starCharge x v χ = 0 := by
  obtain ⟨c, hc⟩ := hx.2 v
  unfold starCharge
  calc ∑ w ∈ univ.erase v, χ w * x s(v, w)
      = ∑ w ∈ univ.erase v, ∑ T ∈ triAt H F v, (if w ∈ T then χ w * c T else 0) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [hc w (Finset.ne_of_mem_erase hw), Finset.mul_sum, Finset.sum_filter]
    _ = ∑ T ∈ triAt H F v, ∑ w ∈ univ.erase v, (if w ∈ T then χ w * c T else 0) :=
        Finset.sum_comm
    _ = ∑ T ∈ triAt H F v, c T * ∑ w ∈ T.erase v, χ w := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter, Finset.mul_sum]
        have : (univ.erase v).filter (· ∈ T) = T.erase v := by
          ext w; simp [and_comm]
        rw [this]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ = 0 := Finset.sum_eq_zero fun T hT => by rw [hχ T hT, mul_zero]

/-- **Paridad de las estrellas.** Para `x ∈ M_G`, la suma de `x` en la estrella de cada
vértice es par (cada arista del enlace tiene dos extremos). -/
theorem star_sum_even {H : Host V I} {F : Set (Multiset I)} {x : Sym2 V → ℤ}
    (hx : x ∈ localGroup H F) (v : V) : Even (∑ w ∈ univ.erase v, x s(v, w)) := by
  obtain ⟨c, hc⟩ := hx.2 v
  have hcard : ∀ T ∈ triAt H F v, (T.erase v).card = 2 := by
    intro T hT
    simp only [triAt, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    rw [Finset.card_erase_of_mem hT.2, hT.1.1]
  have : ∑ w ∈ univ.erase v, x s(v, w) = ∑ T ∈ triAt H F v, 2 * c T := by
    calc ∑ w ∈ univ.erase v, x s(v, w)
        = ∑ w ∈ univ.erase v, ∑ T ∈ triAt H F v, (if w ∈ T then c T else 0) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hc w (Finset.ne_of_mem_erase hw), Finset.sum_filter]
      _ = ∑ T ∈ triAt H F v, ∑ w ∈ univ.erase v, (if w ∈ T then c T else 0) :=
          Finset.sum_comm
      _ = ∑ T ∈ triAt H F v, 2 * c T := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [← Finset.sum_filter]
          have : (univ.erase v).filter (· ∈ T) = T.erase v := by
            ext w; simp [and_comm]
          rw [this, Finset.sum_const, hcard T hT]; simp
  rw [this, ← Finset.mul_sum]
  exact even_two_mul _

/-- El grupo cociente `Q_G = M_G / Λ_G` de (L1). -/
abbrev physQuot (H : Host V I) (F : Set (Multiset I)) :=
  localGroup H F ⧸ (lattice H F).comap (localGroup H F).subtype

/-- Corolario: todo grafo físico tiene estrellas de suma par en cada vértice, es decir,
grado par en cada vértice (condición de divisibilidad local necesaria). -/
theorem isPhysical_degree_even {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    (hJ : IsPhysical H F J) (v : V) :
    Even ((univ.erase v).filter (fun w => s(v, w) ∈ J)).card := by
  have := star_sum_even (lattice_le_localGroup H F hJ) v
  simpa [ind, Finset.sum_boole] using this

end TypedTriangle
