/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkStar
public import RequestProject.TypedTriangle.CompositeHinge
public import RequestProject.TypedTriangle.Packing

@[expose] public section

/-!
# G1-Z, §4 de la guía V5 — Robustez entera de los enlaces desde las bisagras (S03 §§2–4)

1. Lemas abstractos sobre la imagen entera de la incidencia:
   * `incLattice_eq_of_replace`: si cada columna borrada está en la imagen del grafo menor,
     las imágenes ENTERAS coinciden (no sólo los rangos racionales);
   * `incLattice_vertex_delete`: borrar un vértice `w` conserva la imagen entera de las
     demandas que se anulan en `w`, si `δ_a − δ_b` está en la imagen del grafo menor para
     cada par de vecinos `a, b` de `w`. La prueba no pasa por componentes: el residuo módulo
     la imagen menor es un múltiplo de `δ_w + δ_{a₀}`, y la coordenada en `w` lo anula.
2. Proyección de descomposiciones sobre una estrella (`starProj_decomp`): la proyección de
   `𝟏_K` para una descomposición `D` de `K` es el borde de una cadena del enlace, soportada
   en las bases de los triángulos de `D` por el vértice, con coste `≤ |D|`.
3. Proyección de los dos modos de una bisagra:
   * ápice (`hinge_proj_apex`, §4.1): una bisagra entre `abz` y `abv` da `δ_a + δ_b` como
     borde de una cadena del enlace de `z` con bases en `J`;
   * base (`hinge_proj_base`, §4.2): una bisagra entre `zwa` y `zwb` da `δ_a − δ_b` con bases
     en `J` que evitan `w` (los modos no usan la base `zw`).
4. Robustez (`link_edge_delete`, `link_vertex_delete`, `link_vertices_delete`) y su versión
   desde H3+H4 (`link_image_robust`): para `z ∉ Z` y un grafo malo `B` de grado `≤ d`, con las
   ventanas de `exists_robust_composite_hinge`, toda demanda que se anula en `Z` está en la
   imagen entera del enlace de `z` si y sólo si lo está en la del enlace restringido a aristas
   base que evitan `Z` y `B`.

Los certificados completos pueden modificar aristas de otras estrellas del host; esto NO es
evitación global de vértices para una demanda arbitraria.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

namespace Incidence

variable {V : Type*}

/-! ## 1. Lemas abstractos de la imagen entera -/

lemma incLattice_mono {G G' : SimpleGraph V} (h : G' ≤ G) : incLattice G' ≤ incLattice G := by
  unfold incLattice
  rw [Submodule.span_le]
  rintro _ ⟨⟨e, he⟩, rfl⟩
  exact Submodule.subset_span ⟨⟨e, SimpleGraph.edgeSet_mono h he⟩, rfl⟩

/-- El borde de una cadena soportada en las aristas de `G` está en su imagen entera. -/
lemma bd_mem_incLattice [Fintype V] {G : SimpleGraph V} (s : Sym2 V → ℤ)
    (hs : ∀ e, s e ≠ 0 → e ∈ G.edgeSet) : bd s ∈ incLattice G := by
  unfold bd
  refine Submodule.sum_mem _ fun e _ => ?_
  by_cases h : s e = 0
  · simp [h]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e, hs e h⟩, rfl⟩)

/-- **Sustitución de columnas.** -/
theorem incLattice_eq_of_replace {G G' : SimpleGraph V} (h : G' ≤ G)
    (hrep : ∀ u v, G.Adj u v → dlt u + dlt v ∈ incLattice G') :
    incLattice G = incLattice G' := by
  refine le_antisymm ?_ (incLattice_mono h)
  change Submodule.span ℤ _ ≤ incLattice G'
  rw [Submodule.span_le]
  rintro _ ⟨⟨e, he⟩, rfl⟩
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  change incVec s(u, v) ∈ incLattice G'
  rw [incVec_mk (G.ne_of_adj huv)]
  exact hrep u v huv

/-- Las cargas de la imagen se anulan en un vértice aislado. -/
lemma incLattice_apply_eq_zero {G : SimpleGraph V} {w : V} (hw : ∀ v, ¬ G.Adj w v)
    {x : V → ℤ} (hx : x ∈ incLattice G) : x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hy
    induction e using Sym2.ind with
    | _ a b =>
    have hab : G.Adj a b := he
    change incVec s(a, b) w = 0
    simp only [incVec, Sym2.mem_iff]
    rw [if_neg]
    rintro (rfl | rfl)
    · exact hw _ hab
    · exact hw _ hab.symm
  | zero => rfl
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/-- **Borrado de un vértice.** -/
theorem incLattice_vertex_delete {G G' : SimpleGraph V} {w : V} (h : G' ≤ G)
    (hG' : ∀ u v, G.Adj u v → u ≠ w → v ≠ w → G'.Adj u v) (hw' : ∀ v, ¬ G'.Adj w v)
    (hnb : ∀ a b, G.Adj w a → G.Adj w b → dlt a - dlt b ∈ incLattice G')
    {x : V → ℤ} (hx : x w = 0) : x ∈ incLattice G ↔ x ∈ incLattice G' := by
  refine ⟨fun hxG => ?_, fun hx' => incLattice_mono h hx'⟩
  by_cases hnbr : ∃ a0, G.Adj w a0
  · obtain ⟨a0, ha0⟩ := hnbr
    have key : ∀ y ∈ incLattice G, ∃ k : ℤ, y - k • (dlt w + dlt a0) ∈ incLattice G' := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨e, he⟩, rfl⟩ := hy
        induction e using Sym2.ind with
        | _ a b =>
        have hab : G.Adj a b := he
        change ∃ k : ℤ, incVec s(a, b) - k • (dlt w + dlt a0) ∈ incLattice G'
        rw [incVec_mk (G.ne_of_adj hab)]
        by_cases ha : a = w
        · subst ha
          refine ⟨1, ?_⟩
          have := hnb b a0 hab ha0
          convert this using 1
          rw [one_smul]; abel
        · by_cases hb : b = w
          · subst hb
            refine ⟨1, ?_⟩
            have := hnb a a0 hab.symm ha0
            convert this using 1
            rw [one_smul]; abel
          · exact ⟨0, by simpa using gen_mem (hG' a b hab ha hb)⟩
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨k, hk⟩ := hy
        obtain ⟨l, hl⟩ := hz
        refine ⟨k + l, ?_⟩
        convert Submodule.add_mem _ hk hl using 1
        rw [add_smul]; abel
      | smul c y _ hy =>
        obtain ⟨k, hk⟩ := hy
        refine ⟨c * k, ?_⟩
        convert Submodule.smul_mem _ c hk using 1
        rw [smul_sub, mul_smul]
    obtain ⟨k, hk⟩ := key x hxG
    have h0 := incLattice_apply_eq_zero hw' hk
    have hw0 : a0 ≠ w := (G.ne_of_adj ha0).symm
    have hk0 : k = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, dlt, Pi.single_apply, if_true,
        if_neg (Ne.symm hw0), hx, smul_eq_mul] at h0
      linarith
    rw [hk0, zero_smul, sub_zero] at hk
    exact hk
  · push_neg at hnbr
    have hle : incLattice G ≤ incLattice G' := by
      change Submodule.span ℤ _ ≤ incLattice G'
      rw [Submodule.span_le]
      rintro _ ⟨⟨e, he⟩, rfl⟩
      induction e using Sym2.ind with
      | _ a b =>
      have hab : G.Adj a b := he
      have ha : a ≠ w := fun h' => hnbr b (h' ▸ hab)
      have hb : b ≠ w := fun h' => hnbr a (h' ▸ hab.symm)
      change incVec s(a, b) ∈ incLattice G'
      rw [incVec_mk (G.ne_of_adj hab)]
      exact gen_mem (hG' a b hab ha hb)
    exact hle hxG

end Incidence

open Incidence

variable {V I : Type*} [Fintype V]

/-! ## 2. Proyección de descomposiciones sobre una estrella -/

omit [Fintype V] in
lemma ind_eq_sum_of_decomposition {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F K D) :
    ind K = ∑ T ∈ D, ind (triEdges T) := by
  funext e
  simp only [Finset.sum_apply, ind]
  by_cases he : e ∈ K
  · obtain ⟨T, hT, heT⟩ := hD.exists_mem he
    rw [if_pos he, Finset.sum_eq_single T]
    · simp [heT]
    · intro T' hT' hne
      rw [if_neg]; intro h'; exact hne (hD.unique hT' hT h' heT)
    · intro h; exact absurd hT h
  · rw [if_neg he]; symm
    apply Finset.sum_eq_zero
    intro T hT
    rw [if_neg]; intro h'; exact he (hD.subset hT h')

omit [Fintype V] in
lemma decomp_card {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F K D) : 3 * D.card = K.card := by
  rw [← hD.2.2, Finset.card_biUnion (fun T hT T' hT' hne => hD.2.1 hT hT' hne),
    Finset.sum_congr rfl fun T hT => card_triEdges_three (hD.1 T hT).1]
  simp [mul_comm]

lemma mem_linkEdges {H : Host V I} {F : Set (Multiset I)} {z u w : V} :
    s(u, w) ∈ linkEdges H F z ↔ (linkGraph H F z).Adj u w := by
  simp [linkEdges]

omit [Fintype V] in
lemma triOf_mk (z u w : V) : triOf z s(u, w) = {z, u, w} := by
  ext x; simp [triOf, Sym2.mem_toFinset]

lemma not_mem_of_linkEdges {H : Host V I} {F : Set (Multiset I)} {z : V} {e : Sym2 V}
    (he : e ∈ linkEdges H F z) : z ∉ e ∧ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ u w =>
  obtain ⟨hzu, hzw, huw⟩ := linkGraph_adj_ne (mem_linkEdges.1 he)
  simp [Sym2.mem_iff, hzu, hzw, huw]

/-- Las aristas del triángulo de una arista del enlace. -/
lemma triEdges_triOf {H : Host V I} {F : Set (Multiset I)} {z : V} {e : Sym2 V}
    (he : e ∈ linkEdges H F z) : e ∈ triEdges (triOf z e) ∧ ∀ x ∈ e, s(z, x) ∈ triEdges (triOf z e) := by
  induction e using Sym2.ind with
  | _ u w =>
  obtain ⟨hzu, hzw, huw⟩ := linkGraph_adj_ne (mem_linkEdges.1 he)
  rw [triOf_mk]
  refine ⟨mem_triEdges.2 ⟨by simp, by simp, huw⟩, fun x hx => ?_⟩
  rcases Sym2.mem_iff.1 hx with rfl | rfl
  · exact mem_triEdges.2 ⟨by simp, by simp, hzu⟩
  · exact mem_triEdges.2 ⟨by simp, by simp, hzw⟩

/-- Si el triángulo de `e` está en una descomposición de `K`, sus aristas están en `K`. -/
lemma triOf_edges_mem {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F K D) {z : V} {e : Sym2 V}
    (he : e ∈ linkEdges H F z) (hT : triOf z e ∈ D) : e ∈ K ∧ ∀ x ∈ e, s(z, x) ∈ K := by
  have h := triEdges_triOf he
  exact ⟨hD.subset hT h.1, fun x hx => hD.subset hT (h.2 x hx)⟩

lemma triOf_injOn {H : Host V I} {F : Set (Multiset I)} (z : V) :
    Set.InjOn (triOf z) (linkEdges H F z : Set (Sym2 V)) := by
  intro e he e' he' h
  have hz := (not_mem_of_linkEdges (Finset.mem_coe.1 he)).1
  have hz' := (not_mem_of_linkEdges (Finset.mem_coe.1 he')).1
  apply Sym2.ext
  intro x
  have hx : x ∈ triOf z e ↔ x ∈ triOf z e' := by rw [h]
  simp only [triOf, Finset.mem_insert, Sym2.mem_toFinset] at hx
  constructor
  · intro hxe
    have hxz : x ≠ z := fun h' => hz (h' ▸ hxe)
    rcases hx.1 (Or.inr hxe) with h1 | h1
    · exact absurd h1 hxz
    · exact h1
  · intro hxe
    have hxz : x ≠ z := fun h' => hz' (h' ▸ hxe)
    rcases hx.2 (Or.inr hxe) with h1 | h1
    · exact absurd h1 hxz
    · exact h1

/-- Cadena del enlace de `z` asociada a una familia de triángulos. -/
def decChain (H : Host V I) (F : Set (Multiset I)) (z : V) (D : Finset (Finset V)) :
    Sym2 V → ℤ :=
  fun e => if e ∈ linkEdges H F z ∧ triOf z e ∈ D then 1 else 0

lemma decChain_support {H : Host V I} {F : Set (Multiset I)} {z : V} {D : Finset (Finset V)}
    {e : Sym2 V} (he : decChain H F z D e ≠ 0) : e ∈ linkEdges H F z ∧ triOf z e ∈ D := by
  unfold decChain at he
  split_ifs at he with h
  · exact h
  · exact absurd rfl he

lemma l1E_decChain_le (H : Host V I) (F : Set (Multiset I)) (z : V) (D : Finset (Finset V)) :
    l1E (decChain H F z D) ≤ D.card := by
  have : l1E (decChain H F z D) = ((linkEdges H F z).filter (fun e => triOf z e ∈ D)).card := by
    simp only [l1E, decChain]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rw [← Finset.sum_subset (Finset.subset_univ (linkEdges H F z))]
    · refine Finset.sum_congr rfl fun e he => ?_
      by_cases h : triOf z e ∈ D <;> simp [he, h]
    · intro e _ he
      simp [he]
  rw [this]
  exact_mod_cast Finset.card_le_card_of_injOn (triOf z) (fun e he => (Finset.mem_filter.1 he).2)
    (fun e he e' he' h => triOf_injOn z (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he').1 h)

/-- **Proyección de una descomposición.** -/
theorem starProj_decomp {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F K D) (z : V) :
    bd (decChain H F z D) = starProj z (ind K) := by
  rw [ind_eq_sum_of_decomposition hD, map_sum]
  have h1 : ∑ T ∈ D, starProj z (ind (triEdges T)) =
      ∑ T ∈ D.filter (z ∈ ·), starProj z (ind (triEdges T)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs with h
    · rfl
    · exact starProj_ind_tri_of_not_mem h
  have h2 : bd (decChain H F z D) =
      ∑ e ∈ (linkEdges H F z).filter (fun e => triOf z e ∈ D), incVec e := by
    unfold bd decChain
    rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ (linkEdges H F z))]
    · refine Finset.sum_congr rfl fun e he => ?_
      by_cases h : triOf z e ∈ D <;> simp [he, h]
    · intro e _ he
      simp [he]
  rw [h1, h2]
  refine Finset.sum_nbij (triOf z) ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨he, hT⟩ := Finset.mem_filter.1 he
    exact Finset.mem_filter.2 ⟨hT, by simp [triOf]⟩
  · intro e he e' he' h
    exact triOf_injOn z (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he').1 h
  · intro T hT
    obtain ⟨hTD, hzT⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hT)
    obtain ⟨u, w, huw, hzu, hzw, rfl⟩ := exists_eq_tri_of_mem (hD.1 _ hTD).1 hzT
    refine ⟨s(u, w), ?_, triOf_mk z u w⟩
    have hadj : (linkGraph H F z).Adj u w := ⟨huw, hD.1 _ hTD⟩
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_linkEdges.2 hadj, by rw [triOf_mk]; exact hTD⟩)
  · intro e he
    exact (starProj_triOf (Finset.mem_filter.1 he).1).symm

/-! ## 3. Proyección de los modos de una bisagra -/

omit [Fintype V] in
lemma starProj_wedge_apex {z a b : V} (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b) :
    starProj z (ind (wedge a b z)) = dlt a + dlt b := by
  funext x
  rw [starProj_apply]
  by_cases hx : x = z
  · subst hx; simp [dlt, hza, hzb]
  · rw [if_neg hx]
    simp only [ind, wedge, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, dlt,
      Pi.single_apply, Sym2.eq_iff]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm]

omit [Fintype V] in
lemma starProj_wedge_far {z a b v : V} (hza : z ≠ a) (hzb : z ≠ b) (hzv : z ≠ v) :
    starProj z (ind (wedge a b v)) = 0 := by
  funext x
  rw [starProj_apply]
  split_ifs
  · rfl
  · simp only [ind, wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Pi.zero_apply]
    rw [if_neg]
    tauto

omit [Fintype V] in
lemma starProj_wedge_base {z w a : V} (hzw : z ≠ w) (hza : z ≠ a) :
    starProj z (ind (wedge z w a)) = dlt a := by
  funext x
  rw [starProj_apply]
  by_cases hx : x = z
  · subst hx; simp [dlt, hza]
  · rw [if_neg hx]
    simp only [ind, wedge, Finset.mem_insert, Finset.mem_singleton, dlt, Pi.single_apply,
      Sym2.eq_iff]
    by_cases hxa : x = a <;> simp_all [Ne.symm]

lemma ind_union_wedge_sub {H : Host V I} {F : Set (Multiset I)} {p q a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F p q a b J) (hpq : p ≠ q) (hpa : p ≠ a)
    (hqa : q ≠ a) (hpb : p ≠ b) (hqb : q ≠ b) :
    ind (J ∪ wedge p q a) - ind (J ∪ wedge p q b) = ind (wedge p q a) - ind (wedge p q b) := by
  obtain ⟨h1, h2, -, -⟩ := hJ.isTransformer hpq hpa hqa hpb hqb
  rw [ind_union_of_disjoint h1, ind_union_of_disjoint h2]
  abel

/-- **Proyección en el ápice (§4.1).** Una bisagra `J` entre `abz` y `abv` da `δ_a + δ_b`
como borde de una cadena del enlace de `z` con bases en `J`, de coste
`3‖s‖₁ ≤ 2(|J| + 2)`. -/
theorem hinge_proj_apex {H : Host V I} {F : Set (Multiset I)} {a b z v : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F a b z v J) (hTa : IsAllowed H F {a, b, z})
    (hTb : IsAllowed H F {a, b, v}) (hzv : z ≠ v) :
    ∃ s : Sym2 V → ℤ, bd s = dlt a + dlt b ∧
      (∀ e, s e ≠ 0 → e ∈ linkEdges H F z ∧ e ∈ J) ∧ 3 * l1E s ≤ 2 * (J.card + 2) := by
  obtain ⟨hab, haz, hbz⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hav, hbv⟩ := distinct_of_card_three hTb.1
  obtain ⟨hJE, hdisj, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩ := hJ
  have hJ' : IsHinge H F a b z v J := ⟨hJE, hdisj, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩
  refine ⟨decChain H F z D1 - decChain H F z D2, ?_, ?_, ?_⟩
  · rw [bd_sub, starProj_decomp hD1, starProj_decomp hD2, ← map_sub,
      ind_union_wedge_sub hJ' hab haz hbz hav hbv, map_sub,
      starProj_wedge_apex hab (Ne.symm haz) (Ne.symm hbz),
      starProj_wedge_far (Ne.symm haz) (Ne.symm hbz) hzv, sub_zero]
  · intro e he
    have hJz : s(z, a) ∉ J := fun h => Finset.disjoint_left.1 hdisj h
      (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, Ne.symm haz⟩))
    have hJz' : s(z, b) ∉ J := fun h => Finset.disjoint_left.1 hdisj h
      (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, Ne.symm hbz⟩))
    rw [Pi.sub_apply] at he
    by_cases h1 : decChain H F z D1 e ≠ 0
    · obtain ⟨hl, hT⟩ := decChain_support h1
      refine ⟨hl, ?_⟩
      have hzn := (not_mem_of_linkEdges hl).1
      have := (triOf_edges_mem hD1 hl hT).1
      rcases Finset.mem_union.1 this with h | h
      · exact h
      · exfalso; apply hzn
        simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> simp
    · have h2 : decChain H F z D2 e ≠ 0 := by
        intro h2; apply he; push_neg at h1; rw [h1, h2, sub_zero]
      obtain ⟨hl, hT⟩ := decChain_support h2
      refine ⟨hl, ?_⟩
      obtain ⟨heK, hzK⟩ := triOf_edges_mem hD2 hl hT
      rcases Finset.mem_union.1 heK with h | h
      · exact h
      · exfalso
        simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · have := hzK a (by simp)
          rcases Finset.mem_union.1 this with h' | h'
          · exact hJz h'
          · simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at h'
            rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all
        · have := hzK b (by simp)
          rcases Finset.mem_union.1 this with h' | h'
          · exact hJz' h'
          · simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at h'
            rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all
  · have c1 := decomp_card hD1
    have c2 := decomp_card hD2
    have u1 : (J ∪ wedge a b z).card ≤ J.card + 2 :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_le_two (a := s(a, z)) (b := s(b, z))) _)
    have u2 : (J ∪ wedge a b v).card ≤ J.card + 2 :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_le_two (a := s(a, v)) (b := s(b, v))) _)
    have l1 := l1E_decChain_le H F z D1
    have l2 := l1E_decChain_le H F z D2
    have := l1E_sub_le (decChain H F z D1) (decChain H F z D2)
    have e1 : (3 : ℤ) * D1.card ≤ J.card + 2 := by exact_mod_cast c1 ▸ u1
    have e2 : (3 : ℤ) * D2.card ≤ J.card + 2 := by exact_mod_cast c2 ▸ u2
    linarith

/-- **Proyección en la base (§4.2).** Una bisagra `J` entre `zwa` y `zwb` da `δ_a − δ_b`
como borde de una cadena del enlace de `z` con bases en `J` que evitan `w`. -/
theorem hinge_proj_base {H : Host V I} {F : Set (Multiset I)} {z w a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F z w a b J) (hTa : IsAllowed H F {z, w, a})
    (hTb : IsAllowed H F {z, w, b}) :
    ∃ s : Sym2 V → ℤ, bd s = dlt a - dlt b ∧
      (∀ e, s e ≠ 0 → e ∈ linkEdges H F z ∧ e ∈ J ∧ w ∉ e) ∧
      3 * l1E s ≤ 2 * (J.card + 2) := by
  obtain ⟨hzw, hza, hwa⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hzb, hwb⟩ := distinct_of_card_three hTb.1
  obtain ⟨hJE, hdisj, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩ := hJ
  have hJ' : IsHinge H F z w a b J := ⟨hJE, hdisj, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩
  refine ⟨decChain H F z D1 - decChain H F z D2, ?_, ?_, ?_⟩
  · rw [bd_sub, starProj_decomp hD1, starProj_decomp hD2, ← map_sub,
      ind_union_wedge_sub hJ' hzw hza hwa hzb hwb, map_sub,
      starProj_wedge_base hzw hza, starProj_wedge_base hzw hzb]
  · have hzwJ : s(z, w) ∉ J := fun h => Finset.disjoint_left.1 hdisj h
      (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hzw⟩))
    -- caso genérico para un modo `D` de `J ∪ wedge z w c`
    have hmode : ∀ {c : V} {D : Finset (Finset V)}, z ≠ c → w ≠ c →
        IsDecomposition H F (J ∪ wedge z w c) D → ∀ e, decChain H F z D e ≠ 0 →
          e ∈ linkEdges H F z ∧ e ∈ J ∧ w ∉ e := by
      intro c D hzc hwc hD e he
      obtain ⟨hl, hT⟩ := decChain_support he
      obtain ⟨heK, hzK⟩ := triOf_edges_mem hD hl hT
      have hzn := (not_mem_of_linkEdges hl).1
      have hzw' : s(z, w) ∉ J ∪ wedge z w c := by
        intro h
        rcases Finset.mem_union.1 h with h | h
        · exact hzwJ h
        · simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      have hwe : w ∉ e := fun hw => hzw' (hzK w hw)
      refine ⟨hl, ?_, hwe⟩
      rcases Finset.mem_union.1 heK with h | h
      · exact h
      · exfalso
        simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact hzn (by simp)
        · exact hwe (by simp)
    intro e he
    rw [Pi.sub_apply] at he
    by_cases h1 : decChain H F z D1 e ≠ 0
    · exact hmode hza hwa hD1 e h1
    · have h2 : decChain H F z D2 e ≠ 0 := by
        intro h2; apply he; push_neg at h1; rw [h1, h2, sub_zero]
      exact hmode hzb hwb hD2 e h2
  · have c1 := decomp_card hD1
    have c2 := decomp_card hD2
    have u1 : (J ∪ wedge z w a).card ≤ J.card + 2 :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_le_two (a := s(z, a)) (b := s(w, a))) _)
    have u2 : (J ∪ wedge z w b).card ≤ J.card + 2 :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_le_two (a := s(z, b)) (b := s(w, b))) _)
    have l1 := l1E_decChain_le H F z D1
    have l2 := l1E_decChain_le H F z D2
    have := l1E_sub_le (decChain H F z D1) (decChain H F z D2)
    have e1 : (3 : ℤ) * D1.card ≤ J.card + 2 := by exact_mod_cast c1 ▸ u1
    have e2 : (3 : ℤ) * D2.card ≤ J.card + 2 := by exact_mod_cast c2 ▸ u2
    linarith

/-! ## 4. Enlaces restringidos y robustez de la imagen entera -/

/-- Enlace de `z` restringido a aristas base en `K`. -/
def linkOn (H : Host V I) (F : Set (Multiset I)) (z : V) (K : Finset (Sym2 V)) :
    SimpleGraph V where
  Adj u w := (linkGraph H F z).Adj u w ∧ s(u, w) ∈ K
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.1 rfl⟩

omit [Fintype V] in
lemma linkOn_mono {H : Host V I} {F : Set (Multiset I)} {z : V} {K K' : Finset (Sym2 V)}
    (h : K' ⊆ K) : linkOn H F z K' ≤ linkOn H F z K :=
  fun _ _ hadj => ⟨hadj.1, h hadj.2⟩

/-- El enlace completo es el enlace restringido a las aristas del host. -/
lemma linkOn_edges (H : Host V I) (F : Set (Multiset I)) (z : V) :
    linkOn H F z (edges H) = linkGraph H F z := by
  ext u w
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have := h.2.2.1 u (by simp) w (by simp) h.1
  simp [edges, this]

lemma mem_linkOn_edgeSet {H : Host V I} {F : Set (Multiset I)} {z : V} {K : Finset (Sym2 V)}
    {e : Sym2 V} (hl : e ∈ linkEdges H F z) (hK : e ∈ K) : e ∈ (linkOn H F z K).edgeSet := by
  induction e using Sym2.ind with
  | _ u w => exact ⟨mem_linkEdges.1 hl, hK⟩

/-- **Borrado de aristas del enlace (§4.1).** -/
theorem link_edge_delete {H : Host V I} {F : Set (Multiset I)} {z : V}
    {K K' : Finset (Sym2 V)} (hK : K' ⊆ K)
    (hsup : ∀ a b, (linkOn H F z K).Adj a b → s(a, b) ∉ K' →
      ∃ v J, v ≠ z ∧ IsAllowed H F {a, b, v} ∧ IsHinge H F a b z v J ∧ J ⊆ K') :
    incLattice (linkOn H F z K) = incLattice (linkOn H F z K') := by
  refine incLattice_eq_of_replace (linkOn_mono hK) fun a b hab => ?_
  by_cases hK' : s(a, b) ∈ K'
  · exact gen_mem ⟨hab.1, hK'⟩
  · obtain ⟨v, J, hvz, hTb, hJ, hJK⟩ := hsup a b hab hK'
    have hTa : IsAllowed H F {a, b, z} := by
      have := hab.1.2
      rwa [show ({z, a, b} : Finset V) = {a, b, z} by ext; simp; tauto] at this
    obtain ⟨s, hs, hsupp, -⟩ := hinge_proj_apex hJ hTa hTb (Ne.symm hvz)
    rw [← hs]
    exact bd_mem_incLattice s fun e he =>
      mem_linkOn_edgeSet (hsupp e he).1 (hJK (hsupp e he).2)

/-- **Borrado de un vértice del enlace (§4.2).** -/
theorem link_vertex_delete {H : Host V I} {F : Set (Multiset I)} {z w : V}
    {K : Finset (Sym2 V)}
    (hsup : ∀ a b, (linkOn H F z K).Adj w a → (linkOn H F z K).Adj w b → a ≠ b →
      ∃ J, IsHinge H F z w a b J ∧ J ⊆ K)
    {x : V → ℤ} (hx : x w = 0) :
    x ∈ incLattice (linkOn H F z K) ↔ x ∈ incLattice (linkOn H F z (K.filter (w ∉ ·))) := by
  refine incLattice_vertex_delete (linkOn_mono (Finset.filter_subset _ _)) ?_ ?_ ?_ hx
  · intro u v huv hu hv
    refine ⟨huv.1, Finset.mem_filter.2 ⟨huv.2, ?_⟩⟩
    simp only [Sym2.mem_iff, not_or]
    exact ⟨Ne.symm hu, Ne.symm hv⟩
  · intro v hv
    have := (Finset.mem_filter.1 hv.2).2
    exact this (by simp)
  · intro a b ha hb
    by_cases hab : a = b
    · subst hab; simp
    obtain ⟨J, hJ, hJK⟩ := hsup a b ha hb hab
    obtain ⟨s, hs, hsupp, -⟩ := hinge_proj_base hJ ha.1.2 hb.1.2
    rw [← hs]
    exact bd_mem_incLattice s fun e he =>
      mem_linkOn_edgeSet (hsupp e he).1
        (Finset.mem_filter.2 ⟨hJK (hsupp e he).2.1, (hsupp e he).2.2⟩)

/-- Aristas de `K` que evitan el conjunto de vértices `S`. -/
def avoidSet (K : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  K.filter (fun e => ∀ y ∈ S, y ∉ e)

lemma avoidSet_insert (K : Finset (Sym2 V)) (S : Finset V) (w : V) :
    avoidSet K (insert w S) = (avoidSet K S).filter (w ∉ ·) := by
  ext e
  simp only [avoidSet, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
  tauto

lemma avoidSet_empty (K : Finset (Sym2 V)) : avoidSet K ∅ = K := by
  ext e; simp [avoidSet]

/-- **Borrado iterado de vértices (§4.2).** Los vértices de `Z` se borran uno a uno; cada
paso usa bisagras contenidas en las aristas que evitan los vértices ya borrados. -/
theorem link_vertices_delete {H : Host V I} {F : Set (Multiset I)} {z : V} (Z : Finset V)
    {K : Finset (Sym2 V)}
    (hsup : ∀ S ⊆ Z, ∀ w ∈ Z, w ∉ S → ∀ a b, (linkOn H F z (avoidSet K S)).Adj w a →
      (linkOn H F z (avoidSet K S)).Adj w b → a ≠ b →
      ∃ J, IsHinge H F z w a b J ∧ J ⊆ avoidSet K S)
    {x : V → ℤ} (hx : ∀ y ∈ Z, x y = 0) :
    x ∈ incLattice (linkOn H F z K) ↔ x ∈ incLattice (linkOn H F z (avoidSet K Z)) := by
  suffices h : ∀ S ⊆ Z,
      (x ∈ incLattice (linkOn H F z K) ↔ x ∈ incLattice (linkOn H F z (avoidSet K S))) from
    h Z subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; rw [avoidSet_empty]
  | insert w S hwS ih =>
    intro hsub
    have hS : S ⊆ Z := (Finset.subset_insert w S).trans hsub
    have hw : w ∈ Z := hsub (Finset.mem_insert_self w S)
    rw [ih hS, avoidSet_insert]
    exact link_vertex_delete (hsup S hS w hw hwS) (hx w hw)

/-! ## 5. Robustez desde H3 + H4 -/

/-- Aristas base buenas: del host, fuera de `B`, que evitan `Z`. -/
def goodEdges (H : Host V I) (Z : Finset V) (B : Finset (Sym2 V)) : Finset (Sym2 V) :=
  ((avoidSet (edges H) Z)).filter (· ∉ B)

omit [Fintype V] in
lemma support_mem {J : Finset (Sym2 V)} [Fintype V] {e : Sym2 V} {y : V} (he : e ∈ J)
    (hy : y ∈ e) : y ∈ support J := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, hy⟩

/-- **Robustez de la imagen entera del enlace (S03 §§2–4) desde H3 y H4.** Para `z ∉ Z` y
un grafo malo `B` de grado `≤ d`, con las ventanas de `exists_robust_composite_hinge`, una
demanda que se anula en `Z` está en la imagen entera del enlace de `z` si y sólo si está en
la imagen del enlace restringido a aristas base que evitan `Z` y `B`. -/
theorem link_image_robust {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {z : V}
    (Z : Finset V) (hz : z ∉ Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    {x : V → ℤ} (hx : ∀ y ∈ Z, x y = 0) :
    x ∈ incLattice (linkGraph H F z) ↔ x ∈ incLattice (linkOn H F z (goodEdges H Z B)) := by
  have hdeg0 : ∀ x, degIn (∅ : Finset (Sym2 V)) x ≤ 0 := fun x => by simp [degIn]
  -- 1. borrado de los vértices de `Z`
  have step1 : x ∈ incLattice (linkGraph H F z) ↔
      x ∈ incLattice (linkOn H F z (avoidSet (edges H) Z)) := by
    rw [← linkOn_edges H F z]
    refine link_vertices_delete Z ?_ hx
    intro S hS w hw hwS a b ha hb hab
    have hwin1' : (Z.card : ℝ) + 2 + 4 * (0 : ℕ) < α * Fintype.card V := by
      push_cast; linarith [(by positivity : (0 : ℝ) ≤ 4 * d)]
    have hwin2' : ((Z.card : ℝ) + h + 5 * (0 : ℕ)) * 2 ^ Nat.choose h 2 ≤
        α / 2 * Fintype.card V := by
      push_cast
      refine le_trans ?_ hwin2
      have : (0 : ℝ) ≤ 2 ^ Nat.choose h 2 := by positivity
      nlinarith [(by positivity : (0 : ℝ) ≤ 5 * d)]
    obtain ⟨J, hJ, -, -, hJZ, -⟩ := exists_robust_composite_hinge hα hH3 hH4 hab ha.1.2 hb.1.2
      Z ∅ 0 hdeg0 hwin1' hwin2'
    refine ⟨J, hJ, fun e he => ?_⟩
    simp only [avoidSet, Finset.mem_filter]
    refine ⟨hJ.1 he, fun y hyS hye => ?_⟩
    have hyR := hJZ y (hS hyS) (support_mem he hye)
    have haS : a ∉ S := fun h' => (Finset.mem_filter.1 ha.2).2 a h' (by simp)
    have hbS : b ∉ S := fun h' => (Finset.mem_filter.1 hb.2).2 b h' (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyR
    rcases hyR with rfl | rfl | rfl | rfl
    · exact hz (hS hyS)
    · exact hwS hyS
    · exact haS hyS
    · exact hbS hyS
  -- 2. borrado de las aristas de `B`
  have step2 : incLattice (linkOn H F z (avoidSet (edges H) Z)) =
      incLattice (linkOn H F z (goodEdges H Z B)) := by
    refine link_edge_delete (Finset.filter_subset _ _) fun a b hab hK' => ?_
    have hTa : IsAllowed H F {a, b, z} := by
      have := hab.1.2
      rwa [show ({z, a, b} : Finset V) = {a, b, z} by ext; simp; tauto] at this
    have hX : ((insert z Z).card : ℝ) < α * Fintype.card V := by
      have : ((insert z Z).card : ℝ) ≤ Z.card + 1 := by
        exact_mod_cast Finset.card_insert_le z Z
      linarith [(by positivity : (0 : ℝ) ≤ 4 * d)]
    obtain ⟨v, hTv, hvX⟩ := exists_fresh_apex hH3 hTa (insert z Z) hX
    have hvz : v ≠ z := fun h' => hvX (h' ▸ Finset.mem_insert_self z Z)
    have hvZ : v ∉ Z := fun h' => hvX (Finset.mem_insert_of_mem h')
    obtain ⟨J, hJ, hJB, -, hJZ, -⟩ := exists_robust_composite_hinge hα hH3 hH4
      (Ne.symm hvz) hTa hTv Z B d hdeg hwin1 hwin2
    refine ⟨v, J, hvz, hTv, hJ, fun e he => ?_⟩
    have haZ : a ∉ Z := fun h' => (Finset.mem_filter.1 hab.2).2 a h' (by simp)
    have hbZ : b ∉ Z := fun h' => (Finset.mem_filter.1 hab.2).2 b h' (by simp)
    simp only [goodEdges, avoidSet, Finset.mem_filter]
    refine ⟨⟨hJ.1 he, fun y hyZ hye => ?_⟩, fun heB => Finset.disjoint_left.1 hJB he heB⟩
    have hyR := hJZ y hyZ (support_mem he hye)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyR
    rcases hyR with rfl | rfl | rfl | rfl
    · exact haZ hyZ
    · exact hbZ hyZ
    · exact hz hyZ
    · exact hvZ hyZ
  rw [step1, step2]

end TypedTriangle
