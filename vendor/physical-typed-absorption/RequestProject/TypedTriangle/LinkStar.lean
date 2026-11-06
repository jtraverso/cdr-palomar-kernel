/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.IncidenceSection
public import RequestProject.TypedTriangle.Lattice

@[expose] public section

/-!
# G1-Z, §3 de la guía V5 — Enlaces, proyección de estrella y `localGroup`

* `linkGraph H F v`: grafo sobre TODO `V` con `u ~ w` si `{v,u,w}` es un triángulo
  permitido. Los no vecinos de `v` quedan como vértices aislados (no son componentes
  activas: la sección de `IncidenceSection` les asigna demanda cero).
* `starProj v`: proyección de estrella `π_v(x)(w) = x_{vw}` (`w ≠ v`), `π_v(x)(v) = 0`.
* `starProj_ind_tri`: identidad lineal única — el borde de un triángulo que contiene `v`
  se proyecta en la columna de incidencia de su arista base en el enlace; los demás
  triángulos aportan cero.
* `mem_localGroup_iff_star`: `x ∈ localGroup H F` si y sólo si `x` está soportado en las
  aristas del host y cada proyección de estrella está en la imagen entera de la incidencia
  del enlace (no es una afirmación de `Λ_H = M_H`).
* `starRetire`: con la sección de coste `(2D+1)` sobre un enlace de diámetro `≤ D`, un
  homomorfismo `ℤ`-lineal que produce coeficientes de triángulos en la estrella de `v` cuya
  proyección es la demanda dada, con coste `≤ (2D+1)‖·‖₁`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

/-! ## El enlace de un vértice -/

/-- Enlace de `v`: `u ~ w` si `{v,u,w}` es un triángulo permitido. -/
def linkGraph (H : Host V I) (F : Set (Multiset I)) (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ IsAllowed H F {v, u, w}
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
lemma linkGraph_adj {H : Host V I} {F : Set (Multiset I)} {v u w : V} :
    (linkGraph H F v).Adj u w ↔ u ≠ w ∧ IsAllowed H F {v, u, w} := Iff.rfl

omit [Fintype V] in
lemma linkGraph_adj_ne {H : Host V I} {F : Set (Multiset I)} {v u w : V}
    (h : (linkGraph H F v).Adj u w) : v ≠ u ∧ v ≠ w ∧ u ≠ w := by
  have := distinct_of_card_three h.2.1
  exact ⟨this.1, this.2.1, this.2.2⟩

omit [Fintype V] in
/-- Todo triángulo que contiene `v` es `{v,u,w}` con `u ≠ w`, ambos distintos de `v`. -/
lemma exists_eq_tri_of_mem {T : Finset V} {v : V} (hT : T.card = 3) (hv : v ∈ T) :
    ∃ u w, u ≠ w ∧ v ≠ u ∧ v ≠ w ∧ T = {v, u, w} := by
  have h2 : (T.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, hT]
  obtain ⟨u, w, huw, he⟩ := Finset.card_eq_two.1 h2
  have hu : u ∈ T.erase v := by rw [he]; simp
  have hw : w ∈ T.erase v := by rw [he]; simp
  refine ⟨u, w, huw, (Finset.ne_of_mem_erase hu).symm, (Finset.ne_of_mem_erase hw).symm, ?_⟩
  rw [← Finset.insert_erase hv, he]

/-! ## Proyección de estrella -/

/-- Proyección de estrella `π_v`. -/
def starProj (v : V) : (Sym2 V → ℤ) →ₗ[ℤ] (V → ℤ) where
  toFun x w := if w = v then 0 else x s(v, w)
  map_add' x y := by funext w; by_cases h : w = v <;> simp [h]
  map_smul' k x := by funext w; by_cases h : w = v <;> simp [h]

omit [Fintype V] in
lemma starProj_apply (v : V) (x : Sym2 V → ℤ) (w : V) :
    starProj v x w = if w = v then 0 else x s(v, w) := rfl

omit [Fintype V] in
/-- **Identidad de proyección.** `π_v(𝟏_{E(T)})` es el indicador de `T ∖ {v}` si `v ∈ T`, y
cero en otro caso. -/
lemma starProj_ind_tri (v : V) (T : Finset V) :
    starProj v (ind (triEdges T)) = fun w => if v ∈ T ∧ w ∈ T ∧ w ≠ v then 1 else 0 := by
  funext w
  rw [starProj_apply]
  by_cases hw : w = v
  · simp [hw]
  · simp only [ind, mem_triEdges, if_neg hw]
    by_cases hv : v ∈ T <;> by_cases hwT : w ∈ T <;> simp [hv, hwT, hw, Ne.symm hw]

omit [Fintype V] in
lemma starProj_ind_tri_of_not_mem {v : V} {T : Finset V} (hv : v ∉ T) :
    starProj v (ind (triEdges T)) = 0 := by
  rw [starProj_ind_tri]; funext w; simp [hv]

omit [Fintype V] in
/-- El borde del triángulo `{v,u,w}` se proyecta en la columna de incidencia de su base
`uw` en el enlace de `v`. -/
lemma starProj_ind_tri_eq_incVec {v u w : V} (hvu : v ≠ u) (hvw : v ≠ w) :
    starProj v (ind (triEdges ({v, u, w} : Finset V))) = incVec s(u, w) := by
  rw [starProj_ind_tri]
  funext x
  simp only [incVec, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x = v
  · subst hx; simp [hvu, hvw]
  · simp [hx]

/-! ## Combinaciones de estrella y la imagen entera del enlace -/

/-- Combinación de estrella de coeficientes `c` sobre los triángulos que contienen `v`. -/
def starComb (H : Host V I) (F : Set (Multiset I)) (v : V) (c : Finset V → ℤ) : V → ℤ :=
  ∑ T ∈ triAt H F v, c T • starProj v (ind (triEdges T))

lemma starComb_eq_starProj (H : Host V I) (F : Set (Multiset I)) (v : V) (c : Finset V → ℤ) :
    starComb H F v c = starProj v (∑ T ∈ triAt H F v, c T • ind (triEdges T)) := by
  simp only [starComb, map_sum, LinearMap.map_smul]

lemma mem_triAt {H : Host V I} {F : Set (Multiset I)} {v : V} {T : Finset V} :
    T ∈ triAt H F v ↔ IsAllowed H F T ∧ v ∈ T := by
  simp [triAt, allowed]

/-- Un triángulo de la estrella de `v` se proyecta en una columna del enlace. -/
lemma starProj_tri_mem {H : Host V I} {F : Set (Multiset I)} {v : V} {T : Finset V}
    (hT : T ∈ triAt H F v) :
    starProj v (ind (triEdges T)) ∈ incLattice (linkGraph H F v) := by
  rw [mem_triAt] at hT
  obtain ⟨u, w, huw, hvu, hvw, rfl⟩ := exists_eq_tri_of_mem hT.1.1 hT.2
  rw [starProj_ind_tri_eq_incVec hvu hvw, incVec_mk huw]
  exact gen_mem ⟨huw, hT.1⟩

lemma starComb_mem (H : Host V I) (F : Set (Multiset I)) (v : V) (c : Finset V → ℤ) :
    starComb H F v c ∈ incLattice (linkGraph H F v) :=
  Submodule.sum_mem _ fun _ hT => Submodule.smul_mem _ _ (starProj_tri_mem hT)

/-- Toda carga de la imagen entera del enlace es una combinación de estrella. -/
lemma exists_starComb {H : Host V I} {F : Set (Multiset I)} {v : V} {y : V → ℤ}
    (hy : y ∈ incLattice (linkGraph H F v)) : ∃ c, starComb H F v c = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hy
    induction e using Sym2.ind with
    | _ u w =>
    have hadj : (linkGraph H F v).Adj u w := he
    obtain ⟨hvu, hvw, huw⟩ := linkGraph_adj_ne hadj
    refine ⟨fun T => if T = {v, u, w} then 1 else 0, ?_⟩
    have hmem : ({v, u, w} : Finset V) ∈ triAt H F v := mem_triAt.2 ⟨hadj.2, by simp⟩
    simp only [starComb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', if_pos hmem]
    exact starProj_ind_tri_eq_incVec hvu hvw
  | zero => exact ⟨0, by simp [starComb]⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨d, hd⟩ := hz
    exact ⟨c + d, by simp [starComb, ← hc, ← hd, add_smul, Finset.sum_add_distrib]⟩
  | smul k y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨k • c, by simp [starComb, ← hc, Finset.smul_sum, mul_smul]⟩

lemma starComb_apply_ne (H : Host V I) (F : Set (Multiset I)) {v w : V} (hw : w ≠ v)
    (c : Finset V → ℤ) :
    starComb H F v c w = ∑ T ∈ (triAt H F v).filter (w ∈ ·), c T := by
  simp only [starComb, Finset.sum_apply, Pi.smul_apply, starProj_ind_tri, smul_eq_mul,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hv : v ∈ T := (mem_triAt.1 hT).2
  by_cases hwT : w ∈ T <;> simp [hv, hwT, hw]

lemma starComb_apply_self (H : Host V I) (F : Set (Multiset I)) (v : V) (c : Finset V → ℤ) :
    starComb H F v c v = 0 := by
  simp [starComb, Finset.sum_apply, starProj_ind_tri]

/-- **Puente `localGroup` ↔ imágenes enteras de los enlaces.** -/
theorem mem_localGroup_iff_star (H : Host V I) (F : Set (Multiset I)) (x : Sym2 V → ℤ) :
    x ∈ localGroup H F ↔ (∀ e, e ∉ edges H → x e = 0) ∧
      ∀ v, starProj v x ∈ incLattice (linkGraph H F v) := by
  constructor
  · rintro ⟨h0, hstar⟩
    refine ⟨h0, fun v => ?_⟩
    obtain ⟨c, hc⟩ := hstar v
    have : starProj v x = starComb H F v c := by
      funext w
      by_cases hw : w = v
      · subst hw; rw [starComb_apply_self, starProj_apply, if_pos rfl]
      · rw [starComb_apply_ne H F hw, starProj_apply, if_neg hw, hc w hw]
    rw [this]; exact starComb_mem H F v c
  · rintro ⟨h0, hstar⟩
    refine ⟨h0, fun v => ?_⟩
    obtain ⟨c, hc⟩ := exists_starComb (hstar v)
    refine ⟨c, fun w hw => ?_⟩
    have := congrFun hc w
    rw [starComb_apply_ne H F hw, starProj_apply, if_neg hw] at this
    exact this.symm

/-- La proyección de estrella de un elemento de `M_H` está en la imagen del enlace. -/
lemma starProj_mem_of_localGroup {H : Host V I} {F : Set (Multiset I)} {x : Sym2 V → ℤ}
    (hx : x ∈ localGroup H F) (v : V) : starProj v x ∈ incLattice (linkGraph H F v) :=
  ((mem_localGroup_iff_star H F x).1 hx).2 v

/-! ## Retiro lineal de una estrella con coste controlado -/

/-- Aristas del enlace de `v` como `Finset`. -/
def linkEdges (H : Host V I) (F : Set (Multiset I)) (v : V) : Finset (Sym2 V) :=
  univ.filter (· ∈ (linkGraph H F v).edgeSet)

/-- Triángulo de la estrella de `v` sobre una arista del enlace. -/
def triOf (v : V) (e : Sym2 V) : Finset V := insert v e.toFinset

lemma triOf_mem {H : Host V I} {F : Set (Multiset I)} {v : V} {e : Sym2 V}
    (he : e ∈ linkEdges H F v) : triOf v e ∈ triAt H F v := by
  simp only [linkEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  induction e using Sym2.ind with
  | _ u w =>
  have hadj : (linkGraph H F v).Adj u w := he
  refine mem_triAt.2 ⟨?_, by simp [triOf]⟩
  have : triOf v s(u, w) = {v, u, w} := by
    ext x; simp [triOf, Sym2.mem_toFinset]
  rw [this]; exact hadj.2

lemma starProj_triOf {H : Host V I} {F : Set (Multiset I)} {v : V} {e : Sym2 V}
    (he : e ∈ linkEdges H F v) : starProj v (ind (triEdges (triOf v e))) = incVec e := by
  simp only [linkEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  induction e using Sym2.ind with
  | _ u w =>
  have hadj : (linkGraph H F v).Adj u w := he
  obtain ⟨hvu, hvw, -⟩ := linkGraph_adj_ne hadj
  have : triOf v s(u, w) = {v, u, w} := by
    ext x; simp [triOf, Sym2.mem_toFinset]
  rw [this, starProj_ind_tri_eq_incVec hvu hvw]

/-- Paso lineal de cadenas del enlace a coeficientes de triángulos de la estrella. -/
def edgeTriL (H : Host V I) (F : Set (Multiset I)) (v : V) :
    (Sym2 V → ℤ) →ₗ[ℤ] (Finset V → ℤ) where
  toFun s T := ∑ e ∈ (linkEdges H F v).filter (fun e => triOf v e = T), s e
  map_add' s t := by funext T; simp [Finset.sum_add_distrib]
  map_smul' k s := by funext T; simp [Finset.mul_sum]

lemma edgeTriL_apply (H : Host V I) (F : Set (Multiset I)) (v : V) (s : Sym2 V → ℤ)
    (T : Finset V) :
    edgeTriL H F v s T = ∑ e ∈ (linkEdges H F v).filter (fun e => triOf v e = T), s e := rfl

/-- Los coeficientes producidos están soportados en la estrella de `v`. -/
lemma edgeTriL_support (H : Host V I) (F : Set (Multiset I)) (v : V) (s : Sym2 V → ℤ)
    {T : Finset V} (hT : edgeTriL H F v s T ≠ 0) : T ∈ triAt H F v := by
  rw [edgeTriL_apply] at hT
  obtain ⟨e, he, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  have h := Finset.mem_filter.1 he
  rw [← h.2]; exact triOf_mem h.1

/-- Su combinación de estrella es el borde de la cadena (si está soportada en el enlace). -/
lemma starComb_edgeTriL (H : Host V I) (F : Set (Multiset I)) (v : V) (s : Sym2 V → ℤ)
    (hs : ∀ e, s e ≠ 0 → e ∈ (linkGraph H F v).edgeSet) :
    starComb H F v (edgeTriL H F v s) = bd s := by
  have hmaps : ∀ e ∈ linkEdges H F v, triOf v e ∈ triAt H F v := fun e he => triOf_mem he
  calc starComb H F v (edgeTriL H F v s)
      = ∑ T ∈ triAt H F v, ∑ e ∈ (linkEdges H F v).filter (fun e => triOf v e = T),
          s e • starProj v (ind (triEdges (triOf v e))) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [edgeTriL_apply, Finset.sum_smul]
        exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
    _ = ∑ e ∈ linkEdges H F v, s e • starProj v (ind (triEdges (triOf v e))) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ e ∈ linkEdges H F v, s e • incVec e :=
        Finset.sum_congr rfl fun e he => by rw [starProj_triOf he]
    _ = bd s := by
        rw [bd]
        refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
        have : s e = 0 := by
          by_contra h
          exact he (by simp [linkEdges, hs e h])
        rw [this, zero_smul]

/-- Coste de los coeficientes: `Σ_T |c_T| ≤ ‖s‖₁`. -/
lemma sum_abs_edgeTriL_le (H : Host V I) (F : Set (Multiset I)) (v : V) (s : Sym2 V → ℤ) :
    ∑ T ∈ triAt H F v, |edgeTriL H F v s T| ≤ l1E s := by
  have hmaps : ∀ e ∈ linkEdges H F v, triOf v e ∈ triAt H F v := fun e he => triOf_mem he
  calc ∑ T ∈ triAt H F v, |edgeTriL H F v s T|
      ≤ ∑ T ∈ triAt H F v, ∑ e ∈ (linkEdges H F v).filter (fun e => triOf v e = T), |s e| :=
        Finset.sum_le_sum fun T _ => by
          rw [edgeTriL_apply]; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e ∈ linkEdges H F v, |s e| := Finset.sum_fiberwise_of_maps_to hmaps _
    _ ≤ l1E s := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => abs_nonneg _

/-- **Retiro lineal de estrella.** Si el enlace de `v` tiene diámetro `≤ D`, el homomorfismo
`starRetire = edgeTriL ∘ secL` da, para cada carga `y` de la imagen entera del enlace,
coeficientes de triángulos de la estrella de `v` cuya proyección es `y`, con coste
`≤ (2D+1)‖y‖₁`. -/
def starRetire (H : Host V I) (F : Set (Multiset I)) (v : V) {D : ℕ}
    (hD : DiamLe (linkGraph H F v) D) :
    incLattice (linkGraph H F v) →ₗ[ℤ] (Finset V → ℤ) :=
  (edgeTriL H F v).comp (secL hD)

theorem starRetire_spec (H : Host V I) (F : Set (Multiset I)) (v : V) {D : ℕ}
    (hD : DiamLe (linkGraph H F v) D) (y : incLattice (linkGraph H F v)) :
    (∀ T, starRetire H F v hD y T ≠ 0 → T ∈ triAt H F v) ∧
    starProj v (∑ T ∈ triAt H F v, starRetire H F v hD y T • ind (triEdges T)) = y.1 ∧
    ∑ T ∈ triAt H F v, |starRetire H F v hD y T| ≤ (2 * D + 1) * l1V y.1 := by
  refine ⟨fun T hT => edgeTriL_support H F v _ hT, ?_, ?_⟩
  · rw [← starComb_eq_starProj]
    simp only [starRetire, LinearMap.comp_apply]
    rw [starComb_edgeTriL H F v _ (secL_support hD y), bd_secL]
  · exact (sum_abs_edgeTriL_le H F v _).trans (l1E_secL_le hD y)

/-- **Retiro de la estrella de un elemento de `M_H`.** Restar la combinación de triángulos
producida por `starRetire` anula la estrella en `v`, conserva `M_H` y cuesta
`≤ (2D+1) Σ_{w≠v} |x_{vw}|`. -/
theorem star_retire_localGroup {H : Host V I} {F : Set (Multiset I)} {x : Sym2 V → ℤ}
    (hx : x ∈ localGroup H F) (v : V) {D : ℕ} (hD : DiamLe (linkGraph H F v) D) :
    ∃ c : Finset V → ℤ, (∀ T, c T ≠ 0 → T ∈ triAt H F v) ∧
      starProj v (x - ∑ T ∈ triAt H F v, c T • ind (triEdges T)) = 0 ∧
      x - ∑ T ∈ triAt H F v, c T • ind (triEdges T) ∈ localGroup H F ∧
      ∑ T ∈ triAt H F v, |c T| ≤ (2 * D + 1) * l1V (starProj v x) := by
  set y : incLattice (linkGraph H F v) := ⟨starProj v x, starProj_mem_of_localGroup hx v⟩
  obtain ⟨h1, h2, h3⟩ := starRetire_spec H F v hD y
  refine ⟨starRetire H F v hD y, h1, ?_, ?_, h3⟩
  · rw [map_sub, h2, sub_self]
  · refine Submodule.sub_mem _ hx (Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _ ?_)
    exact lattice_le_localGroup H F
      (Submodule.subset_span ⟨T, (mem_triAt.1 hT).1, rfl⟩)

end TypedTriangle
