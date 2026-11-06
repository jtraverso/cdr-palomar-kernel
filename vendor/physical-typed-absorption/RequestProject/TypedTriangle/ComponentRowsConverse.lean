/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ComponentRows

@[expose] public section

/-!
# Recíproca de S26 §2: el núcleo aumentado se proyecta en perfiles locales — V11

Si `(y, w)` está en el núcleo de `B_aug` del sistema de filas de componentes (con `w` nulo
en filas bipartitas), la extensión por cero de `y` es un perfil local
(`IsLocalProfile`, cuerpo del `carrier` de `localGroup`). La prueba es la descripción de la
imagen entera de la incidencia no orientada de un enlace conexo: balance entre lados en
componentes bipartitas, paridad en las no bipartitas (vía caminos con paridad y la
coloración por paridad cuando no hay ciclos impares).

Consecuencia: la parte física de la proyección de cada ciclo de la cubierta es un perfil
local (`cycle_projection_isLocalProfile`).
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ComponentRows

open TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- Vector estrella en `v` de un triángulo. -/
def triVec (v : V) (T : Finset V) : V → ℤ := fun u => if u ∈ T ∧ u ≠ v then 1 else 0

/-- Imagen entera de la incidencia no orientada del enlace de `v`. -/
def starIm (v : V) : Submodule ℤ (V → ℤ) :=
  Submodule.span ℤ (Set.range (fun T : {T // T ∈ triAt G lab F v} => triVec v T.1))

/-- Vector unitario. -/
abbrev dl (u : V) : V → ℤ := Pi.single u 1

lemma adj_mem_starIm {v u w : V} (h : (link G lab F v).Adj u w) :
    dl u + dl w ∈ starIm G lab F v := by
  obtain ⟨huw, hA⟩ := h
  obtain ⟨hvu, hvw, -⟩ := SparseEdge.distinct_of_card_three hA.1
  have hT : ({v, u, w} : Finset V) ∈ triAt G lab F v := by
    simp [triAt, hA]
  have : triVec v {v, u, w} = dl u + dl w := by
    funext a
    simp only [triVec, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, dl,
      Pi.single_apply]
    by_cases hau : a = u
    · subst hau; simp [huw, Ne.symm hvu]
    · by_cases haw : a = w
      · subst haw; simp [hau, Ne.symm hvw]
      · simp [hau, haw]
  rw [← this]
  exact Submodule.subset_span ⟨⟨_, hT⟩, rfl⟩

/-- Alcance con paridad en el enlace de `v`. -/
def ParReach (v : V) : V × Bool → V × Bool → Prop :=
  Relation.ReflTransGen (fun p q => (link G lab F v).Adj p.1 q.1 ∧ q.2 = !p.2)

/-- Signo de paridad. -/
def eps (b : Bool) : ℤ := if b then -1 else 1

lemma parReach_mem {v u0 : V} {q : V × Bool} (h : ParReach G lab F v (u0, false) q) :
    dl u0 - eps q.2 • dl q.1 ∈ starIm G lab F v := by
  induction h with
  | refl => simp [eps]
  | @tail a c _ hstep ih =>
    obtain ⟨hadj, hc⟩ := hstep
    have h2 := adj_mem_starIm G lab F hadj
    have key : dl u0 - eps c.2 • dl c.1 =
        (dl u0 - eps a.2 • dl a.1) + eps a.2 • (dl a.1 + dl c.1) := by
      obtain ⟨c1, c2⟩ := c
      obtain ⟨a1, a2⟩ := a
      simp only at hc ⊢
      subst hc
      cases a2 <;> simp [eps] <;> abel
    rw [key]
    exact Submodule.add_mem _ ih (Submodule.smul_mem _ _ h2)

omit [Fintype V] in
lemma parReach_reachable {v u0 : V} {b0 : Bool} {q : V × Bool}
    (h : ParReach G lab F v (u0, b0) q) : (link G lab F v).Reachable u0 q.1 := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans hstep.1.reachable

omit [Fintype V] in
lemma exists_parReach {v u0 u : V} (h : (link G lab F v).Reachable u0 u) :
    ∃ b, ParReach G lab F v (u0, false) (u, b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨false, Relation.ReflTransGen.refl⟩
  | tail _ hadj ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨!b, Relation.ReflTransGen.tail hb ⟨hadj, rfl⟩⟩

lemma mem_comp_iff {v u0 u : V} :
    u ∈ comp G lab F v u0 ↔ (link G lab F v).Reachable u0 u := by
  simp [comp]

lemma comp_eq_of_mem {v u0 u : V} (h : u ∈ comp G lab F v u0) :
    comp G lab F v u = comp G lab F v u0 := by
  rw [mem_comp_iff] at h
  ext w
  rw [mem_comp_iff, mem_comp_iff]
  exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

lemma col_parity {v u0 : V} (hB : IsBip G lab F (v, comp G lab F v u0)) {q : V × Bool}
    (h : ParReach G lab F v (u0, false) q) :
    col G lab F (v, comp G lab F v u0) q.1 =
      xor (col G lab F (v, comp G lab F v u0) u0) q.2 := by
  induction h with
  | refl => simp
  | @tail a c hab hstep ih =>
    obtain ⟨hadj, hc⟩ := hstep
    have ha : a.1 ∈ comp G lab F v u0 := (mem_comp_iff G lab F).mpr (parReach_reachable G lab F hab)
    have hc' : c.1 ∈ comp G lab F v u0 :=
      (mem_comp_iff G lab F).mpr ((parReach_reachable G lab F hab).trans hadj.reachable)
    have hne : col G lab F (v, comp G lab F v u0) a.1 ≠ col G lab F (v, comp G lab F v u0) c.1 := by
      unfold col; rw [dif_pos hB]
      exact Classical.choose_spec hB a.1 ha c.1 hc' hadj
    rw [hc]
    revert hne ih
    cases col G lab F (v, comp G lab F v u0) a.1 <;> cases col G lab F (v, comp G lab F v u0) c.1 <;>
      cases col G lab F (v, comp G lab F v u0) u0 <;> cases a.2 <;> simp

lemma two_dl_of_not_bip {v u0 : V} (hB : ¬ IsBip G lab F (v, comp G lab F v u0)) :
    (2 : ℤ) • dl u0 ∈ starIm G lab F v := by
  by_contra hno
  have hone : ∀ u, ¬ (ParReach G lab F v (u0, false) (u, true) ∧
      ParReach G lab F v (u0, false) (u, false)) := by
    rintro u ⟨h1, h2⟩
    have m1 := parReach_mem G lab F h1
    have m2 := parReach_mem G lab F h2
    apply hno
    have : (2 : ℤ) • dl u0 = (dl u0 - eps true • dl u) + (dl u0 - eps false • dl u) := by
      simp [eps, two_smul]
    rw [this]
    exact Submodule.add_mem _ m1 m2
  apply hB
  refine ⟨fun u => decide (ParReach G lab F v (u0, false) (u, true)), fun u hu w hw hadj => ?_⟩
  obtain ⟨b, hb⟩ := exists_parReach G lab F ((mem_comp_iff G lab F).mp hu)
  have hw' : ParReach G lab F v (u0, false) (w, !b) := Relation.ReflTransGen.tail hb ⟨hadj, rfl⟩
  cases b
  · have hu1 : ¬ ParReach G lab F v (u0, false) (u, true) := fun h => hone u ⟨h, hb⟩
    have hw1 : ParReach G lab F v (u0, false) (w, true) := hw'
    simp [hu1, hw1]
  · have hw1 : ¬ ParReach G lab F v (u0, false) (w, true) := fun h => hone w ⟨h, hw'⟩
    simp [hb, hw1]

/-- Coeficiente de transporte de `δ_u` a `δ_{u0}` módulo la imagen. -/
def kap (v u0 u : V) : ℤ :=
  if IsBip G lab F (v, comp G lab F v u0) then
    sgn (col G lab F (v, comp G lab F v u0) u) * sgn (col G lab F (v, comp G lab F v u0) u0)
  else 1

lemma dl_sub_mem {v u0 u : V} (hu : u ∈ comp G lab F v u0) :
    dl u - kap G lab F v u0 u • dl u0 ∈ starIm G lab F v := by
  obtain ⟨b, hb⟩ := exists_parReach G lab F ((mem_comp_iff G lab F).mp hu)
  have hm := parReach_mem G lab F hb
  simp only at hm
  unfold kap
  by_cases hB : IsBip G lab F (v, comp G lab F v u0)
  · rw [if_pos hB]
    have hcol := col_parity G lab F hB hb
    simp only at hcol
    rw [hcol]
    have : dl u - (sgn (xor (col G lab F (v, comp G lab F v u0) u0) b) *
        sgn (col G lab F (v, comp G lab F v u0) u0)) • dl u0 =
        (-eps b) • (dl u0 - eps b • dl u) := by
      cases b <;> cases col G lab F (v, comp G lab F v u0) u0 <;> simp [eps, sgn] <;> abel
    rw [this]
    exact Submodule.smul_mem _ _ hm
  · rw [if_neg hB, one_smul]
    cases b
    · have : dl u - dl u0 = (-1 : ℤ) • (dl u0 - eps false • dl u) := by simp [eps]
      rw [this]; exact Submodule.smul_mem _ _ hm
    · have h2 := two_dl_of_not_bip G lab F hB
      have : dl u - dl u0 = (dl u0 - eps true • dl u) - (2 : ℤ) • dl u0 := by
        simp only [eps, two_smul, if_true, neg_smul, one_smul, sub_neg_eq_add]; abel
      rw [this]; exact Submodule.sub_mem _ hm h2

/-- Un vector soportado en una componente y equilibrado según su fila está en la
imagen. -/
lemma restrict_mem_starIm {v u0 : V} (t : V → ℤ) (w : ℤ)
    (hsupp : ∀ u, u ∉ comp G lab F v u0 → t u = 0)
    (hw : IsBip G lab F (v, comp G lab F v u0) → w = 0)
    (hsum : ∑ u ∈ comp G lab F v u0, sgn (sigma G lab F (v, comp G lab F v u0) u) * t u = 2 * w) :
    t ∈ starIm G lab F v := by
  set K := comp G lab F v u0 with hK
  have ht : t = ∑ u ∈ K, t u • dl u := by
    funext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, dl, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with ha
    · rfl
    · exact hsupp a ha
  have hdiff : t - (∑ u ∈ K, t u * kap G lab F v u0 u) • dl u0 ∈ starIm G lab F v := by
    have : ∑ u ∈ K, t u • (dl u - kap G lab F v u0 u • dl u0) =
        t - (∑ u ∈ K, t u * kap G lab F v u0 u) • dl u0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
      rw [← ht]
    rw [← this]
    exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ (dl_sub_mem G lab F hu)
  by_cases hB : IsBip G lab F (v, K)
  · have hzero : ∑ u ∈ K, t u * kap G lab F v u0 u = 0 := by
      unfold kap
      simp only [← hK, if_pos hB]
      have : ∀ u, t u * (sgn (col G lab F (v, K) u) * sgn (col G lab F (v, K) u0)) =
          sgn (col G lab F (v, K) u0) * (sgn (sigma G lab F (v, K) u) * t u) := by
        intro u; unfold sigma; rw [if_pos hB]; ring
      rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.mul_sum, hsum, hw hB]
      ring
    rw [hzero, zero_smul, sub_zero] at hdiff
    exact hdiff
  · have hsum' : ∑ u ∈ K, t u * kap G lab F v u0 u = 2 * w := by
      unfold kap
      simp only [← hK, if_neg hB]
      rw [← hsum]
      refine Finset.sum_congr rfl fun u _ => ?_
      unfold sigma; rw [if_neg hB]; simp [sgn]
    rw [hsum'] at hdiff
    have h2 : (2 * w) • dl u0 = w • ((2 : ℤ) • dl u0) := by rw [smul_smul, mul_comm]
    rw [h2] at hdiff
    have := Submodule.add_mem _ hdiff (Submodule.smul_mem _ w (two_dl_of_not_bip G lab F hB))
    simpa using this


lemma comp_eq_iff {v u0 u : V} :
    comp G lab F v u = comp G lab F v u0 ↔ (link G lab F v).Reachable u0 u := by
  constructor
  · intro h
    have : u ∈ comp G lab F v u := by simp [comp]
    rw [h, mem_comp_iff] at this
    exact this
  · intro h
    exact comp_eq_of_mem G lab F ((mem_comp_iff G lab F).mpr h)

/-- Extensión por cero de un vector sobre las aristas. -/
def extE (y : Col G → ℤ) : Sym2 V → ℤ := fun e => if h : e ∈ G.edgeSet then y ⟨e, h⟩ else 0

omit [Fintype V] in
lemma extE_col (y : Col G → ℤ) (e : Col G) : extE G y e.1 = y e := by simp [extE, e.2]

/-- **Recíproca de S26 §2: el núcleo aumentado está en el grupo local.** Si `(y, w)` está
en el núcleo de `B_aug` del sistema de filas de componentes y `w` es nulo en las filas
bipartitas, la extensión por cero de `y` es un perfil local (cuerpo del `carrier` de
`localGroup ⟨G, lab⟩ F`). -/
theorem kernel_isLocalProfile (y : Col G → ℤ) (w : Row V → ℤ)
    (hw : ∀ j, IsBip G lab F j → w j = 0)
    (hker : ∀ j, baug (rowSys G lab F) y w j = 0) :
    IsLocalProfile G lab F (extE G y) := by
  have hsupp : ∀ e, e ∉ SparseEdge.edges G → extE G y e = 0 := fun e he => by
    rw [SparseEdge.mem_edges] at he; simp [extE, he]
  refine ⟨hsupp, fun v => ?_⟩
  set x := extE G y with hxdef
  have hy : (fun e : Col G => x e.1) = y := funext (extE_col G y)
  have hvv : x s(v, v) = 0 := hsupp _ (by
    rw [SparseEdge.mem_edges, SimpleGraph.mem_edgeSet]; exact G.irrefl)
  have hrow : ∀ K, ∑ u, (if comp G lab F v u = K then
      sgn (sigma G lab F (v, K) u) * x s(v, u) else 0) = 2 * w (v, K) := by
    intro K
    have := hker (v, K)
    rw [← hy, baug_rowSys, sum_term_eq G lab F x hsupp (v, K)] at this
    linarith
  set st : V → ℤ := fun u => if u ≠ v then x s(v, u) else 0 with hst
  have hstx : ∀ u, st u = x s(v, u) := fun u => by
    by_cases h : u = v
    · subst h; simp [hst, hvv]
    · simp [hst, h]
  have hs : st ∈ starIm G lab F v := by
    have hdec : st = ∑ K ∈ univ.image (comp G lab F v),
        (fun u => if comp G lab F v u = K then st u else 0) := by
      funext u
      rw [Finset.sum_apply, Finset.sum_ite_eq]
      simp
    rw [hdec]
    refine Submodule.sum_mem _ fun K hK => ?_
    obtain ⟨u0, -, rfl⟩ := Finset.mem_image.mp hK
    refine restrict_mem_starIm G lab F _ (w (v, comp G lab F v u0)) ?_ (hw _) ?_
    · intro u hu
      rw [if_neg]
      intro h
      exact hu ((mem_comp_iff G lab F).mpr ((comp_eq_iff G lab F).mp h))
    · rw [← hrow]
      refine (Finset.sum_congr (s₂ := univ.filter (fun w => (link G lab F v).Reachable u0 w))
        rfl (fun _ _ => rfl)).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hr : (link G lab F v).Reachable u0 u
      · have h1 : comp G lab F v u = comp G lab F v u0 := (comp_eq_iff G lab F).mpr hr
        simp only [hr, h1, if_true, hstx]
      · have h1 : ¬ comp G lab F v u = comp G lab F v u0 :=
          fun h => hr ((comp_eq_iff G lab F).mp h)
        simp only [hr, h1, if_false]
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hs
  refine ⟨fun T => if h : T ∈ triAt G lab F v then c' ⟨T, h⟩ else 0, fun u hu => ?_⟩
  have h1 : x s(v, u) = st u := (hstx u).symm
  rw [h1, ← hc', Finset.sum_apply]
  change _ = ∑ T ∈ (triAt G lab F v).filter (u ∈ ·), _
  rw [Finset.sum_filter, ← Finset.sum_coe_sort (triAt G lab F v)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Pi.smul_apply, triVec, smul_eq_mul, Finset.coe_mem, dif_pos, Subtype.coe_eta]
  by_cases huT : u ∈ T.1
  · simp [huT, hu]
  · simp [huT]

/-- **La parte física de la proyección de cada ciclo de la cubierta es un perfil local**
(está en el grupo local `M_H`; no se afirma que esté en el retículo físico). -/
theorem cycle_projection_isLocalProfile (C : Finset (Arc (rowSys G lab F)))
    (hC : IsSimpleCycle (src _) (tgt _) C) :
    IsLocalProfile G lab F (extE G (flowP _ (Circulation.ind C))) := by
  refine kernel_isLocalProfile G lab F _ (flowV _ (Circulation.ind C)) (fun j hj => ?_)
    (baug_cycle_eq_zero _ hC)
  unfold flowV
  refine Finset.sum_eq_zero fun α _ => ?_
  rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
  · simp [projV]
  · simp only [projV]
    rw [if_neg, mul_zero]
    intro hk
    have h1 := k.2
    rw [hk] at h1
    have h2 := (rowSys_nb G lab F j).mpr hj
    rw [h1] at h2
    exact Bool.noConfusion h2

end TypedTriangle.ComponentRows
