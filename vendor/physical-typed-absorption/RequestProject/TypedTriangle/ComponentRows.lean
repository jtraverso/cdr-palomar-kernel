/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SignedCoverLift
public import RequestProject.TypedTriangle.SparseEdgeDefs

@[expose] public section

/-!
# Grafo de filas de componentes de un host (S26 §2) y lift de un perfil local (§4) — V11

Instancia física de `SignedCover` sobre un host `(G, lab, F)` (con las definiciones
desplegadas de `SparseEdgeDefs`, que coinciden por definición con las de `Defs.lean` para
`⟨G, lab⟩`):

* `link v` — el enlace `L_v`: `u ~ w` si `u ≠ w` y `{v, u, w}` es un triángulo permitido.
* filas `(v, K)` con `K ⊆ V`; las filas de componentes son `(v, comp v u)`. Las demás filas
  no tienen columnas (son aisladas y su `z` es cero).
* `IsBip` — la fila admite una 2-coloración propia de su enlace; `sigma` — signo de un
  vecino (`col` en filas bipartitas, `+1` en las demás); `nb` — filas no bipartitas, que
  llevan la columna virtual `−2 e_j`.
* columnas físicas: las aristas de `G`, con extremos `(a, comp a b)` y `(b, comp b a)` y
  coeficientes `sigma`.

`IsLocalProfile G lab F x` es literalmente el cuerpo del `carrier` de
`TypedTriangle.localGroup ⟨G, lab⟩ F` (`Lattice.lean`). No se identifica grupo local con
retículo físico.

Resultado principal: `local_profile_cover_cycles` — todo perfil local admite un lift
entero `(x, z)` al núcleo aumentado (construido, no supuesto) y una descomposición en
ciclos simples de la cubierta con suma exacta, longitud total `‖x‖₁ + ‖z‖₁ ≤ 2‖x‖₁`, y
ocurrencias por vértice físico `v` acotadas por `Σ_{e ∋ v} |x e|` (= `d_abs(x)` en `v`).
-/

open Finset Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TypedTriangle.ComponentRows

open TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- El enlace `L_v(G)`: `u ~ w` si `u ≠ w` y `{v, u, w}` es un triángulo permitido. -/
def link (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ SparseEdge.IsAllowed G lab F {v, u, w}
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Componente de `u` en el enlace de `v` (como conjunto de vértices). -/
def comp (v u : V) : Finset V := univ.filter (fun w => (link G lab F v).Reachable u w)

/-- Filas: pares `(raíz, conjunto)`; las filas de componentes son `(v, comp v u)`. -/
abbrev Row (V : Type*) := V × Finset V

/-- La fila admite una 2-coloración propia de su enlace. -/
def IsBip (j : Row V) : Prop :=
  ∃ col : V → Bool, ∀ u ∈ j.2, ∀ w ∈ j.2, (link G lab F j.1).Adj u w → col u ≠ col w

/-- Coloración elegida de una fila bipartita. -/
def col (j : Row V) : V → Bool :=
  if h : IsBip G lab F j then Classical.choose h else fun _ => true

/-- Signo `σ_j(u)`: lado en filas bipartitas, `+1` en las no bipartitas. -/
def sigma (j : Row V) (u : V) : Bool := if IsBip G lab F j then col G lab F j u else true

/-- Columnas físicas: las aristas de `G`. -/
abbrev Col := {e : Sym2 V // e ∈ G.edgeSet}

/-- Extremos ordenados elegidos de una arista. -/
def ends (e : Col G) : V × V := Quot.out e.1

/-- Fila del primer extremo. -/
def row1 (e : Col G) : Row V := ((ends G e).1, comp G lab F (ends G e).1 (ends G e).2)

/-- Fila del segundo extremo. -/
def row2 (e : Col G) : Row V := ((ends G e).2, comp G lab F (ends G e).2 (ends G e).1)

/-- **Sistema de filas de componentes** del host. -/
def rowSys : RowSystem (Row V) (Col G) where
  r1 := row1 G lab F
  r2 := row2 G lab F
  a1 e := sigma G lab F (row1 G lab F e) (ends G e).2
  a2 e := sigma G lab F (row2 G lab F e) (ends G e).1
  nb j := !decide (IsBip G lab F j)

/-- **Perfil local**: el cuerpo del `carrier` de `localGroup ⟨G, lab⟩ F` (`Lattice.lean`):
soportado en las aristas y, en cada raíz `v`, en la imagen entera de la incidencia no
orientada del enlace. -/
def IsLocalProfile (x : Sym2 V → ℤ) : Prop :=
  (∀ e, e ∉ SparseEdge.edges G → x e = 0) ∧
    ∀ v, ∃ c : Finset V → ℤ, ∀ w, w ≠ v →
      x s(v, w) = ∑ T ∈ ((univ.filter (SparseEdge.IsAllowed G lab F)).filter (v ∈ ·)).filter
        (w ∈ ·), c T

/-! ### Hechos básicos -/

omit [Fintype V] in
lemma ends_spec (e : Col G) : s((ends G e).1, (ends G e).2) = e.1 := Quot.out_eq _

omit [Fintype V] in
lemma ends_ne (e : Col G) : (ends G e).1 ≠ (ends G e).2 := by
  have h := e.2
  rw [← ends_spec G e, SimpleGraph.mem_edgeSet] at h
  exact h.ne


/-- Término de la columna `e` en la fila `j` de `B_aug`. -/
def term (x : Sym2 V → ℤ) (e : Col G) (j : Row V) : ℤ :=
  (if row1 G lab F e = j then sgn (sigma G lab F (row1 G lab F e) (ends G e).2) * x e.1 else 0) +
    (if row2 G lab F e = j then sgn (sigma G lab F (row2 G lab F e) (ends G e).1) * x e.1 else 0)

/-- Reindexación de un término de columna por el vecino `u` de la raíz. -/
lemma term_eq (x : Sym2 V → ℤ) (e : Col G) (j : Row V) :
    term G lab F x e j = ∑ u, (if e.1 = s(j.1, u) ∧ comp G lab F j.1 u = j.2 then
      sgn (sigma G lab F j u) * x s(j.1, u) else 0) := by
  obtain ⟨v, K⟩ := j
  have hab := ends_ne G e
  have he := (ends_spec G e).symm
  set a := (ends G e).1 with ha
  set b := (ends G e).2 with hb
  unfold term row1 row2
  rw [← ha, ← hb]
  by_cases hav : a = v
  · subst hav
    rw [Finset.sum_eq_single b (fun u _ hu => by
      rw [if_neg]; rintro ⟨h1, -⟩; rw [he, Sym2.eq_iff] at h1
      rcases h1 with ⟨-, h⟩ | ⟨h, h'⟩
      · exact hu h.symm
      · exact hab h'.symm) (by simp)]
    have h2 : ¬ ((b, comp G lab F b a) = (a, K)) := fun h => hab (Prod.mk.inj h).1.symm
    rw [if_neg h2, add_zero]
    by_cases hK : comp G lab F a b = K
    · subst hK; simp [he]
    · have h1 : ¬ ((a, comp G lab F a b) = (a, K)) := fun h => hK (Prod.mk.inj h).2
      rw [if_neg h1, if_neg (fun h => hK h.2)]
  · by_cases hbv : b = v
    · subst hbv
      rw [Finset.sum_eq_single a (fun u _ hu => by
        rw [if_neg]; rintro ⟨h1, -⟩; rw [he, Sym2.eq_iff] at h1
        rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
        · exact hav h
        · exact hu h.symm) (by simp)]
      have h1 : ¬ ((a, comp G lab F a b) = (b, K)) := fun h => hav (Prod.mk.inj h).1
      rw [if_neg h1, zero_add]
      by_cases hK : comp G lab F b a = K
      · subst hK; simp [he, Sym2.eq_swap]
      · have h2 : ¬ ((b, comp G lab F b a) = (b, K)) := fun h => hK (Prod.mk.inj h).2
        rw [if_neg h2, if_neg (fun h => hK h.2)]
    · have h1 : ¬ ((a, comp G lab F a b) = (v, K)) := fun h => hav (Prod.mk.inj h).1
      have h2 : ¬ ((b, comp G lab F b a) = (v, K)) := fun h => hbv (Prod.mk.inj h).1
      rw [if_neg h1, if_neg h2, add_zero]
      symm
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [if_neg]; rintro ⟨h, -⟩; rw [he, Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨-, h⟩
      · exact hav h
      · exact hbv h

/-- La suma de los términos de columna en la fila `(v, K)` es la estrella firmada de `x`
en `v` restringida a `K`. -/
lemma sum_term_eq (x : Sym2 V → ℤ) (hsupp : ∀ e, e ∉ SparseEdge.edges G → x e = 0)
    (j : Row V) : ∑ e : Col G, term G lab F x e j =
      ∑ u, (if comp G lab F j.1 u = j.2 then sgn (sigma G lab F j u) * x s(j.1, u) else 0) := by
  rw [Finset.sum_congr rfl (fun e _ => term_eq G lab F x e j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hE : s(j.1, u) ∈ G.edgeSet
  · rw [Finset.sum_eq_single (⟨s(j.1, u), hE⟩ : Col G) (fun e _ he => by
      rw [if_neg]; rintro ⟨h, -⟩; exact he (Subtype.ext h)) (by simp)]
    simp
  · rw [Finset.sum_eq_zero (fun e _ => by
      rw [if_neg]; rintro ⟨h, -⟩; exact hE (h ▸ e.2))]
    have : x s(j.1, u) = 0 := hsupp _ (by rw [SparseEdge.mem_edges]; exact hE)
    simp [this]

/-- Triángulos permitidos por `v`. -/
def triAt (v : V) : Finset (Finset V) :=
  (univ.filter (SparseEdge.IsAllowed G lab F)).filter (v ∈ ·)

/-- Valor de un triángulo `T ∋ v` en la fila `(v, K)`. -/
def triVal (v : V) (K : Finset V) (T : Finset V) : ℤ :=
  ∑ u ∈ T.erase v, (if comp G lab F v u = K then sgn (sigma G lab F (v, K) u) else 0)

/-- Expresión de la estrella firmada mediante los coeficientes locales `c`. -/
lemma star_eq_sum_tri (x : Sym2 V → ℤ) (hsupp : ∀ e, e ∉ SparseEdge.edges G → x e = 0)
    (v : V) (K : Finset V) (c : Finset V → ℤ)
    (hc : ∀ w, w ≠ v → x s(v, w) = ∑ T ∈ (triAt G lab F v).filter (w ∈ ·), c T) :
    ∑ u, (if comp G lab F v u = K then sgn (sigma G lab F (v, K) u) * x s(v, u) else 0) =
      ∑ T ∈ triAt G lab F v, c T * triVal G lab F v K T := by
  have hvv : x s(v, v) = 0 := hsupp _ (by
    rw [SparseEdge.mem_edges, SimpleGraph.mem_edgeSet]; exact G.irrefl)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  simp only [hvv, mul_zero, ite_self, zero_add]
  calc ∑ u ∈ univ.erase v, (if comp G lab F v u = K then
          sgn (sigma G lab F (v, K) u) * x s(v, u) else 0)
      = ∑ u ∈ univ.erase v, ∑ T ∈ triAt G lab F v, (if u ∈ T then
          (if comp G lab F v u = K then sgn (sigma G lab F (v, K) u) else 0) * c T else 0) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hc u (Finset.ne_of_mem_erase hu), Finset.sum_filter, Finset.mul_sum]
        split_ifs <;> simp
    _ = ∑ T ∈ triAt G lab F v, ∑ u ∈ univ.erase v, (if u ∈ T then
          (if comp G lab F v u = K then sgn (sigma G lab F (v, K) u) else 0) * c T else 0) :=
        Finset.sum_comm
    _ = ∑ T ∈ triAt G lab F v, c T * triVal G lab F v K T := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter, triVal, Finset.mul_sum]
        have : (univ.erase v).filter (· ∈ T) = T.erase v := by
          ext w; simp [and_comm]
        rw [this]
        exact Finset.sum_congr rfl fun w _ => by ring

/-- Valor de un triángulo: nulo en filas bipartitas, siempre par. -/
lemma triVal_spec (v : V) (K : Finset V) {T : Finset V} (hT : T ∈ triAt G lab F v) :
    (IsBip G lab F (v, K) → triVal G lab F v K T = 0) ∧ 2 ∣ triVal G lab F v K T := by
  simp only [triAt, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨hA, hv⟩ := hT
  have hcard : (T.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, hA.1]
  obtain ⟨u1, u2, hne, herase⟩ := Finset.card_eq_two.mp hcard
  have hTeq : T = {v, u1, u2} := by rw [← herase, Finset.insert_erase hv]
  have hadj : (link G lab F v).Adj u1 u2 := ⟨hne, hTeq ▸ hA⟩
  have hcomp : comp G lab F v u1 = comp G lab F v u2 := by
    ext w
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hadj.reachable.symm.trans h, fun h => hadj.reachable.trans h⟩
  have hmem : ∀ u, u ∈ comp G lab F v u := fun u => by
    simp [comp]
  unfold triVal
  rw [herase, Finset.sum_pair hne]
  by_cases hK : comp G lab F v u1 = K
  · have hK2 : comp G lab F v u2 = K := hcomp ▸ hK
    rw [if_pos hK, if_pos hK2]
    by_cases hB : IsBip G lab F (v, K)
    · have hcol : col G lab F (v, K) u1 ≠ col G lab F (v, K) u2 := by
        unfold col; rw [dif_pos hB]
        exact Classical.choose_spec hB u1 (hK ▸ hmem u1) u2 (hK2 ▸ hmem u2) hadj
      have h0 : sgn (sigma G lab F (v, K) u1) + sgn (sigma G lab F (v, K) u2) = 0 := by
        unfold sigma; rw [if_pos hB, if_pos hB]
        revert hcol
        cases col G lab F (v, K) u1 <;> cases col G lab F (v, K) u2 <;> simp [sgn]
      exact ⟨fun _ => h0, by rw [h0]; exact dvd_zero 2⟩
    · unfold sigma; rw [if_neg hB, if_neg hB]
      exact ⟨fun h => absurd h hB, by simp⟩
  · have hK2 : ¬ comp G lab F v u2 = K := hcomp ▸ hK
    rw [if_neg hK, if_neg hK2]
    simp


/-! ### Lift entero al núcleo aumentado -/

/-- Coordenadas virtuales del lift: `z_j = (Σ_{u ∈ K} x_{vu}) / 2` en filas no bipartitas
(`(1/2)·B x` en la fila), `0` en las bipartitas. -/
def zLift (x : Sym2 V → ℤ) (j : Row V) : ℤ :=
  if IsBip G lab F j then 0 else (∑ e : Col G, term G lab F x e j) / 2

lemma rowSys_nb (j : Row V) : (rowSys G lab F).nb j = false ↔ IsBip G lab F j := by
  simp [rowSys]

lemma baug_rowSys (x : Sym2 V → ℤ) (z : Row V → ℤ) (j : Row V) :
    baug (rowSys G lab F) (fun e => x e.1) z j = ∑ e : Col G, term G lab F x e j - 2 * z j := by
  unfold baug term
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1 <;> split_ifs <;> simp_all [rowSys]

/-- **Lift de un perfil local al núcleo aumentado (S26 §2).** Si `x` es un perfil local,
`(x, zLift x)` está en el núcleo de `B_aug` del sistema de filas de componentes. -/
theorem baug_zLift (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (j : Row V) :
    baug (rowSys G lab F) (fun e => x e.1) (zLift G lab F x) j = 0 := by
  rw [baug_rowSys]
  obtain ⟨v, K⟩ := j
  obtain ⟨c, hc⟩ := hx.2 v
  have hsum : ∑ e : Col G, term G lab F x e (v, K) =
      ∑ T ∈ triAt G lab F v, c T * triVal G lab F v K T :=
    (sum_term_eq G lab F x hx.1 (v, K)).trans
      (star_eq_sum_tri G lab F x hx.1 v K c (fun w hw => hc w hw))
  unfold zLift
  by_cases hB : IsBip G lab F (v, K)
  · rw [if_pos hB, hsum, Finset.sum_eq_zero (fun T hT => by
      rw [(triVal_spec G lab F v K hT).1 hB, mul_zero])]
    ring
  · rw [if_neg hB]
    have hdvd : (2 : ℤ) ∣ ∑ e : Col G, term G lab F x e (v, K) := by
      rw [hsum]
      exact Finset.dvd_sum fun T hT => dvd_mul_of_dvd_right (triVal_spec G lab F v K hT).2 _
    rw [Int.mul_ediv_cancel' hdvd]
    ring

lemma root_count_eq (e : Col G) (v : V) (y : ℤ) :
    y * ((if ((rowSys G lab F).r1 e).1 = v then 1 else 0) +
      (if ((rowSys G lab F).r2 e).1 = v then 1 else 0)) = if v ∈ e.1 then y else 0 := by
  have hab := ends_ne G e
  have hmem : v ∈ e.1 ↔ v = (ends G e).1 ∨ v = (ends G e).2 := by
    rw [← ends_spec G e, Sym2.mem_iff]
  simp only [rowSys, row1, row2]
  by_cases h1 : (ends G e).1 = v
  · have h2 : ¬ (ends G e).2 = v := fun h => hab (h1.trans h.symm)
    rw [if_pos h1, if_neg h2, if_pos (hmem.mpr (Or.inl h1.symm))]; ring
  · by_cases h2 : (ends G e).2 = v
    · rw [if_neg h1, if_pos h2, if_pos (hmem.mpr (Or.inr h2.symm))]; ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h => (hmem.mp h).elim (fun h' => h1 h'.symm)
        (fun h' => h2 h'.symm))]; ring

/-- **S26 §§2 y 4 en el host: lift de un perfil local y descomposición en ciclos de la
cubierta con normas y ocurrencias.** Para todo perfil local `x` (cuerpo del `carrier` de
`localGroup ⟨G, lab⟩ F`) existe un lift entero `z` (nulo en filas bipartitas) con
`B_aug(x, z) = 0` y `‖z‖₁ ≤ ‖x‖₁`, y una lista de ciclos simples de la cubierta aumentada:
* cada ciclo se proyecta al núcleo aumentado;
* las proyecciones físicas suman exactamente `x` en cada arista y las virtuales `z`;
* la longitud total es `‖x‖₁ + ‖z‖₁` (≤ `2‖x‖₁`);
* el número de posiciones de ciclos sobre las filas (y estados) del vértice físico `v`
  es a lo sumo `Σ_{e ∋ v} |x e|`, es decir `d_abs(x)` en `v`;
* la descomposición es conforme (sin cancelaciones). -/
theorem local_profile_cover_cycles (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) :
    ∃ z : Row V → ℤ, (∀ j, IsBip G lab F j → z j = 0) ∧
      (∀ j, baug (rowSys G lab F) (fun e => x e.1) z j = 0) ∧
      ∑ j, |z j| ≤ ∑ e : Col G, |x e.1| ∧
      ∃ L : List (Finset (Arc (rowSys G lab F))),
        (∀ C ∈ L, IsSimpleCycle (src _) (tgt _) C) ∧
        (∀ C ∈ L, ∀ j, baug (rowSys G lab F) (flowP _ (Circulation.ind C))
          (flowV _ (Circulation.ind C)) j = 0) ∧
        (∀ e : Col G, (L.map (fun C => flowP _ (Circulation.ind C) e)).sum = x e.1) ∧
        (∀ j, (L.map (fun C => flowV _ (Circulation.ind C) j)).sum = z j) ∧
        (((L.map Finset.card).sum : ℕ) : ℤ) = ∑ e : Col G, |x e.1| + ∑ j, |z j| ∧
        (∀ v, ((∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
            (L.countP (fun C => (j, true) ∈ C.image (src (rowSys G lab F))) +
              L.countP (fun C => (j, false) ∈ C.image (src (rowSys G lab F)))) : ℕ) : ℤ) ≤
          ∑ e : Col G, if v ∈ e.1 then |x e.1| else 0) ∧
        ∀ C ∈ L, ∀ α ∈ C, (∀ e, projP _ α e = 0 ∨ 0 < projP _ α e * x e.1) ∧
          (∀ j, projV _ α j = 0 ∨ 0 < projV _ α j * zLift G lab F x j) := by
  have hz : ∀ j, (rowSys G lab F).nb j = false → zLift G lab F x j = 0 := fun j h => by
    unfold zLift; rw [if_pos ((rowSys_nb G lab F j).mp h)]
  obtain ⟨L, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_cover_cycle_decomp_roots (rowSys G lab F) (fun e => x e.1) (zLift G lab F x)
      Prod.fst hz (baug_zLift G lab F x hx)
  refine ⟨zLift G lab F x, fun j hj => by unfold zLift; rw [if_pos hj],
    baug_zLift G lab F x hx, h6, L, h1, h2, h3, h4, h5, fun v => ?_, h8⟩
  have h := (h7 v).trans_eq (Finset.sum_congr rfl fun e _ => root_count_eq G lab F e v _)
  convert h

end TypedTriangle.ComponentRows
