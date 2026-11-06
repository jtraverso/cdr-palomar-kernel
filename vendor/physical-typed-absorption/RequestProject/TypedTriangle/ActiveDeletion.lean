/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ActiveSigns
public import RequestProject.TypedTriangle.DiameterPacking

@[expose] public section

/-!
# Borrado de los estados sobre un conjunto físico `A` (V12, S26 §3)

Se borran todos los estados activos cuya raíz física está en `A`. `survGraph A` es el grafo
inducido de la cubierta sobre los estados activos supervivientes.

**Hipótesis de borrado** (`DeletionHyp`, sólo para raíces `a ∈ A`; son hipótesis geométricas
auxiliares del núcleo preparado, no premisas del teorema global T):

* `conn` — cada componente activa `K` del enlace de `a` sigue conexa tras quitar `A`;
* `bip` — si `K` no es bipartita, `K ∖ A` sigue sin ser bipartita (en el enlace sin `A`);
* `fresh` — toda arista `ab` con `a, b ∈ A` y tercero permitido tiene un tercero
  permitido fuera de `A`;
* `nonempty` — `K ∖ A ≠ ∅` (se deduce de los tamaños: `deletionHyp_nonempty_of_card`).

**Resultado** (`reachable_surv_of_reachable`): dos estados supervivientes conectados en la
cubierta activa siguen conectados en la cubierta sin los estados sobre `A`. La prueba sigue el
argumento del producto de signos: un estado borrado `X` sobre `(a, K)` se sustituye por sus
vecinos supervivientes `nbrSt X u`, `u ∈ K ∖ A` (y sus opuestos si `K` no es bipartita); el
producto de signos en los triángulos `{a, u, w}` y la conexión/no bipartición de `K ∖ A`
conectan esos sustitutos; las filas con raíz borrada adyacentes se tratan aparte con el
tercero fresco.

**Grado y diámetro** (`card_sdiff_le_survDegree`, `surv_dist_lt`): todo superviviente sobre
`(v, K)` tiene `≥ |K ∖ A|` vecinos supervivientes; con `n ≤ C|K|`, `2C|A| ≤ n`, y `≤ C` filas
activas por raíz, el grado es `≥ n/(2C)` y dos supervivientes conectados en la cubierta
original están a distancia `< 12 C²` en la cubierta sin `A`.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

variable (G lab F) in
/-- Estado activo superviviente al borrado de `A`. -/
def Good (A : Finset V) (X : Row V × Bool) : Prop := IsActiveRow G lab F X.1 ∧ X.1.1 ∉ A

variable (G lab F) in
/-- Estados activos supervivientes. -/
abbrev Surv (A : Finset V) := {X : Row V × Bool // Good G lab F A X}

variable (G lab F) in
/-- **Cubierta activa tras borrar los estados sobre `A`.** -/
def survGraph (A : Finset V) : SimpleGraph (Surv G lab F A) where
  Adj x y := CAdj G lab F x.1 y.1
  symm := ⟨fun _ _ h => cadj_symm h⟩
  loopless := ⟨fun _ h => cadj_ne h rfl⟩

variable (G lab F) in
/-- Enlace de `a` sin los vértices de `A`. -/
def linkA (a : V) (A : Finset V) : SimpleGraph V where
  Adj u w := (link G lab F a).Adj u w ∧ u ∉ A ∧ w ∉ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (link G lab F a).loopless.irrefl _ h.1⟩

variable (G lab F) in
/-- Hipótesis de borrado (para raíces en `A`). -/
structure DeletionHyp (A : Finset V) : Prop where
  conn : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∀ u ∈ K, ∀ w ∈ K, u ∉ A → w ∉ A →
    (linkA G lab F a A).Reachable u w
  bip : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ¬ IsBip G lab F (a, K) →
    ¬ ∃ col : V → Bool, ∀ u ∈ K, ∀ w ∈ K, (linkA G lab F a A).Adj u w → col u ≠ col w
  fresh : ∀ a ∈ A, ∀ b ∈ A, LinkActive G lab F a b → ∃ w, w ∉ A ∧ (link G lab F a).Adj b w
  nonempty : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∃ u ∈ K, u ∉ A

/-! ### Conectividad entre supervivientes (sobre estados crudos) -/

variable (G lab F) in
/-- Dos estados supervivientes conectados en `survGraph A`. -/
def SR (A : Finset V) (Z Z' : Row V × Bool) : Prop :=
  ∃ (h : Good G lab F A Z) (h' : Good G lab F A Z'), (survGraph G lab F A).Reachable ⟨Z, h⟩ ⟨Z', h'⟩

variable {A : Finset V}

lemma SR.refl {Z : Row V × Bool} (h : Good G lab F A Z) : SR G lab F A Z Z :=
  ⟨h, h, SimpleGraph.Reachable.refl _⟩

lemma SR.symm {Z Z' : Row V × Bool} (h : SR G lab F A Z Z') : SR G lab F A Z' Z := by
  obtain ⟨h1, h2, r⟩ := h; exact ⟨h2, h1, r.symm⟩

lemma SR.trans {Z Z' Z'' : Row V × Bool} (h : SR G lab F A Z Z') (h' : SR G lab F A Z' Z'') :
    SR G lab F A Z Z'' := by
  obtain ⟨h1, h2, r1⟩ := h
  obtain ⟨h2', h3, r2⟩ := h'
  exact ⟨h1, h3, r1.trans r2⟩

lemma SR.of_cadj {Z Z' : Row V × Bool} (h : Good G lab F A Z) (h' : Good G lab F A Z')
    (hc : CAdj G lab F Z Z') : SR G lab F A Z Z' := ⟨h, h', SimpleGraph.Adj.reachable hc⟩

lemma Good.flip {Z : Row V × Bool} (h : Good G lab F A Z) : Good G lab F A (flipSt Z) := h

variable (G lab F A) in
/-- El cambio de signo es un automorfismo de `survGraph A`. -/
def flipHom : survGraph G lab F A →g survGraph G lab F A where
  toFun x := ⟨flipSt x.1, x.2⟩
  map_rel' h := cadj_flip h

lemma SR.flip {Z Z' : Row V × Bool} (h : SR G lab F A Z Z') :
    SR G lab F A (flipSt Z) (flipSt Z') := by
  obtain ⟨h1, h2, r⟩ := h
  exact ⟨h1.flip, h2.flip, r.map (flipHom G lab F A)⟩

/-! ### Sustitutos de un estado borrado -/

/-- Hechos sobre un vértice de una fila activa. -/
lemma activeRow_mem {a : V} {K : Finset V} (hK : IsActiveRow G lab F (a, K)) {u : V}
    (hu : u ∈ K) : G.Adj a u ∧ K = comp G lab F a u ∧ LinkActive G lab F a u := by
  have hla := linkActive_of_activeRow hK hu
  obtain ⟨u₀, -, hK0⟩ := hK
  simp only at hK0
  obtain ⟨w, hw⟩ := hla
  refine ⟨link_adj_G hw, ?_, ⟨w, hw⟩⟩
  rw [comp_eq_of_mem (hK0 ▸ hu : u ∈ comp G lab F a u₀), hK0]

/-- Sustituto: vecino superviviente por `u ∈ K ∖ A`. -/
lemma good_nbr {X : Row V × Bool} (hX : IsActiveRow G lab F X.1) {u : V} (hu : u ∈ X.1.2)
    (huA : u ∉ A) : Good G lab F A (nbrSt G lab F X u) := by
  obtain ⟨⟨a, K⟩, s⟩ := X
  exact ⟨nbrSt_active (activeRow_mem hX hu).2.2, huA⟩

lemma cadj_nbr_of_mem {X : Row V × Bool} (hX : IsActiveRow G lab F X.1) {u : V}
    (hu : u ∈ X.1.2) : CAdj G lab F X (nbrSt G lab F X u) := by
  obtain ⟨⟨a, K⟩, s⟩ := X
  obtain ⟨h1, h2, -⟩ := activeRow_mem hX hu
  exact cadj_nbr h1 h2

variable (G lab F A) in
/-- Representantes supervivientes de un estado: él mismo si sobrevive; si su raíz está en `A`,
sus vecinos supervivientes (y los de su opuesto si la fila no es bipartita). -/
def InRep (Z y : Row V × Bool) : Prop :=
  Good G lab F A y ∧ (y = Z ∨ (Z.1.1 ∈ A ∧ (CAdj G lab F Z y ∨
    (¬ IsBip G lab F Z.1 ∧ CAdj G lab F (flipSt Z) y))))

/-- Los vecinos supervivientes de un estado activo borrado son sus `nbrSt X u`, `u ∈ K ∖ A`. -/
lemma cadj_good_eq {X y : Row V × Bool} (hXA : X.1.1 ∈ A) (hy : Good G lab F A y)
    (h : CAdj G lab F X y) : y.1.1 ∈ X.1.2 ∧ y = nbrSt G lab F X y.1.1 := by
  rcases cadj_cases h with ⟨-, -, hK, hY⟩ | ⟨hY, -⟩
  · exact ⟨hK ▸ mem_comp_self _ _, hY⟩
  · exact absurd (hY ▸ hXA : y.1.1 ∈ A) hy.2

section Deleted

variable {X : Row V × Bool} (hXact : IsActiveRow G lab F X.1) (hXA : X.1.1 ∈ A)
include hXact

/-- (E1) Dos sustitutos por `u ~ w` en el enlace sin `A`. -/
lemma SR_nbr_nbr {u w : V} (hu : u ∈ X.1.2) (huA : u ∉ A) (hw : w ∈ X.1.2) (hwA : w ∉ A)
    (h : (link G lab F X.1.1).Adj u w) :
    SR G lab F A (nbrSt G lab F X u)
      (if xor (xor (decide (IsBip G lab F X.1)) (decide (IsBip G lab F (u, comp G lab F u X.1.1))))
          (decide (IsBip G lab F (w, comp G lab F w X.1.1)))
      then nbrSt G lab F X w else flipSt (nbrSt G lab F X w)) := by
  obtain ⟨⟨a, K⟩, s⟩ := X
  simp only at hu hw h ⊢
  obtain ⟨-, hKu, -⟩ := activeRow_mem hXact hu
  have hgu := good_nbr (A := A) hXact hu huA
  have hgw := good_nbr (A := A) hXact hw hwA
  obtain ⟨hua, -⟩ := link_adj_rot h
  have hGuw : G.Adj u w := h.2.2.1 u (by simp) w (by simp) h.1
  have hc : CAdj G lab F (nbrSt G lab F ((a, K), s) u)
      (nbrSt G lab F (nbrSt G lab F ((a, K), s) u) w) :=
    cadj_nbr hGuw (comp_eq_of_adj hua).symm
  rw [nbr_nbr_triangle (X := ((a, K), s)) h hKu] at hc
  simp only at hc
  split_ifs at hc ⊢
  · exact SR.of_cadj hgu hgw hc
  · exact SR.of_cadj hgu hgw.flip hc

/-- (E2) En una fila de llegada no bipartita, un sustituto y su opuesto son adyacentes. -/
lemma SR_nbr_flip {u : V} (hu : u ∈ X.1.2) (huA : u ∉ A)
    (hB : ¬ IsBip G lab F (u, comp G lab F u X.1.1)) :
    SR G lab F A (nbrSt G lab F X u) (flipSt (nbrSt G lab F X u)) := by
  have hg := good_nbr (A := A) hXact hu huA
  exact SR.of_cadj hg hg.flip (cadj_vert hB)

/-- Propagación a lo largo del enlace sin `A`: una relación reflexiva y transitiva que vale en
las aristas de `K ∖ A` vale entre dos vértices cualesquiera de `K ∖ A`. -/
lemma rel_of_conn (hH : DeletionHyp G lab F A) (hXA : X.1.1 ∈ A) (Rel : V → V → Prop)
    (hrefl : ∀ u ∈ X.1.2, u ∉ A → Rel u u) (htrans : ∀ u v w, Rel u v → Rel v w → Rel u w)
    (hadj : ∀ u v, u ∈ X.1.2 → u ∉ A → v ∈ X.1.2 → v ∉ A → (link G lab F X.1.1).Adj u v →
      Rel u v) :
    ∀ u w, u ∈ X.1.2 → u ∉ A → w ∈ X.1.2 → w ∉ A → Rel u w := by
  intro u w hu huA hw hwA
  obtain ⟨p⟩ := hH.conn X.1.1 hXA X.1.2 hXact u hu w hw huA hwA
  induction p with
  | nil => exact hrefl _ hu huA
  | @cons u v w' h p ih =>
    have hv : v ∈ X.1.2 := by
      obtain ⟨-, hK, -⟩ := activeRow_mem (a := X.1.1) (K := X.1.2) hXact hu
      rw [hK]; exact mem_comp_of_adj h.1
    exact htrans _ _ _ (hadj u v hu huA hv h.2.2 h.1) (ih hv h.2.2 hw hwA)

/-- Bloques emparejados o cruzados. -/
def Match (u w : V) : Prop :=
  (SR G lab F A (nbrSt G lab F X u) (nbrSt G lab F X w) ∧
      SR G lab F A (flipSt (nbrSt G lab F X u)) (flipSt (nbrSt G lab F X w))) ∨
    (SR G lab F A (nbrSt G lab F X u) (flipSt (nbrSt G lab F X w)) ∧
      SR G lab F A (flipSt (nbrSt G lab F X u)) (nbrSt G lab F X w))

omit hXact in
lemma Match.trans {u v w : V} (h1 : Match (G := G) (lab := lab) (F := F) (A := A) (X := X) u v)
    (h2 : Match (G := G) (lab := lab) (F := F) (A := A) (X := X) v w) :
    Match (G := G) (lab := lab) (F := F) (A := A) (X := X) u w := by
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨a1.trans b1, a2.trans b2⟩
  · exact Or.inr ⟨a1.trans b1, a2.trans b2⟩
  · exact Or.inr ⟨a1.trans b2, a2.trans b1⟩
  · exact Or.inl ⟨a1.trans b2, a2.trans b1⟩

lemma match_all (hH : DeletionHyp G lab F A) (hXA : X.1.1 ∈ A) :
    ∀ u w, u ∈ X.1.2 → u ∉ A → w ∈ X.1.2 → w ∉ A →
      Match (G := G) (lab := lab) (F := F) (A := A) (X := X) u w := by
  apply rel_of_conn hXact hH hXA
  · intro u hu huA
    have hg := good_nbr (A := A) hXact hu huA
    exact Or.inl ⟨SR.refl hg, SR.refl hg.flip⟩
  · intro u v w h1 h2; exact h1.trans h2
  · intro u v hu huA hv hvA h
    have e := SR_nbr_nbr (A := A) hXact hu huA hv hvA h
    have e' := e.flip
    split_ifs at e e'
    · exact Or.inl ⟨e, e'⟩
    · rw [flipSt_flipSt] at e'
      exact Or.inr ⟨e, e'⟩

/-- Forma de los representantes de un estado borrado. -/
lemma inRep_form (hXA : X.1.1 ∈ A) {y : Row V × Bool} (hy : InRep G lab F A X y) :
    ∃ u, u ∈ X.1.2 ∧ u ∉ A ∧ (y = nbrSt G lab F X u ∨
      (¬ IsBip G lab F X.1 ∧ y = flipSt (nbrSt G lab F X u))) := by
  obtain ⟨hg, hy⟩ := hy
  rcases hy with rfl | ⟨-, h | ⟨hB, h⟩⟩
  · exact absurd hXA hg.2
  · obtain ⟨hm, he⟩ := cadj_good_eq hXA hg h
    exact ⟨y.1.1, hm, hg.2, Or.inl he⟩
  · obtain ⟨hm, he⟩ := cadj_good_eq (X := flipSt X) hXA hg h
    rw [nbrSt_flipSt] at he
    exact ⟨y.1.1, hm, hg.2, Or.inr ⟨hB, he⟩⟩

/-- **Los representantes de un estado borrado están conectados entre sí** (conexión y no
bipartición de `K ∖ A`, producto de signos). -/
theorem inRep_connected (hH : DeletionHyp G lab F A) (hXA : X.1.1 ∈ A) {y₁ y₂ : Row V × Bool}
    (h₁ : InRep G lab F A X y₁) (h₂ : InRep G lab F A X y₂) : SR G lab F A y₁ y₂ := by
  obtain ⟨u, hu, huA, hy₁⟩ := inRep_form hXact hXA h₁
  obtain ⟨w, hw, hwA, hy₂⟩ := inRep_form hXact hXA h₂
  have hM := match_all (A := A) hXact hH hXA
  by_cases hB : IsBip G lab F X.1
  · -- fila bipartita: los sustitutos son `nbrSt X u`, todos conectados
    have hQ : ∀ u w, u ∈ X.1.2 → u ∉ A → w ∈ X.1.2 → w ∉ A →
        SR G lab F A (nbrSt G lab F X u) (nbrSt G lab F X w) := by
      apply rel_of_conn hXact hH hXA
      · intro u hu huA; exact SR.refl (good_nbr hXact hu huA)
      · intro u v w h1 h2; exact h1.trans h2
      · intro u v hu huA hv hvA h
        have e := SR_nbr_nbr (A := A) hXact hu huA hv hvA h
        have e' := e.flip
        rw [decide_eq_true hB] at e e'
        by_cases hbu : IsBip G lab F (u, comp G lab F u X.1.1) <;>
          by_cases hbv : IsBip G lab F (v, comp G lab F v X.1.1) <;>
          simp only [hbu, hbv, decide_true, decide_false, Bool.not_true,
            Bool.not_false, Bool.xor_true, Bool.xor_false, if_true, if_false,
            Bool.false_eq_true, flipSt_flipSt] at e e'
        · exact e
        · exact e.trans (SR_nbr_flip hXact hv hvA hbv).symm
        · exact (SR_nbr_flip hXact hu huA hbu).trans e'
        · exact e
    rcases hy₁ with rfl | ⟨hB', -⟩
    · rcases hy₂ with rfl | ⟨hB', -⟩
      · exact hQ u w hu huA hw hwA
      · exact absurd hB hB'
    · exact absurd hB hB'
  · -- fila no bipartita
    have hall : ∀ v, v ∈ X.1.2 → v ∉ A → ∀ z, (z = nbrSt G lab F X v ∨
        z = flipSt (nbrSt G lab F X v)) → ∀ v₀, v₀ ∈ X.1.2 → v₀ ∉ A →
        SR G lab F A (nbrSt G lab F X v₀) (flipSt (nbrSt G lab F X v₀)) →
        SR G lab F A z (nbrSt G lab F X v₀) := by
      intro v hv hvA z hz v₀ hv₀ hv₀A h0
      rcases hM v₀ v hv₀ hv₀A hv hvA with ⟨m1, m2⟩ | ⟨m1, m2⟩ <;> rcases hz with rfl | rfl
      · exact m1.symm
      · exact m2.symm.trans h0.symm
      · exact m2.symm.trans h0.symm
      · exact m1.symm
    have hz₁ : y₁ = nbrSt G lab F X u ∨ y₁ = flipSt (nbrSt G lab F X u) := by
      rcases hy₁ with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have hz₂ : y₂ = nbrSt G lab F X w ∨ y₂ = flipSt (nbrSt G lab F X w) := by
      rcases hy₂ with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    by_cases hex : ∃ v₀, v₀ ∈ X.1.2 ∧ v₀ ∉ A ∧
        SR G lab F A (nbrSt G lab F X v₀) (flipSt (nbrSt G lab F X v₀))
    · obtain ⟨v₀, hv₀, hv₀A, h0⟩ := hex
      exact (hall u hu huA y₁ hz₁ v₀ hv₀ hv₀A h0).trans
        (hall w hw hwA y₂ hz₂ v₀ hv₀ hv₀A h0).symm
    · exfalso
      push_neg at hex
      -- todas las filas de llegada son bipartitas
      have hbipall : ∀ v, v ∈ X.1.2 → v ∉ A → IsBip G lab F (v, comp G lab F v X.1.1) := by
        intro v hv hvA
        by_contra hb
        exact hex v hv hvA (SR_nbr_flip hXact hv hvA hb)
      -- los sustitutos se cruzan en cada arista
      have hcross : ∀ v v', v ∈ X.1.2 → v ∉ A → v' ∈ X.1.2 → v' ∉ A →
          (link G lab F X.1.1).Adj v v' →
          SR G lab F A (nbrSt G lab F X v) (flipSt (nbrSt G lab F X v')) ∧
          SR G lab F A (flipSt (nbrSt G lab F X v)) (nbrSt G lab F X v') := by
        intro v v' hv hvA hv' hv'A h
        have e := SR_nbr_nbr (A := A) hXact hv hvA hv' hv'A h
        have e' := e.flip
        rw [decide_eq_false hB, decide_eq_true (hbipall v hv hvA),
          decide_eq_true (hbipall v' hv' hv'A)] at e e'
        simp only [Bool.false_xor, Bool.xor_self, Bool.false_eq_true, if_false,
          flipSt_flipSt] at e e'
        exact ⟨e, e'⟩
      apply hH.bip X.1.1 hXA X.1.2 hXact hB
      refine ⟨fun v => decide (SR G lab F A (nbrSt G lab F X u) (nbrSt G lab F X v)), ?_⟩
      intro v hv v' hv' hadj
      obtain ⟨hl, hvA, hv'A⟩ := hadj
      obtain ⟨c1, c2⟩ := hcross v v' hv hvA hv' hv'A hl
      by_cases r1 : SR G lab F A (nbrSt G lab F X u) (nbrSt G lab F X v) <;>
        by_cases r2 : SR G lab F A (nbrSt G lab F X u) (nbrSt G lab F X v') <;>
        simp only [r1, r2, decide_true, decide_false, ne_eq, not_true_eq_false,
          Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true]
      · exact hex v' hv' hv'A ((r2.symm.trans r1).trans c1)
      · rcases hM u v' hu huA hv' hv'A with ⟨m1, -⟩ | ⟨m1, -⟩
        · exact r2 m1
        · exact r1 (m1.trans (hcross v' v hv' hv'A hv hvA hl.symm).2)

end Deleted

/-! ### Representantes de un estado cualquiera y paso de arista -/

lemma inRep_self {Z : Row V × Bool} (h : Good G lab F A Z) : InRep G lab F A Z Z :=
  ⟨h, Or.inl rfl⟩

lemma inRep_connected' (hH : DeletionHyp G lab F A) {Z : Row V × Bool}
    (hZ : IsActiveRow G lab F Z.1) {y₁ y₂ : Row V × Bool}
    (h₁ : InRep G lab F A Z y₁) (h₂ : InRep G lab F A Z y₂) : SR G lab F A y₁ y₂ := by
  by_cases hZA : Z.1.1 ∈ A
  · exact inRep_connected hZ hH hZA h₁ h₂
  · have e : ∀ y, InRep G lab F A Z y → y = Z := by
      rintro y ⟨-, h | ⟨h, -⟩⟩
      · exact h
      · exact absurd h hZA
    rw [e _ h₁, e _ h₂]
    exact SR.refl ⟨hZ, hZA⟩

lemma inRep_nbr {Z : Row V × Bool} (hZ : IsActiveRow G lab F Z.1) (hZA : Z.1.1 ∈ A) {u : V}
    (hu : u ∈ Z.1.2) (huA : u ∉ A) : InRep G lab F A Z (nbrSt G lab F Z u) :=
  ⟨good_nbr hZ hu huA, Or.inr ⟨hZA, Or.inl (cadj_nbr_of_mem hZ hu)⟩⟩

/-- **Paso de arista**: dos estados activos adyacentes tienen representantes conectados. -/
lemma step_rep (hH : DeletionHyp G lab F A) {Z Y : Row V × Bool} (hZ : IsActiveRow G lab F Z.1)
    (h : CAdj G lab F Z Y) :
    ∃ z y, InRep G lab F A Z z ∧ InRep G lab F A Y y ∧ SR G lab F A z y := by
  have hY : IsActiveRow G lab F Y.1 := cadj_active hZ h
  by_cases hZA : Z.1.1 ∈ A <;> by_cases hYA : Y.1.1 ∈ A
  · rcases cadj_cases h with ⟨hne, hadj, hK, hYe⟩ | ⟨hYe, hB⟩
    · -- dos raíces borradas adyacentes: tercero fresco
      set b := Y.1.1
      have hbK : b ∈ Z.1.2 := hK ▸ mem_comp_self _ _
      obtain ⟨-, -, hla⟩ := activeRow_mem (a := Z.1.1) (K := Z.1.2) hZ hbK
      obtain ⟨w, hwA, hlw⟩ := hH.fresh Z.1.1 hZA b hYA hla
      have hwZ : w ∈ Z.1.2 := hK ▸ mem_comp_of_adj hlw
      obtain ⟨hba, -⟩ := link_adj_rot hlw
      have hwY : w ∈ Y.1.2 := by rw [hYe]; exact mem_comp_of_adj hba
      have hrZ := inRep_nbr (A := A) hZ hZA hwZ hwA
      have hrY := inRep_nbr (A := A) hY hYA hwY hwA
      have htri := nbr_nbr_triangle (X := Z) hlw hK
      rw [← hYe] at htri
      split_ifs at htri with hpar
      · exact ⟨_, _, hrZ, hrY, by rw [htri]; exact SR.refl hrZ.1⟩
      · by_cases hB1 : IsBip G lab F Z.1
        · by_cases hB2 : IsBip G lab F (b, comp G lab F b Z.1.1)
          · have hB3 : ¬ IsBip G lab F (w, comp G lab F w Z.1.1) := by
              intro hB3
              apply hpar
              rw [decide_eq_true hB1, decide_eq_true hB2, decide_eq_true hB3]; rfl
            refine ⟨_, _, hrZ, hrY, ?_⟩
            rw [htri]
            exact SR.of_cadj hrZ.1 hrZ.1.flip (cadj_vert hB3)
          · have hYrow : Y.1 = (b, comp G lab F b Z.1.1) := by rw [hYe]; rfl
            refine ⟨_, flipSt (nbrSt G lab F Y w), hrZ, ⟨hrY.1.flip, Or.inr ⟨hYA, Or.inr
              ⟨hYrow ▸ hB2, cadj_flip (cadj_nbr_of_mem hY hwY)⟩⟩⟩, ?_⟩
            rw [htri, flipSt_flipSt]
            exact SR.refl hrZ.1
        · refine ⟨flipSt (nbrSt G lab F Z w), _, ⟨hrZ.1.flip, Or.inr ⟨hZA, Or.inr
            ⟨hB1, cadj_flip (cadj_nbr_of_mem hZ hwZ)⟩⟩⟩, hrY, ?_⟩
          rw [htri]
          exact SR.refl hrZ.1.flip
    · -- arco vertical entre dos estados borrados
      obtain ⟨u, hu, huA⟩ := hH.nonempty Z.1.1 hZA Z.1.2 hZ
      have hr := inRep_nbr (A := A) hZ hZA hu huA
      refine ⟨_, _, hr, ⟨hr.1, Or.inr ⟨hYA, Or.inr ⟨?_, ?_⟩⟩⟩, SR.refl hr.1⟩
      · rw [hYe]; exact hB
      · rw [hYe, flipSt_flipSt]; exact cadj_nbr_of_mem hZ hu
  · exact ⟨Y, Y, ⟨⟨hY, hYA⟩, Or.inr ⟨hZA, Or.inl h⟩⟩, inRep_self ⟨hY, hYA⟩,
      SR.refl ⟨hY, hYA⟩⟩
  · exact ⟨Z, Z, inRep_self ⟨hZ, hZA⟩, ⟨⟨hZ, hZA⟩, Or.inr ⟨hYA, Or.inl (cadj_symm h)⟩⟩,
      SR.refl ⟨hZ, hZA⟩⟩
  · exact ⟨Z, Y, inRep_self ⟨hZ, hZA⟩, inRep_self ⟨hY, hYA⟩, SR.of_cadj ⟨hZ, hZA⟩ ⟨hY, hYA⟩ h⟩

/-- **S26 §3: el borrado de los estados sobre `A` preserva las componentes.** Bajo las
hipótesis de borrado (conexión y no bipartición de `K ∖ A` en los enlaces de las raíces
borradas, terceros frescos fuera de `A`, `K ∖ A ≠ ∅`), dos estados activos supervivientes
conectados en la cubierta activa siguen conectados en la cubierta sin los estados sobre `A`. -/
theorem reachable_surv_of_reachable (hH : DeletionHyp G lab F A) {X Y : AState G lab F}
    (hX : X.1.1.1 ∉ A) (hY : Y.1.1.1 ∉ A) (h : (stateGraph G lab F).Reachable X Y) :
    (survGraph G lab F A).Reachable ⟨X.1, X.2, hX⟩ ⟨Y.1, Y.2, hY⟩ := by
  obtain ⟨p⟩ := h
  have key : ∀ (Z Z' : AState G lab F) (_ : (stateGraph G lab F).Walk Z Z') (z z' : Row V × Bool),
      InRep G lab F A Z.1 z → InRep G lab F A Z'.1 z' → SR G lab F A z z' := by
    intro Z Z' q
    induction q with
    | @nil Z₀ => exact fun z z' hz hz' => inRep_connected' hH Z₀.2 hz hz'
    | @cons Z₁ Z₂ Z₃ hadj q ih =>
      intro z z' hz hz'
      obtain ⟨z₁, y₁, hz₁, hy₁, hr⟩ := step_rep hH Z₁.2 hadj
      exact ((inRep_connected' hH Z₁.2 hz hz₁).trans hr).trans (ih y₁ z' hy₁ hz')
  obtain ⟨h1, h2, r⟩ := key X Y p X.1 Y.1 (inRep_self ⟨X.2, hX⟩) (inRep_self ⟨Y.2, hY⟩)
  exact r

/-! ### Grado y diámetro tras el borrado -/

/-- Todo superviviente sobre `(v, K)` tiene al menos `|K ∖ A|` vecinos supervivientes. -/
theorem card_sdiff_le_survDegree (x : Surv G lab F A) :
    (x.1.1.2 \ A).card ≤ (survGraph G lab F A).degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : x.1.1.2 \ A ⊆
      ((survGraph G lab F A).neighborFinset x).image (fun b => b.1.1.1) := by
    intro u hu
    obtain ⟨huK, huA⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨b, hb, rfl⟩ := exists_neighbor_over (G := G) (lab := lab) (F := F) ⟨x.1, x.2.1⟩ huK
    exact Finset.mem_image.mpr ⟨⟨b.1, b.2, huA⟩,
      (SimpleGraph.mem_neighborFinset _ _ _).mpr hb, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Grado mínimo tras el borrado: con `n ≤ C·|K|` para toda componente activa y
`2C·|A| ≤ n`, todo superviviente tiene grado `≥ n/(2C)`. -/
theorem card_le_survDegree (C : ℕ)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hA : 2 * C * A.card ≤ Fintype.card V) (x : Surv G lab F A) :
    Fintype.card V ≤ 2 * C * (survGraph G lab F A).degree x := by
  have h1 := hdeg _ x.2.1
  have h2 := card_sdiff_le_survDegree x
  have h3 : x.1.1.2.card - A.card ≤ (x.1.1.2 \ A).card := Finset.le_card_sdiff _ _
  have h4 : 2 * C * (x.1.1.2.card - A.card) ≤ 2 * C * (survGraph G lab F A).degree x :=
    Nat.mul_le_mul_left _ (h3.trans h2)
  have h5 : 2 * C * (x.1.1.2.card - A.card) = 2 * (C * x.1.1.2.card) - 2 * C * A.card := by
    rw [Nat.mul_sub]; ring_nf
  omega

lemma card_surv_le : Fintype.card (Surv G lab F A) ≤ Fintype.card (AState G lab F) :=
  Fintype.card_le_of_injective (fun x => (⟨x.1, x.2.1⟩ : AState G lab F))
    (fun x y h => Subtype.ext (by have := congrArg Subtype.val h; simpa using this))

/-- `K ∖ A ≠ ∅` se deduce de los tamaños. -/
lemma nonempty_of_card (C : ℕ) (hn : 0 < Fintype.card V)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hA : 2 * C * A.card ≤ Fintype.card V) :
    ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∃ u ∈ K, u ∉ A := by
  intro a _ K hK
  have h1 := hdeg _ hK
  simp only at h1
  by_contra hc
  push_neg at hc
  have hsub : K ⊆ A := hc
  have := Finset.card_le_card hsub
  have h2 : C * K.card ≤ C * A.card := Nat.mul_le_mul_left _ this
  have hC : 0 < C * K.card := by omega
  have : 0 < C := Nat.pos_of_mul_pos_right hC
  nlinarith

/-- **S26 §3, forma final (condicional a la preparación).** Con a lo sumo `C` filas activas por
raíz, componentes activas de tamaño `≥ n/C`, `2C|A| ≤ n` y las hipótesis de borrado, dos estados
activos supervivientes conectados en la cubierta activa están a distancia `< 12 C²` en la
cubierta sin los estados sobre `A`. -/
theorem surv_dist_lt (hH : DeletionHyp G lab F A) (C : ℕ) (hn : 0 < Fintype.card V)
    (hrows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hA : 2 * C * A.card ≤ Fintype.card V) {X Y : AState G lab F}
    (hX : X.1.1.1 ∉ A) (hY : Y.1.1.1 ∉ A) (h : (stateGraph G lab F).Reachable X Y) :
    (survGraph G lab F A).Reachable ⟨X.1, X.2, hX⟩ ⟨Y.1, Y.2, hY⟩ ∧
      (survGraph G lab F A).dist ⟨X.1, X.2, hX⟩ ⟨Y.1, Y.2, hY⟩ < 12 * C ^ 2 := by
  have hr := reachable_surv_of_reachable hH hX hY h
  refine ⟨hr, ?_⟩
  haveI : Nonempty (Surv G lab F A) := ⟨⟨X.1, X.2, hX⟩⟩
  obtain ⟨v, hv⟩ := (survGraph G lab F A).exists_minimal_degree_vertex
  exact Packing.dist_lt_of_card_le C (Fintype.card V) (survGraph G lab F A).minDegree hn
    (card_surv_le.trans (card_AState_le G lab F C hrows))
    (by rw [hv]; exact card_le_survDegree C hdeg hA v)
    (fun w => (survGraph G lab F A).minDegree_le_degree w) hr

/-- Constructor de las hipótesis de borrado: `K ∖ A ≠ ∅` se obtiene de los tamaños. -/
theorem deletionHyp_of_card (C : ℕ) (hn : 0 < Fintype.card V)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hA : 2 * C * A.card ≤ Fintype.card V)
    (conn : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∀ u ∈ K, ∀ w ∈ K, u ∉ A → w ∉ A →
      (linkA G lab F a A).Reachable u w)
    (bip : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ¬ IsBip G lab F (a, K) →
      ¬ ∃ col : V → Bool, ∀ u ∈ K, ∀ w ∈ K, (linkA G lab F a A).Adj u w → col u ≠ col w)
    (fresh : ∀ a ∈ A, ∀ b ∈ A, LinkActive G lab F a b → ∃ w, w ∉ A ∧ (link G lab F a).Adj b w) :
    DeletionHyp G lab F A :=
  ⟨conn, bip, fresh, nonempty_of_card C hn hdeg hA⟩

end TypedTriangle.ActiveCover
