/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ActiveDeletion
public import RequestProject.TypedTriangle.ComponentRowsConverse

@[expose] public section

/-!
# Caminos de estados de la cubierta activa y su proyección (V13, S26 §5, parte B)

Un *camino de estados* es una lista `[X₀, X₁, …, X_k]` de estados `(fila, signo)` con un arco
de la cubierta entre estados consecutivos (`List.IsChain (CAdj G lab F)`). Su proyección
física/virtual es la suma de las proyecciones firmadas de sus aristas (`edgeProjP`,
`edgeProjV` de V12):

* `pathP_reverse` / `pathV_reverse` — invertir el camino cambia el signo de la proyección
  (unicidad de arcos y arco inverso de V12);
* `baug_path` — el borde aumentado de un camino es `φ(X₀) − φ(X_k)`; en particular la
  proyección de todo camino CERRADO está en el núcleo aumentado;
* `pathV_bip` — la proyección virtual se anula en filas bipartitas;
* `pathP_ne_zero_root` — una arista física `e` con proyección no nula sólo contiene raíces de
  estados del camino;
* `norm_path_le` — `‖πP‖₁ + ‖πV‖₁ ≤ k` (longitud del camino).

También los casos cortos de la parte A (`card_ne_one`, `proj_eq_zero_of_card_two`): la
cubierta activa no tiene lazos, y un dígono dirigido se proyecta a cero (unicidad del arco e
inversión). Esto usa las propiedades del grafo activo; no vale para multigrafos con arcos
paralelos arbitrarios.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation

/-! ### Sumas sobre pares consecutivos (genérico) -/

/-- `chainSum f [x₀, …, x_k] = Σ_i f x_i x_{i+1}`. -/
def chainSum {α M : Type*} [AddCommGroup M] (f : α → α → M) : List α → M
  | a :: b :: t => f a b + chainSum f (b :: t)
  | _ => 0

section ChainSum

variable {α M : Type*} [AddCommGroup M] (f : α → α → M)

@[simp] lemma chainSum_nil : chainSum f [] = 0 := rfl
@[simp] lemma chainSum_single (a : α) : chainSum f [a] = 0 := rfl
lemma chainSum_cons_cons (a b : α) (t : List α) :
    chainSum f (a :: b :: t) = f a b + chainSum f (b :: t) := rfl

lemma chainSum_append_pair (l : List α) (b c : α) :
    chainSum f (l ++ [b, c]) = chainSum f (l ++ [b]) + f b c := by
  induction l with
  | nil => simp [chainSum]
  | cons a l ih =>
    cases l with
    | nil => simp [chainSum]
    | cons d l' =>
      simp only [List.cons_append] at ih ⊢
      rw [chainSum_cons_cons, ih, chainSum_cons_cons]
      abel

lemma chainSum_reverse (hf : ∀ a b, f b a = - f a b) (l : List α) :
    chainSum f l.reverse = - chainSum f l := by
  induction l with
  | nil => simp
  | cons a m ih =>
    cases m with
    | nil => simp
    | cons b m =>
      rw [List.reverse_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        chainSum_append_pair, ← List.reverse_cons, ih, chainSum_cons_cons, hf]
      abel

/-- Telescopio: si `f a b = φ a − φ b` en cada paso, la suma es `φ(primero) − φ(último)`. -/
lemma chainSum_telescope {R : α → α → Prop} (φ : α → M) (hf : ∀ a b, R a b → f a b = φ a - φ b)
    (a : α) (t : List α) (h : List.IsChain R (a :: t)) :
    chainSum f (a :: t) = φ a - φ ((a :: t).getLast (by simp)) := by
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
    rw [List.isChain_cons_cons] at h
    rw [chainSum_cons_cons, ih b h.2, hf a b h.1, List.getLast_cons_cons]
    abel

lemma chainSum_add (g : α → α → M) (l : List α) :
    chainSum f l + chainSum g l = chainSum (fun a b => f a b + g a b) l := by
  induction l with
  | nil => simp
  | cons a m ih =>
    cases m with
    | nil => simp
    | cons b m =>
      simp only [chainSum_cons_cons] at ih ⊢
      rw [← ih]; abel

lemma chainSum_apply {β : Type*} (g : α → α → β → ℤ) (l : List α) (x : β) :
    chainSum g l x = chainSum (fun a b => g a b x) l := by
  induction l with
  | nil => rfl
  | cons a m ih =>
    cases m with
    | nil => rfl
    | cons b m => simp only [chainSum_cons_cons, Pi.add_apply, ih]

lemma exists_of_chainSum_ne_zero {g : α → α → ℤ} {l : List α} (h : chainSum g l ≠ 0) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ g a b ≠ 0 := by
  induction l with
  | nil => simp at h
  | cons a m ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      rw [chainSum_cons_cons] at h
      by_cases hab : g a b = 0
      · rw [hab, zero_add] at h
        obtain ⟨c, d, hc, hd, hcd⟩ := ih h
        exact ⟨c, d, List.mem_cons_of_mem _ hc, List.mem_cons_of_mem _ hd, hcd⟩
      · exact ⟨a, b, by simp, by simp, hab⟩

lemma abs_chainSum_le (g : α → α → ℤ) (l : List α) :
    |chainSum g l| ≤ chainSum (fun a b => |g a b|) l := by
  induction l with
  | nil => simp
  | cons a m ih =>
    cases m with
    | nil => simp
    | cons b m =>
      simp only [chainSum_cons_cons]
      exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

lemma chainSum_le_length (g : α → α → ℤ) (hg : ∀ a b, g a b ≤ 1) (a : α) (t : List α) :
    chainSum g (a :: t) ≤ (t.length : ℤ) := by
  induction t generalizing a with
  | nil => simp
  | cons b m ih =>
    rw [chainSum_cons_cons, List.length_cons]
    push_cast
    linarith [hg a b, ih b]

lemma sum_chainSum {β : Type*} [Fintype β] (g : α → α → β → ℤ) (l : List α) :
    ∑ x, chainSum (fun a b => g a b x) l = chainSum (fun a b => ∑ x, g a b x) l := by
  induction l with
  | nil => simp
  | cons a m ih =>
    cases m with
    | nil => simp
    | cons b m => simp only [chainSum_cons_cons, Finset.sum_add_distrib, ih]

end ChainSum

/-! ### Proyección de caminos de estados -/

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- Estados crudos. -/
abbrev St (V : Type*) := Row V × Bool

variable (G lab F) in
/-- Proyección física de un camino de estados. -/
def pathP (l : List (St V)) : Col G → ℤ := chainSum (fun a b => edgeProjP G lab F a b) l

variable (G lab F) in
/-- Proyección virtual de un camino de estados. -/
def pathV (l : List (St V)) : Row V → ℤ := chainSum (fun a b => edgeProjV G lab F a b) l

lemma pathP_reverse (l : List (St V)) : pathP G lab F l.reverse = - pathP G lab F l := by
  unfold pathP
  exact chainSum_reverse _ (fun a b => funext fun q => edgeProjP_swap G lab F a b q) l

lemma pathV_reverse (l : List (St V)) : pathV G lab F l.reverse = - pathV G lab F l := by
  unfold pathV
  exact chainSum_reverse _ (fun a b => funext fun j => edgeProjV_swap G lab F a b j) l

/-- Borde aumentado de un estado: `φ(X) = sgn(s) e_j` para `X = (j, s)`. -/
def stBd (X : St V) (j : Row V) : ℤ := if X.1 = j then sgn X.2 else 0

/-- Linealidad de `B_aug`. -/
lemma baug_add {R P : Type*} [Fintype R] [Fintype P] (S : RowSystem R P) (x x' : P → ℤ)
    (z z' : R → ℤ) (j : R) :
    baug S (x + x') (z + z') j = baug S x z j + baug S x' z' j := by
  unfold baug
  have h : ∀ p, ((if S.r1 p = j then sgn (S.a1 p) * (x + x') p else 0) +
      (if S.r2 p = j then sgn (S.a2 p) * (x + x') p else 0)) =
      ((if S.r1 p = j then sgn (S.a1 p) * x p else 0) +
        (if S.r2 p = j then sgn (S.a2 p) * x p else 0)) +
      ((if S.r1 p = j then sgn (S.a1 p) * x' p else 0) +
        (if S.r2 p = j then sgn (S.a2 p) * x' p else 0)) := fun p => by
    simp only [Pi.add_apply]; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_add_distrib]
  simp only [Pi.add_apply]; ring

lemma baug_zero {R P : Type*} [Fintype R] [Fintype P] (S : RowSystem R P) (j : R) :
    baug S 0 0 j = 0 := by
  unfold baug; simp

lemma baug_chainSum (l : List (St V)) (j : Row V) :
    baug (rowSys G lab F) (pathP G lab F l) (pathV G lab F l) j =
      chainSum (fun a b => baug (rowSys G lab F) (edgeProjP G lab F a b)
        (edgeProjV G lab F a b) j) l := by
  unfold pathP pathV
  induction l with
  | nil => simp [baug_zero]
  | cons a m ih =>
    cases m with
    | nil => simp [baug_zero]
    | cons b m => simp only [chainSum_cons_cons, baug_add, ih]

/-- Borde aumentado de una arista del grafo de estados. -/
lemma baug_edge {a b : St V} (h : CAdj G lab F a b) (j : Row V) :
    baug (rowSys G lab F) (edgeProjP G lab F a b) (edgeProjV G lab F a b) j =
      stBd a j - stBd b j := by
  obtain ⟨α, rfl, rfl⟩ := h
  have h1 : edgeProjP G lab F (src _ α) (tgt _ α) = projP _ α :=
    funext fun q => edgeProjP_arc G lab F α q
  have h2 : edgeProjV G lab F (src _ α) (tgt _ α) = projV _ α :=
    funext fun j => edgeProjV_arc G lab F α j
  rw [h1, h2, baug_proj_arc]
  unfold stBd
  split_ifs <;> simp_all

/-- **Borde aumentado de un camino**: `φ(primero) − φ(último)`. -/
theorem baug_path (a : St V) (t : List (St V)) (h : List.IsChain (CAdj G lab F) (a :: t))
    (j : Row V) :
    baug (rowSys G lab F) (pathP G lab F (a :: t)) (pathV G lab F (a :: t)) j =
      stBd a j - stBd ((a :: t).getLast (by simp)) j := by
  rw [baug_chainSum]
  exact chainSum_telescope _ (fun X => stBd X j) (fun a b hab => baug_edge hab j) a t h

/-- La proyección virtual de una arista se anula en las filas bipartitas. -/
lemma edgeProjV_bip (a b : St V) {j : Row V} (hj : IsBip G lab F j) :
    edgeProjV G lab F a b j = 0 := by
  unfold edgeProjV
  split_ifs with h
  · generalize Classical.choose h = α
    rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
    · simp [projV]
    · simp only [projV]
      rw [if_neg]
      intro hk
      have h1 := k.2
      rw [hk] at h1
      have h2 := (rowSys_nb G lab F j).mpr hj
      rw [h1] at h2
      exact Bool.noConfusion h2
  · rfl

lemma pathV_bip (l : List (St V)) {j : Row V} (hj : IsBip G lab F j) :
    pathV G lab F l j = 0 := by
  unfold pathV
  rw [chainSum_apply]
  induction l with
  | nil => rfl
  | cons a m ih =>
    cases m with
    | nil => rfl
    | cons b m => rw [chainSum_cons_cons, edgeProjV_bip a b hj, ih, add_zero]

/-- Una arista física con proyección no nula sólo contiene raíces de los dos estados. -/
lemma edgeProjP_ne_zero_root {a b : St V} {q : Col G} (h : edgeProjP G lab F a b q ≠ 0)
    {v : V} (hv : v ∈ q.1) : v = a.1.1 ∨ v = b.1.1 := by
  unfold edgeProjP at h
  split_ifs at h with hex
  · obtain ⟨h1, h2⟩ := Classical.choose_spec hex
    generalize Classical.choose hex = α at h h1 h2
    rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
    · by_cases hpq : p = q
      · subst hpq
        rw [← ends_spec G p, Sym2.mem_iff] at hv
        rw [← h1, ← h2]
        cases d <;> simp only [src, tgt, Bool.false_eq_true, if_false, if_true, rowSys, row1,
          row2] <;> tauto
      · simp [projP, hpq] at h
    · simp [projP] at h
  · exact absurd rfl h

/-- **Soporte**: si la proyección física de un camino es no nula en `e ∋ v`, entonces `v` es la
raíz de algún estado del camino. -/
theorem pathP_ne_zero_root {l : List (St V)} {q : Col G} (h : pathP G lab F l q ≠ 0)
    {v : V} (hv : v ∈ q.1) : ∃ X ∈ l, X.1.1 = v := by
  unfold pathP at h
  rw [chainSum_apply] at h
  obtain ⟨a, b, ha, hb, hab⟩ := exists_of_chainSum_ne_zero h
  rcases edgeProjP_ne_zero_root hab hv with rfl | rfl
  · exact ⟨a, ha, rfl⟩
  · exact ⟨b, hb, rfl⟩

/-- Cada arista tiene `‖πP‖₁ + ‖πV‖₁ ≤ 1`. -/
lemma norm_edge_le (a b : St V) :
    ∑ q, |edgeProjP G lab F a b q| + ∑ j, |edgeProjV G lab F a b j| ≤ 1 := by
  unfold edgeProjP edgeProjV
  split_ifs with h
  · generalize Classical.choose h = α
    rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
    · simp only [projP, projV, abs_zero, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
      simp only [if_true]
      cases s <;> cases (if d = true then (rowSys G lab F).a1 p else (rowSys G lab F).a2 p) <;>
        simp [sgn]
    · simp only [projP, projV, abs_zero, Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single k.1 (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      cases s <;> simp [sgn]
  · simp

/-- **Norma de la proyección de un camino** `≤` su longitud. -/
theorem norm_path_le (a : St V) (t : List (St V)) :
    ∑ q, |pathP G lab F (a :: t) q| + ∑ j, |pathV G lab F (a :: t) j| ≤ (t.length : ℤ) := by
  unfold pathP pathV
  simp only [chainSum_apply]
  refine (add_le_add (Finset.sum_le_sum fun q _ => abs_chainSum_le _ _)
    (Finset.sum_le_sum fun j _ => abs_chainSum_le _ _)).trans ?_
  rw [sum_chainSum (fun a b q => |edgeProjP G lab F a b q|),
    sum_chainSum (fun a b j => |edgeProjV G lab F a b j|), chainSum_add]
  exact chainSum_le_length _ (fun a b => norm_edge_le a b) a t

/-! ### Casos cortos de la parte A en la cubierta activa -/

/-- **La cubierta no tiene ciclos de un arco** (no hay lazos). -/
theorem card_ne_one {C : Finset (Arc (rowSys G lab F))}
    (hC : IsSimpleCycle (src _) (tgt _) C) : C.card ≠ 1 := by
  intro h1
  obtain ⟨a, -, ha⟩ := hC.card_eq_one h1
  exact src_ne_tgt G lab F a ha.symm

/-- **Un dígono dirigido se proyecta a cero**: por unicidad del arco, el segundo arco es el
inverso del primero, y sus proyecciones física y virtual se cancelan. -/
theorem proj_eq_zero_of_card_two {C : Finset (Arc (rowSys G lab F))}
    (hC : IsSimpleCycle (src _) (tgt _) C) (h2 : C.card = 2) :
    flowP _ (Circulation.ind C) = 0 ∧ flowV _ (Circulation.ind C) = 0 := by
  obtain ⟨a, b, hab, rfl, h1, h2', -⟩ := hC.card_eq_two h2
  have hb : b = revArc _ a :=
    arc_unique G lab F (by rw [src_revArc, h1]) (by rw [tgt_revArc, h2'])
  subst hb
  constructor
  · funext q
    unfold flowP Circulation.ind
    rw [Fintype.sum_eq_add a (revArc _ a) hab (fun c hc => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [if_neg (by tauto)]; simp)]
    simp [hab, projP_revArc]
  · funext j
    unfold flowV Circulation.ind
    rw [Fintype.sum_eq_add a (revArc _ a) hab (fun c hc => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [if_neg (by tauto)]; simp)]
    simp [hab, projV_revArc]

end TypedTriangle.ActiveCover
