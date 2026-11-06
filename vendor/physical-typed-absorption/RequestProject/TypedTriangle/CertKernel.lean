/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.AveragedCert
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 — Núcleo de certificados de dos niveles (definiciones y borde)

Construcción determinista (promedio exacto) de la guía V4 §A1–A2:

* pivotes GLOBALES `p_f = promedio_{b ∈ Piv f} δ_{f ∪ {b}}`, compartidos por todas las fuentes;
* para un triángulo `T = {u,v,a}` con `uv ∈ B`, un ápice INTERMEDIO `c` (elegido después de
  `b`) y dos bisagras `uva → uvc → uvb` que evitan `B`; así la pareja `ab` puede estar en `B`;
* en el primer modo, los triángulos `Q` que contienen aristas borradas (sólo pueden ser las de
  la cuña `W_a`, una por triángulo) se retiran y se sustituyen por su certificado de una
  arista construido con el pivote global de esa arista (sustitución finita de profundidad 2;
  incluye el caso `T ∈ Q` con tres aristas borradas).

Los datos `Piv`, `Cs`, `fam` (pivotes, ápices intermedios y familias de bisagras) son
parámetros; `KHyp` recoge exactamente lo que el borde y el soporte necesitan. El archivo
`CertProvider.lean` construye datos concretos a partir de (H4) y del grado triangular.

Resultado principal de este archivo: `bdry_kcert`,
`∂ cert_T = 1_{E(T)} − Σ_{f ∈ B} 1_{E(T)}(f) ∂p_f` para todo triángulo permitido `T`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-! ### Promedios finitos -/

/-- Promedio uniforme sobre un `Finset` (cero si es vacío). -/
def avgOver {α : Type*} (s : Finset α) (g : α → ℝ) : ℝ := ∑ x ∈ s, (1 / (s.card : ℝ)) * g x

lemma avgOver_const {α : Type*} {s : Finset α} (hs : s.Nonempty) (k : ℝ) :
    avgOver s (fun _ => k) = k := by
  unfold avgOver
  have : (s.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 hs).ne'
  rw [sum_const, nsmul_eq_mul]; field_simp

lemma avgOver_add {α : Type*} (s : Finset α) (f g : α → ℝ) :
    avgOver s (fun x => f x + g x) = avgOver s f + avgOver s g := by
  unfold avgOver; rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring

lemma avgOver_sub {α : Type*} (s : Finset α) (f g : α → ℝ) :
    avgOver s (fun x => f x - g x) = avgOver s f - avgOver s g := by
  unfold avgOver; rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring

lemma avgOver_congr {α : Type*} {s : Finset α} {f g : α → ℝ} (h : ∀ x ∈ s, f x = g x) :
    avgOver s f = avgOver s g := by
  unfold avgOver; exact sum_congr rfl fun x hx => by rw [h x hx]

lemma avgOver_le {α : Type*} {s : Finset α} {f g : α → ℝ} (h : ∀ x ∈ s, f x ≤ g x) :
    avgOver s f ≤ avgOver s g := by
  unfold avgOver
  exact sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (h x hx) (by positivity)

lemma avgOver_nonneg {α : Type*} {s : Finset α} {f : α → ℝ} (h : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ avgOver s f := by
  unfold avgOver; exact sum_nonneg fun x hx => mul_nonneg (by positivity) (h x hx)

lemma abs_avgOver_le {α : Type*} (s : Finset α) (f : α → ℝ) :
    |avgOver s f| ≤ avgOver s (fun x => |f x|) := by
  unfold avgOver
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
  rw [abs_mul, abs_of_nonneg (by positivity)]

lemma avgOver_mul_const {α : Type*} (s : Finset α) (f : α → ℝ) (k : ℝ) :
    avgOver s (fun x => f x * k) = avgOver s f * k := by
  unfold avgOver; rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring

lemma avgOver_const_mul {α : Type*} (s : Finset α) (f : α → ℝ) (k : ℝ) :
    avgOver s (fun x => k * f x) = k * avgOver s f := by
  unfold avgOver; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

lemma avgOver_eq_zero {α : Type*} {s : Finset α} {f : α → ℝ} (h : ∀ x ∈ s, f x = 0) :
    avgOver s f = 0 := by
  unfold avgOver; exact sum_eq_zero fun x hx => by rw [h x hx, mul_zero]

/-- Promedio de una indicatriz: fracción de elementos que la satisfacen. -/
lemma avgOver_ite {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    avgOver s (fun x => if P x then (1 : ℝ) else 0) = (s.filter P).card / s.card := by
  unfold avgOver
  rw [← mul_sum, sum_boole]; ring

/-- Borde de un promedio. -/
lemma bdry_avgOver {H : Host V I} {F : Set (Multiset I)} {α : Type*} (s : Finset α)
    (g : α → Finset V → ℝ) (e : Sym2 V) :
    bdry H F (fun S => avgOver s (fun x => g x S)) e = avgOver s (fun x => bdry H F (g x) e) :=
  bdry_sum_smul s (fun _ => 1 / (s.card : ℝ)) g e

lemma bdry_add' {H : Host V I} {F : Set (Multiset I)} (f g : Finset V → ℝ) (e : Sym2 V) :
    bdry H F (fun S => f S + g S) e = bdry H F f e + bdry H F g e := by
  unfold bdry; rw [← sum_add_distrib]; exact sum_congr rfl fun T _ => by ring

lemma bdry_finsum {H : Host V I} {F : Set (Multiset I)} {α : Type*} (s : Finset α)
    (g : α → Finset V → ℝ) (e : Sym2 V) :
    bdry H F (fun S => ∑ x ∈ s, g x S) e = ∑ x ∈ s, bdry H F (g x) e := by
  have := bdry_sum_smul (H := H) (F := F) s (fun _ => 1) g e
  simpa using this

lemma bdry_congr {H : Host V I} {F : Set (Multiset I)} {f g : Finset V → ℝ}
    (h : ∀ S, f S = g S) (e : Sym2 V) : bdry H F f e = bdry H F g e := by
  rw [show f = g from funext h]

/-- Borde de la indicatriz de una familia de triángulos permitidos. -/
lemma bdry_indSet {H : Host V I} {F : Set (Multiset I)} {X : Finset (Finset V)}
    (hX : ∀ Q ∈ X, IsAllowed H F Q) (e : Sym2 V) :
    bdry H F (fun S => if S ∈ X then 1 else 0) e = ∑ Q ∈ X, indR (triEdges Q) e := by
  unfold bdry
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext T
  simp only [mem_filter, allowed, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hX T h, h⟩⟩

/-! ### Datos del núcleo -/

/-- Datos de la construcción: pivotes `Piv f`, ápices intermedios `Cs u v a b` y familias de
bisagras `fam u v a c` (para el par `{u,v,a}`, `{u,v,c}`). -/
structure KData (V : Type*) where
  Piv : Sym2 V → Finset V
  Cs : V → V → V → V → Finset V
  fam : V → V → V → V → Finset (Finset (Sym2 V))

/-- `x = (u,v,a)` es un dato de toque de `T` con `B`: `T = {u,v,a}`, distintos, `uv ∈ B`. -/
def IsTouch (B : Finset (Sym2 V)) (T : Finset V) (x : V × V × V) : Prop :=
  T = {x.1, x.2.1, x.2.2} ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 ∧ s(x.1, x.2.1) ∈ B

/-- Núcleo de pivote global `p_f`. -/
def pivK (K : KData V) (f : Sym2 V) (S : Finset V) : ℝ :=
  avgOver (K.Piv f) (fun b => if S = insert b f.toFinset then 1 else 0)

/-- Triángulos del primer modo que tocan `B`. -/
def badQ (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (u v a c : V)
    (J : Finset (Sym2 V)) : Finset (Finset V) :=
  (hdec1 H F u v a c J).filter (fun Q => ¬ Disjoint (triEdges Q) B)

/-- Certificado de la primera bisagra con los triángulos que tocan `B` retirados. -/
def hcQ (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (u v a c : V)
    (J : Finset (Sym2 V)) (S : Finset V) : ℝ :=
  hingeCert H F u v a c J S - (if S ∈ badQ H F B u v a c J then 1 else 0)

/-- Certificado de dos niveles (sin la corrección): promedio sobre pivote `b`, ápice
intermedio `c` y bisagras `uva → uvc` (modo recortado) y `uvc → uvb`. -/
def Rfun (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V)
    (u v a : V) (S : Finset V) : ℝ :=
  avgOver (K.Piv s(u, v)) fun b => avgOver (K.Cs u v a b) fun c =>
    avgOver (K.fam u v a c) (fun J => hcQ H F B u v a c J S) +
      avgOver (K.fam u v c b) (fun J => hingeCert H F u v c b J S)

/-- Certificado de una arista de un triángulo `Q` (vía su dato de toque elegido). -/
def RQ (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V)
    (Q : Finset V) (S : Finset V) : ℝ :=
  if h : ∃ x, IsTouch B Q x then
    Rfun H F B K (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2 S
  else 0

/-- Corrección: sustitución de los triángulos retirados por sus certificados de una arista. -/
def corrK (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V)
    (u v a : V) (S : Finset V) : ℝ :=
  avgOver (K.Piv s(u, v)) fun b => avgOver (K.Cs u v a b) fun c =>
    avgOver (K.fam u v a c) fun J => ∑ Q ∈ badQ H F B u v a c J, RQ H F B K Q S

/-- **Certificado final** de un triángulo `T`: `δ_T` si `T` no toca `B`; si lo toca, el
certificado de dos niveles más la corrección. -/
def kcert (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V)
    (T : Finset V) (S : Finset V) : ℝ :=
  if h : ∃ x, IsTouch B T x then
    Rfun H F B K (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2 S +
      corrK H F B K (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2 S
  else if S = T then 1 else 0

/-- Hipótesis sobre los datos para el borde y el soporte. -/
structure KHyp (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V) :
    Prop where
  piv_ne : ∀ f ∈ B, (K.Piv f).Nonempty
  piv_ok : ∀ f ∈ B, ∀ b ∈ K.Piv f,
    IsAllowed H F (insert b f.toFinset) ∧ b ∉ f ∧ ∀ x ∈ f, s(x, b) ∉ B
  cs_ne : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    (K.Cs u v a b).Nonempty
  cs_ok : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, IsAllowed H F {u, v, c} ∧ c ≠ a ∧ c ≠ b ∧ s(u, c) ∉ B ∧ s(v, c) ∉ B
  fam1_ne : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, (K.fam u v a c).Nonempty
  fam1_ok : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, ∀ J ∈ K.fam u v a c, IsHinge H F u v a c J ∧ Disjoint J B
  fam2_ne : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, (K.fam u v c b).Nonempty
  fam2_ok : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, ∀ J ∈ K.fam u v c b, IsHinge H F u v c b J ∧ Disjoint J B

end TypedTriangle
