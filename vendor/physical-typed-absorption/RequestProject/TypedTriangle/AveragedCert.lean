/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SeedPositivity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# B2 (versión promediada) — certificados de transporte desde bisagras

Para un triángulo `T_a = {u,v,a}` que toca `B` sólo en `f = uv`, un conjunto de ápices
pivote `b ∈ 𝒫` (con `T_b = {u,v,b}` permitido) y, para cada `b`, una familia no vacía
`𝒥_b` de bisagras para `(T_a, T_b)`, se define el certificado PROMEDIADO

  `c̄(S) = (1/|𝒫|) Σ_b (1/|𝒥_b|) Σ_{J ∈ 𝒥_b} (1_{S ∈ D₁(J)} − 1_{S ∈ D₂(J)})`,

donde `D₁(J)`, `D₂(J)` son descomposiciones elegidas de `J ∪ W_a`, `J ∪ W_b`, y el pivote
promediado `p_f = (1/|𝒫|) Σ_b δ_{T_b}`. Se demuestra:

* `bdry_avgCert`: `∂c̄ = 1_{E(T_a)} − ∂p_f` (la ecuación de borde de B1, caso de una arista);
* `avgCert_support`: si las bisagras y las cuñas evitan `B`, el soporte de `c̄` está en
  triángulos permitidos del residual `E ∖ B`;
* `abs_avgCert_le`: `|c̄(S)| ≤ (1/|𝒫|) Σ_b #{J ∈ 𝒥_b : V(S) ⊆ V(J) ∪ R_b}/|𝒥_b|`,
  la cota que alimenta la cuenta de dispersión.

El promedio sobre TODA la familia reemplaza al muestreo aleatorio de S05 (el valor
esperado de la construcción aleatoria es exactamente este promedio).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma indR_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (e : Sym2 V) :
    indR (A ∪ B) e = indR A e + indR B e := by
  unfold indR
  by_cases hA : e ∈ A
  · have hB : e ∉ B := Finset.disjoint_left.1 h hA
    simp [hA, hB]
  · by_cases hB : e ∈ B <;> simp [hA, hB]

/-- Borde de una combinación finita. -/
lemma bdry_sum_smul {H : Host V I} {F : Set (Multiset I)} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (g : ι → Finset V → ℝ) (e : Sym2 V) :
    bdry H F (fun S => ∑ i ∈ s, c i * g i S) e = ∑ i ∈ s, c i * bdry H F (g i) e := by
  unfold bdry
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => by ring

lemma bdry_sub' {H : Host V I} {F : Set (Multiset I)} (f g : Finset V → ℝ) (e : Sym2 V) :
    bdry H F (fun S => f S - g S) e = bdry H F f e - bdry H F g e := by
  unfold bdry
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => by ring

/-- Borde del indicador de una descomposición. -/
lemma bdry_indDec {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F J D) (e : Sym2 V) :
    bdry H F (fun S => if S ∈ D then 1 else 0) e = indR J e := by
  unfold bdry
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : (allowed H F).filter (fun T => T ∈ D) = D := by
    ext T
    simp only [Finset.mem_filter, allowed, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hD.1 T h, h⟩⟩
  rw [this, sum_indR_of_isDecomposition hD e]

/-- Borde de una delta en un triángulo permitido. -/
lemma bdry_delta {H : Host V I} {F : Set (Multiset I)} {T : Finset V} (hT : IsAllowed H F T)
    (e : Sym2 V) : bdry H F (fun S => if S = T then 1 else 0) e = indR (triEdges T) e := by
  unfold bdry
  rw [Finset.sum_eq_single T]
  · simp
  · intro S _ hS; simp [hS]
  · intro h; exact absurd (by simpa [allowed] using hT) h

/-- Primera descomposición elegida de una bisagra (`J ∪ W_a`). -/
def hdec1 (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (J : Finset (Sym2 V)) :
    Finset (Finset V) :=
  if h : IsHinge H F u v a b J then Classical.choose h.2.2.1 else ∅

/-- Segunda descomposición elegida de una bisagra (`J ∪ W_b`). -/
def hdec2 (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (J : Finset (Sym2 V)) :
    Finset (Finset V) :=
  if h : IsHinge H F u v a b J then Classical.choose h.2.2.2 else ∅

lemma hdec1_spec {H : Host V I} {F : Set (Multiset I)} {u v a b : V} {J : Finset (Sym2 V)}
    (hJ : IsHinge H F u v a b J) : IsDecomposition H F (J ∪ wedge u v a) (hdec1 H F u v a b J) := by
  unfold hdec1; rw [dif_pos hJ]; exact Classical.choose_spec hJ.2.2.1

lemma hdec2_spec {H : Host V I} {F : Set (Multiset I)} {u v a b : V} {J : Finset (Sym2 V)}
    (hJ : IsHinge H F u v a b J) : IsDecomposition H F (J ∪ wedge u v b) (hdec2 H F u v a b J) := by
  unfold hdec2; rw [dif_pos hJ]; exact Classical.choose_spec hJ.2.2.2

/-- Certificado entero de una bisagra: diferencia de sus dos modos. -/
def hingeCert (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (J : Finset (Sym2 V))
    (S : Finset V) : ℝ :=
  (if S ∈ hdec1 H F u v a b J then 1 else 0) - (if S ∈ hdec2 H F u v a b J then 1 else 0)

omit [Fintype V] in
lemma wedge_subset_triEdges {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    wedge u v a ⊆ triEdges ({u, v, a} : Finset V) := by
  rw [triEdges_eq_insert_wedge huv hua hva]; exact Finset.subset_insert _ _

/-- **Borde del certificado de una bisagra:** `∂c_J = 1_{E(T_a)} − 1_{E(T_b)}`. -/
theorem bdry_hingeCert {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) (hTa : IsAllowed H F {u, v, a})
    (hTb : IsAllowed H F {u, v, b}) (e : Sym2 V) :
    bdry H F (hingeCert H F u v a b J) e =
      indR (triEdges ({u, v, a} : Finset V)) e - indR (triEdges ({u, v, b} : Finset V)) e := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  have hdisj := hJ.2.1
  have hJa : Disjoint J (wedge u v a) := Finset.disjoint_of_subset_right
    ((wedge_subset_triEdges huv hua hva).trans Finset.subset_union_left) hdisj
  have hJb : Disjoint J (wedge u v b) := Finset.disjoint_of_subset_right
    ((wedge_subset_triEdges huv hub hvb).trans Finset.subset_union_right) hdisj
  unfold hingeCert
  rw [bdry_sub', bdry_indDec (hdec1_spec hJ), bdry_indDec (hdec2_spec hJ),
    indR_union_of_disjoint hJa, indR_union_of_disjoint hJb,
    triEdges_eq_insert_wedge huv hua hva, triEdges_eq_insert_wedge huv hub hvb,
    Finset.insert_eq, Finset.insert_eq,
    indR_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge huv hua hva)),
    indR_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge huv hub hvb))]
  ring

/-- Certificado promediado sobre pivotes y bisagras. -/
def avgCert (H : Host V I) (F : Set (Multiset I)) (u v a : V) (Pv : Finset V)
    (fam : V → Finset (Finset (Sym2 V))) (S : Finset V) : ℝ :=
  ∑ b ∈ Pv, (1 / Pv.card) * ∑ J ∈ fam b, (1 / (fam b).card) * hingeCert H F u v a b J S

/-- Pivote promediado `p_f = (1/|𝒫|) Σ_b δ_{T_b}`. -/
def pivotAvg (u v : V) (Pv : Finset V) (S : Finset V) : ℝ :=
  ∑ b ∈ Pv, (1 / Pv.card) * (if S = {u, v, b} then 1 else 0)

/-- **Ecuación de borde del certificado promediado (B2, una arista).** -/
theorem bdry_avgCert {H : Host V I} {F : Set (Multiset I)} {u v a : V} {Pv : Finset V}
    {fam : V → Finset (Finset (Sym2 V))} (hPv : Pv.Nonempty)
    (hTa : IsAllowed H F {u, v, a}) (hTb : ∀ b ∈ Pv, IsAllowed H F {u, v, b})
    (hfam : ∀ b ∈ Pv, (fam b).Nonempty) (hJ : ∀ b ∈ Pv, ∀ J ∈ fam b, IsHinge H F u v a b J)
    (e : Sym2 V) :
    bdry H F (avgCert H F u v a Pv fam) e =
      indR (triEdges ({u, v, a} : Finset V)) e - bdry H F (pivotAvg u v Pv) e := by
  have hP0 : (Pv.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hPv).ne'
  unfold avgCert pivotAvg
  rw [bdry_sum_smul, bdry_sum_smul]
  have h1 : ∀ b ∈ Pv, bdry H F (fun S => ∑ J ∈ fam b, (1 / (fam b).card) *
      hingeCert H F u v a b J S) e =
      indR (triEdges ({u, v, a} : Finset V)) e - indR (triEdges ({u, v, b} : Finset V)) e := by
    intro b hb
    have hf0 : ((fam b).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 (hfam b hb)).ne'
    rw [bdry_sum_smul]
    rw [Finset.sum_congr rfl fun J hJ' => by rw [bdry_hingeCert (hJ b hb J hJ') hTa (hTb b hb)]]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl fun b hb => by rw [h1 b hb]]
  have h2 : ∑ i ∈ Pv, 1 / (Pv.card : ℝ) * bdry H F (fun S => if S = {u, v, i} then 1 else 0) e =
      ∑ i ∈ Pv, 1 / (Pv.card : ℝ) * indR (triEdges ({u, v, i} : Finset V)) e :=
    Finset.sum_congr rfl fun b hb => by rw [bdry_delta (hTb b hb)]
  rw [h2, Finset.sum_congr rfl (fun b _ => mul_sub _ _ _), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [Fintype V] in
/-- Un triángulo permitido cuyas aristas están en `K` es permitido en `subHost H K`. -/
lemma isAllowed_subHost_of {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {S : Finset V} (hS : IsAllowed H F S) (hK : triEdges S ⊆ K) : IsAllowed (subHost H K) F S := by
  refine ⟨hS.1, fun x hx y hy hxy => ?_, hS.2.2⟩
  simp only [subHost, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨hK ((mem_triEdges).2 ⟨hx, hy, hxy⟩), hxy⟩, hS.2.1 x hx y hy hxy⟩

lemma hingeCert_ne_zero {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} {S : Finset V} (h : hingeCert H F u v a b J S ≠ 0) :
    S ∈ hdec1 H F u v a b J ∨ S ∈ hdec2 H F u v a b J := by
  unfold hingeCert at h
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2] at h

/-- **Soporte residual del certificado promediado.** -/
theorem avgCert_support {H : Host V I} {F : Set (Multiset I)} {u v a : V} {Pv : Finset V}
    {fam : V → Finset (Finset (Sym2 V))} {B : Finset (Sym2 V)}
    (hJ : ∀ b ∈ Pv, ∀ J ∈ fam b, IsHinge H F u v a b J)
    (hJB : ∀ b ∈ Pv, ∀ J ∈ fam b, Disjoint J B)
    (hWa : Disjoint (wedge u v a) B) (hWb : ∀ b ∈ Pv, Disjoint (wedge u v b) B)
    {S : Finset V} (hS : avgCert H F u v a Pv fam S ≠ 0) :
    IsAllowed (residual H B) F S := by
  obtain ⟨b, hb, hbS⟩ : ∃ b ∈ Pv, ∃ J ∈ fam b, hingeCert H F u v a b J S ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hS
    unfold avgCert
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.sum_eq_zero fun J hJ' => by rw [hc b hb J hJ', mul_zero], mul_zero]
  obtain ⟨J, hJm, hne⟩ := hbS
  have hH := hJ b hb J hJm
  have key : ∀ (W : Finset (Sym2 V)) (D : Finset (Finset V)), IsDecomposition H F (J ∪ W) D →
      Disjoint W B → S ∈ D → IsAllowed (residual H B) F S := by
    intro W D hD hW hSD
    have hSA := hD.1 S hSD
    refine isAllowed_subHost_of hSA fun e he => ?_
    have heJW := hD.subset hSD he
    rw [Finset.mem_sdiff]
    refine ⟨triEdges_subset_edges hSA he, fun heB => ?_⟩
    rcases Finset.mem_union.1 heJW with h | h
    · exact Finset.disjoint_left.1 (hJB b hb J hJm) h heB
    · exact Finset.disjoint_left.1 hW h heB
  rcases hingeCert_ne_zero hne with h | h
  · exact key _ _ (hdec1_spec hH) hWa h
  · exact key _ _ (hdec2_spec hH) (hWb b hb) h

omit [Fintype V] in
/-- Vértices de un triángulo de una descomposición de `J ∪ W_t`: en `V(J) ∪ {u,v,t}`. -/
lemma subset_support_of_mem_dec {H : Host V I} {F : Set (Multiset I)} [Fintype V]
    {J : Finset (Sym2 V)} {u v t : V} {D : Finset (Finset V)}
    (hD : IsDecomposition H F (J ∪ wedge u v t) D) {S : Finset V} (hS : S ∈ D) :
    S ⊆ support J ∪ {u, v, t} := by
  intro x hx
  have hS3 := (hD.1 S hS).1
  obtain ⟨y, hyS, hyx⟩ : ∃ y ∈ S, y ≠ x := by
    by_contra hc
    push_neg at hc
    have : S ⊆ {x} := fun z hz => Finset.mem_singleton.2 (hc z hz)
    have := Finset.card_le_card this
    simp at this; omega
  have he : s(x, y) ∈ J ∪ wedge u v t := hD.subset hS (mem_triEdges.2 ⟨hx, hyS, hyx.symm⟩)
  rcases Finset.mem_union.1 he with h | h
  · exact Finset.mem_union_left _ (by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨_, h, Sym2.mem_mk_left x y⟩)
  · apply Finset.mem_union_right
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) | (⟨h1, -⟩ | ⟨h1, -⟩) <;>
      first | exact Or.inl h1 | exact Or.inr (Or.inl h1) | exact Or.inr (Or.inr h1)

lemma abs_hingeCert_le {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) (S : Finset V) :
    |hingeCert H F u v a b J S| ≤
      if S ⊆ support J ∪ {u, v, a, b} then 1 else 0 := by
  by_cases h0 : hingeCert H F u v a b J S = 0
  · rw [h0, abs_zero]; split_ifs <;> norm_num
  · have hsub : S ⊆ support J ∪ {u, v, a, b} := by
      rcases hingeCert_ne_zero h0 with h | h
      · refine (subset_support_of_mem_dec (hdec1_spec hJ) h).trans ?_
        intro x hx; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      · refine (subset_support_of_mem_dec (hdec2_spec hJ) h).trans ?_
        intro x hx; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
    rw [if_pos hsub]
    unfold hingeCert
    split_ifs <;> norm_num

/-- **Cota puntual del certificado promediado.** -/
theorem abs_avgCert_le {H : Host V I} {F : Set (Multiset I)} {u v a : V} {Pv : Finset V}
    {fam : V → Finset (Finset (Sym2 V))} (hJ : ∀ b ∈ Pv, ∀ J ∈ fam b, IsHinge H F u v a b J)
    (S : Finset V) :
    |avgCert H F u v a Pv fam S| ≤ ∑ b ∈ Pv, (1 / (Pv.card : ℝ)) * ((1 / ((fam b).card : ℝ)) *
      (((fam b).filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ)) := by
  unfold avgCert
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ J ∈ fam b, |1 / ((fam b).card : ℝ) * hingeCert H F u v a b J S| ≤
      1 / ((fam b).card : ℝ) * (if S ⊆ support J ∪ {u, v, a, b} then 1 else 0) := by
    intro J hJ'
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_hingeCert_le (hJ b hb J hJ') S) (by positivity)
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- **Cuenta de bisagras que contienen un triángulo.** Para bisagras de orden `i` con raíces
`R = {u,v,a,b}` (`a ≠ b`), el número de las que cubren `S` (`S ⊆ V(J) ∪ R`) es
`≤ 2^{C(i,2)} n^{i−4} (1/n)^{|S ∖ R|}`. -/
theorem hinges_cover_count {H : Host V I} {F : Set (Multiset I)} {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (i : ℕ) (S : Finset V)
    (hn : 1 ≤ (Fintype.card V : ℝ)) :
    (((hinges H F u v a b i).filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ) ≤
      2 ^ Nat.choose i 2 * (Fintype.card V : ℝ) ^ (i - 4) *
        (1 / (Fintype.card V : ℝ)) ^ (S \ {u, v, a, b}).card := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  set R : Finset V := {u, v, a, b}
  have hR : R.card = 4 := roots_card huv hua hva hub hvb hab
  set s := (S \ R).card
  set n := (Fintype.card V : ℝ)
  have hRS : (R ∪ S).card = 4 + s := by
    rw [← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint Finset.disjoint_sdiff, hR]
  have hsub : (hinges H F u v a b i).filter (fun J => S ⊆ support J ∪ R) ⊆
      (hinges H F u v a b i).filter (fun J => R ∪ S ⊆ support J) := by
    intro J hJ
    simp only [Finset.mem_filter, hinges, Finset.mem_univ, true_and] at hJ ⊢
    refine ⟨hJ.1, Finset.union_subset (hinge_order_ge_six hab hTa hTb hJ.1.1).1 ?_⟩
    intro x hx
    rcases Finset.mem_union.1 (hJ.2 hx) with h | h
    · exact h
    · exact (hinge_order_ge_six hab hTa hTb hJ.1.1).1 h
  have hpos : 0 ≤ 2 ^ Nat.choose i 2 * n ^ (i - 4) * (1 / n) ^ s := by positivity
  by_cases hi : 4 + s ≤ i
  · have h1 := hinges_rooted_le (H := H) (F := F) (u := u) (v := v) (a := a) (b := b) i (R ∪ S)
      (by rw [hRS]; exact hi)
    rw [hRS] at h1
    have h2 : ((((hinges H F u v a b i).filter (fun J => S ⊆ support J ∪ R)).card : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ) ^ (i - (4 + s)) * 2 ^ Nat.choose i 2 := by
      exact_mod_cast (Finset.card_le_card hsub).trans h1
    refine h2.trans (le_of_eq ?_)
    have hn0 : n ≠ 0 := by positivity
    have : i - 4 = (i - (4 + s)) + s := by omega
    rw [this, pow_add, one_div_pow]
    field_simp
    rfl
  · have : (hinges H F u v a b i).filter (fun J => S ⊆ support J ∪ R) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro J hJ
      have hJ' := hsub hJ
      simp only [Finset.mem_filter, hinges, Finset.mem_univ, true_and] at hJ'
      have := Finset.card_le_card hJ'.2
      rw [hRS, hJ'.1.2] at this
      exact hi this
    rw [this, Finset.card_empty, Nat.cast_zero]; exact hpos

/-- **Dispersión del certificado promediado (B2).** Si cada familia `𝒥_b` está formada por
bisagras de orden `i_b ≤ h` y tiene al menos `β n^{i_b − 4}` elementos, entonces para cada
triángulo `S` (de tres vértices)

  `|c̄(S)| ≤ (2^{C(h,2)}/β) (1 + 3n/|𝒫|) (1/n)^{3 − |S ∩ T_a|}`.

Con `|𝒫| ≥ n/C'` el factor es una constante: es la hipótesis `hL` de `seed_perturbation`
con `t = 1/n`. -/
theorem avgCert_dispersion {H : Host V I} {F : Set (Multiset I)} {u v a : V} {Pv : Finset V}
    {fam : V → Finset (Finset (Sym2 V))} {ib : V → ℕ} {h : ℕ} {β : ℝ} (hβ : 0 < β)
    (hTa : IsAllowed H F {u, v, a}) (hPv : Pv.Nonempty)
    (hTb : ∀ b ∈ Pv, IsAllowed H F {u, v, b}) (hba : ∀ b ∈ Pv, b ≠ a)
    (hfam : ∀ b ∈ Pv, fam b ⊆ hinges H F u v a b (ib b))
    (hsize : ∀ b ∈ Pv, β * (Fintype.card V : ℝ) ^ (ib b - 4) ≤ (fam b).card)
    (hih : ∀ b ∈ Pv, ib b ≤ h) (hn : 1 ≤ (Fintype.card V : ℝ)) {S : Finset V}
    (hS3 : S.card = 3) :
    |avgCert H F u v a Pv fam S| ≤ 2 ^ Nat.choose h 2 / β *
      (1 + 3 * Fintype.card V / Pv.card) * ptw S (1 / Fintype.card V) {u, v, a} := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  set n := (Fintype.card V : ℝ)
  set T : Finset V := {u, v, a}
  set s := (S \ T).card
  set M : ℝ := 2 ^ Nat.choose h 2
  have hn0 : 0 < n := by linarith
  have hP0 : (0 : ℝ) < Pv.card := by exact_mod_cast Finset.card_pos.2 hPv
  have hJ : ∀ b ∈ Pv, ∀ J ∈ fam b, IsHinge H F u v a b J := fun b hb J hJ' => by
    have := hfam b hb hJ'
    simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1
  have hptw : ptw S (1 / n) T = (1 / n) ^ s := by
    unfold ptw; congr 1
    have := Finset.card_sdiff_add_card_inter S T
    omega
  -- cota por pivote
  have hper : ∀ b ∈ Pv, (1 / ((fam b).card : ℝ)) *
      (((fam b).filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ) ≤
      M / β * (1 / n) ^ (S \ {u, v, a, b}).card := by
    intro b hb
    have hfpos : 0 < ((fam b).card : ℝ) :=
      lt_of_lt_of_le (by positivity) (hsize b hb)
    have hc := hinges_cover_count (hba b hb).symm hTa (hTb b hb) (ib b) S hn
    have hsub : (fam b).filter (fun J => S ⊆ support J ∪ {u, v, a, b}) ⊆
        (hinges H F u v a b (ib b)).filter (fun J => S ⊆ support J ∪ {u, v, a, b}) :=
      Finset.filter_subset_filter _ (hfam b hb)
    have hc' : (((fam b).filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ) ≤
        2 ^ Nat.choose (ib b) 2 * n ^ (ib b - 4) * (1 / n) ^ (S \ {u, v, a, b}).card :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) hc
    have hM : (2 : ℝ) ^ Nat.choose (ib b) 2 ≤ M :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (hih b hb))
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfpos]
    have hq : 0 ≤ (1 / n) ^ (S \ {u, v, a, b}).card := by positivity
    calc _ ≤ 2 ^ Nat.choose (ib b) 2 * n ^ (ib b - 4) * (1 / n) ^ (S \ {u, v, a, b}).card := hc'
      _ ≤ M * n ^ (ib b - 4) * (1 / n) ^ (S \ {u, v, a, b}).card := by gcongr
      _ = M / β * (1 / n) ^ (S \ {u, v, a, b}).card * (β * n ^ (ib b - 4)) := by
          field_simp
      _ ≤ M / β * (1 / n) ^ (S \ {u, v, a, b}).card * (fam b).card := by
          gcongr; exact hsize b hb
  -- exponentes
  have hexp : ∀ b ∈ Pv, (1 / n) ^ (S \ {u, v, a, b}).card ≤
      (1 / n) ^ s + (if b ∈ S then n * (1 / n) ^ s else 0) := by
    intro b hb
    have hRT : ({u, v, a, b} : Finset V) = insert b T := by
      ext x; simp only [T, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hRT]
    by_cases hbS : b ∈ S
    · have hbT : b ∉ T := by
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl | rfl)
        · exact (distinct_of_card_three (hTb b hb).1).2.1 rfl
        · exact (distinct_of_card_three (hTb b hb).1).2.2 rfl
        · exact hba b hb rfl
      have hbST : b ∈ S \ T := Finset.mem_sdiff.2 ⟨hbS, hbT⟩
      have hc : (S \ insert b T).card + 1 = s := by
        have : S \ insert b T = (S \ T).erase b := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        rw [this, Finset.card_erase_of_mem hbST]
        have : 0 < s := Finset.card_pos.2 ⟨b, hbST⟩
        omega
      rw [if_pos hbS, ← hc, pow_succ]
      have : (1 / n) ^ (S \ insert b T).card * (1 / n) * n = (1 / n) ^ (S \ insert b T).card := by
        field_simp
      have h0 : 0 ≤ (1 / n) ^ (S \ insert b T).card * (1 / n) := by positivity
      nlinarith
    · have : S \ insert b T = S \ T := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim (fun h' => hbS (h' ▸ h1)) h2⟩
      rw [if_neg hbS, this, add_zero]
  have hcntS : ((Pv.filter (fun b => b ∈ S)).card : ℝ) ≤ 3 := by
    have := Finset.card_le_card (show Pv.filter (fun b => b ∈ S) ⊆ S from fun b hb =>
      (Finset.mem_filter.1 hb).2)
    rw [hS3] at this; exact_mod_cast this
  calc |avgCert H F u v a Pv fam S|
      ≤ ∑ b ∈ Pv, (1 / (Pv.card : ℝ)) * ((1 / ((fam b).card : ℝ)) *
        (((fam b).filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ)) := abs_avgCert_le hJ S
    _ ≤ ∑ b ∈ Pv, (1 / (Pv.card : ℝ)) * (M / β * ((1 / n) ^ s +
          (if b ∈ S then n * (1 / n) ^ s else 0))) := by
        refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (hper b hb).trans (mul_le_mul_of_nonneg_left (hexp b hb) (by positivity))
    _ = M / β * (1 / (Pv.card : ℝ)) * (Pv.card * (1 / n) ^ s +
          (Pv.filter (fun b => b ∈ S)).card * (n * (1 / n) ^ s)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ M / β * (1 / (Pv.card : ℝ)) * (Pv.card * (1 / n) ^ s + 3 * (n * (1 / n) ^ s)) := by
        gcongr
    _ = M / β * (1 + 3 * n / Pv.card) * ptw S (1 / n) T := by
        rw [hptw]; field_simp

end TypedTriangle
