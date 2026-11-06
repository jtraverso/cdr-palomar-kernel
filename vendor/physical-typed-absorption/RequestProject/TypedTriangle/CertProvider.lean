/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertDispersion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 — Proveedor concreto de datos del núcleo desde (H4) y el grado triangular

Datos concretos:

* `Piv f = {b : f ∪ {b} permitido, b ∉ f, xb ∉ B para x ∈ f}` (pivotes GLOBALES, sólo
  dependen de la arista borrada `f`, nunca de la fuente `T`);
* `Cs u v a b = {c : uvc permitido, c ≠ a, b, y uc, vc, ac, cb ∉ B}` (ápice intermedio);
* `fam u v p q` = bisagras de `(uvp, uvq)` del orden `i` dado por (H4) que evitan `B`
  (ROBUSTAS: `robust_fresh_hinges`, al menos `(α/2) n^{i−4}` de ellas).

`provK_hyp_disp`: si cada arista está en al menos `n/κ₀` triángulos permitidos, se cumple
(H4) y el grado de `B` es `≤ d` con `10·2^{C(h,2)} d ≤ α n` y `8κ₀ d + 4κ₀ ≤ n`,
entonces los datos cumplen `KHyp` y `KDisp` con `β = α/2`, `κ = 2κ₀`. Las ventanas son
explícitas y no dependen del host, de `B` ni de la demanda.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Orden de bisagra escogido por (H4) para el par `(uva, uvc)`. -/
def ordH (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (hh : ℕ) (u v a c : V) : ℕ :=
  if h : ∃ i, 6 ≤ i ∧ i ≤ hh ∧
      α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a c i).card then Nat.find h
  else 6

lemma ordH_spec {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {hh : ℕ} {u v a c : V}
    (h : ∃ i, 6 ≤ i ∧ i ≤ hh ∧
      α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a c i).card) :
    6 ≤ ordH H F α hh u v a c ∧ ordH H F α hh u v a c ≤ hh ∧
      α * (Fintype.card V : ℝ) ^ (ordH H F α hh u v a c - 4) ≤
        (hinges H F u v a c (ordH H F α hh u v a c)).card := by
  unfold ordH; rw [dif_pos h]; exact Nat.find_spec h

/-- Datos concretos del núcleo. -/
def provK (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (α : ℝ) (hh : ℕ) :
    KData V where
  Piv f := univ.filter (fun b => IsAllowed H F (insert b f.toFinset) ∧ b ∉ f ∧
    ∀ x ∈ f, s(x, b) ∉ B)
  Cs u v a b := univ.filter (fun c => IsAllowed H F {u, v, c} ∧ c ≠ a ∧ c ≠ b ∧
    s(u, c) ∉ B ∧ s(v, c) ∉ B ∧ s(a, c) ∉ B ∧ s(c, b) ∉ B)
  fam u v p q := (hinges H F u v p q (ordH H F α hh u v p q)).filter (fun J => Disjoint J B)

omit [Fintype V] in
lemma mem_nbrIn_iff [Fintype V] {B : Finset (Sym2 V)} {x z : V} :
    z ∈ nbrIn B x ↔ s(x, z) ∈ B := by simp [nbrIn]

/-- Pivotes: pierden a lo sumo `2d` ápices. -/
lemma card_triOn_le_piv {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {α : ℝ}
    {hh d : ℕ} (hdeg : ∀ x, degIn B x ≤ d) {f : Sym2 V} (hf : ¬ f.IsDiag) :
    (triOn H F f).card ≤ ((provK H F B α hh).Piv f).card + 2 * d := by
  induction f using Sym2.ind with
  | _ x y =>
  set P := (provK H F B α hh).Piv s(x, y)
  have hsub : triOn H F s(x, y) ⊆ (P ∪ (nbrIn B x ∪ nbrIn B y)).image
      (fun w => insert w (s(x, y)).toFinset) := by
    intro T hT
    simp only [triOn, allowed, mem_filter, mem_univ, true_and] at hT
    obtain ⟨w, hw⟩ := eq_insert_of_mem_triEdges hT.1.1 hT.2
    rw [mem_image]
    refine ⟨w, ?_, hw.symm⟩
    have hwf : w ∉ s(x, y) := by
      intro hm
      have : T = (s(x, y)).toFinset := by
        rw [hw]; exact insert_eq_of_mem (Sym2.mem_toFinset.2 hm)
      have h3 := hT.1.1
      rw [this, Sym2.card_toFinset_of_not_isDiag _ hf] at h3
      omega
    by_cases hB : ∀ z ∈ s(x, y), s(z, w) ∉ B
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hw ▸ hT.1, hwf, hB⟩)
    · push_neg at hB
      obtain ⟨z, hz, hzB⟩ := hB
      apply mem_union_right
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact mem_union_left _ (mem_nbrIn_iff.2 hzB)
      · exact mem_union_right _ (mem_nbrIn_iff.2 hzB)
  calc (triOn H F s(x, y)).card ≤ (P ∪ (nbrIn B x ∪ nbrIn B y)).card :=
        (card_le_card hsub).trans card_image_le
    _ ≤ P.card + ((nbrIn B x).card + (nbrIn B y).card) :=
        (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    _ ≤ P.card + 2 * d := by
        have := (card_nbrIn_le B x).trans (hdeg x)
        have := (card_nbrIn_le B y).trans (hdeg y)
        omega

/-- Ápices intermedios: pierden a lo sumo `4d + 2`. -/
lemma card_triOn_le_cs {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {α : ℝ}
    {hh d : ℕ} (hdeg : ∀ x, degIn B x ≤ d) {u v a b : V} :
    (triOn H F s(u, v)).card ≤ ((provK H F B α hh).Cs u v a b).card + (4 * d + 2) := by
  set C := (provK H F B α hh).Cs u v a b
  set N := nbrIn B u ∪ nbrIn B v ∪ nbrIn B a ∪ nbrIn B b with hNdef
  have hsub : triOn H F s(u, v) ⊆ (C ∪ (N ∪ {a, b})).image
      (fun w => insert w (s(u, v)).toFinset) := by
    intro T hT
    simp only [triOn, allowed, mem_filter, mem_univ, true_and] at hT
    obtain ⟨w, hw⟩ := eq_insert_of_mem_triEdges hT.1.1 hT.2
    rw [mem_image]
    refine ⟨w, ?_, hw.symm⟩
    have hTw : IsAllowed H F {u, v, w} := by rw [tri_eq_insert_toFinset, ← hw]; exact hT.1
    by_cases hC : w ≠ a ∧ w ≠ b ∧ s(u, w) ∉ B ∧ s(v, w) ∉ B ∧ s(a, w) ∉ B ∧ s(w, b) ∉ B
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hTw, hC⟩)
    · apply mem_union_right
      simp only [not_and_or, not_not, ne_eq] at hC
      simp only [N, mem_union, mem_insert, mem_singleton, mem_nbrIn_iff]
      rcases hC with h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr (by rw [Sym2.eq_swap]; exact h))
  have hN : N.card ≤ 4 * d := by
    have h1 := (card_nbrIn_le B u).trans (hdeg u)
    have h2 := (card_nbrIn_le B v).trans (hdeg v)
    have h3 := (card_nbrIn_le B a).trans (hdeg a)
    have h4 := (card_nbrIn_le B b).trans (hdeg b)
    have := card_union_le (nbrIn B u ∪ nbrIn B v ∪ nbrIn B a) (nbrIn B b)
    have := card_union_le (nbrIn B u ∪ nbrIn B v) (nbrIn B a)
    have := card_union_le (nbrIn B u) (nbrIn B v)
    rw [hNdef]
    omega
  calc (triOn H F s(u, v)).card ≤ (C ∪ (N ∪ {a, b})).card :=
        (card_le_card hsub).trans card_image_le
    _ ≤ C.card + (N.card + ({a, b} : Finset V).card) :=
        (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    _ ≤ C.card + (4 * d + 2) := by have := card_le_two (a := a) (b := b); omega

/-- Familias robustas: no vacías y abundantes. -/
lemma provK_fam {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {α : ℝ}
    {hh d : ℕ} (hcond : HingeCond H F α hh) (hdeg : ∀ x, degIn B x ≤ d)
    (hd1 : 10 * 2 ^ Nat.choose hh 2 * (d : ℝ) ≤ α * Fintype.card V)
    (hn : 0 < (Fintype.card V : ℝ)) {u v p q : V} (hpq : p ≠ q)
    (hTp : IsAllowed H F {u, v, p}) (hTq : IsAllowed H F {u, v, q}) (hB : s(p, q) ∉ B) :
    ∃ i ≤ hh, (provK H F B α hh).fam u v p q ⊆ hinges H F u v p q i ∧
      α / 2 * (Fintype.card V : ℝ) ^ (i - 4) ≤ ((provK H F B α hh).fam u v p q).card := by
  set n := (Fintype.card V : ℝ)
  obtain ⟨h6, hle, hsup⟩ := ordH_spec (hcond u v p q hpq hTp hTq)
  set i := ordH H F α hh u v p q
  refine ⟨i, hle, filter_subset _ _, ?_⟩
  have hwin : ((((∅ : Finset V).card : ℝ)) + 5 * d) * n ^ (i - 5) * 2 ^ Nat.choose i 2 ≤
      α / 2 * n ^ (i - 4) := by
    have hM : (2 : ℝ) ^ Nat.choose i 2 ≤ 2 ^ Nat.choose hh 2 :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hle)
    have hpow : n ^ (i - 4) = n ^ (i - 5) * n := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow, card_empty, Nat.cast_zero, zero_add]
    have h5 : 0 ≤ n ^ (i - 5) := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    calc 5 * (d : ℝ) * n ^ (i - 5) * 2 ^ Nat.choose i 2
        ≤ 5 * d * n ^ (i - 5) * 2 ^ Nat.choose hh 2 := by gcongr
      _ = n ^ (i - 5) * (10 * 2 ^ Nat.choose hh 2 * d) / 2 := by ring
      _ ≤ n ^ (i - 5) * (α * n) / 2 := by gcongr
      _ = α / 2 * (n ^ (i - 5) * n) := by ring
  have hr := robust_fresh_hinges hpq hTp hTq i h6 α ∅ B d hdeg hB hsup hwin
  refine hr.trans (le_of_eq ?_)
  congr 2
  ext J
  simp [provK, i]

/-- **Proveedor concreto (P06).** Bajo las ventanas uniformes, los datos `provK` cumplen las
hipótesis de borde/soporte y de dispersión. -/
theorem provK_hyp_disp {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {α κ₀ : ℝ}
    (hα : 0 < α) (hκ₀ : 0 < κ₀) {hh d : ℕ} (hcond : HingeCond H F α hh)
    (htri : ∀ f ∈ edges H, (Fintype.card V : ℝ) ≤ κ₀ * (triOn H F f).card)
    (hB : B ⊆ edges H) (hdeg : ∀ x, degIn B x ≤ d)
    (hd1 : 10 * 2 ^ Nat.choose hh 2 * (d : ℝ) ≤ α * Fintype.card V)
    (hd2 : 8 * κ₀ * d + 4 * κ₀ ≤ Fintype.card V) :
    KHyp H F B (provK H F B α hh) ∧ KDisp H F B (provK H F B α hh) hh (α / 2) (2 * κ₀) := by
  set n := (Fintype.card V : ℝ)
  set K := provK H F B α hh
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hn : 0 < n := by nlinarith
  have hedge : ∀ {u v : V}, s(u, v) ∈ edges H → u ≠ v := by
    intro u v h huv
    subst huv
    simp only [edges, mem_filter, mem_univ, true_and] at h
    exact H.G.irrefl h
  -- tamaños
  have hpiv : ∀ f ∈ B, n ≤ 2 * κ₀ * (K.Piv f).card := by
    intro f hf
    have hfe := hB hf
    have hnd : ¬ f.IsDiag := by
      simp only [edges, mem_filter, mem_univ, true_and] at hfe
      exact H.G.not_isDiag_of_mem_edgeSet hfe
    have h1 := htri f hfe
    have h2 : ((triOn H F f).card : ℝ) ≤ (K.Piv f).card + 2 * d := by
      exact_mod_cast card_triOn_le_piv (α := α) (hh := hh) hdeg hnd
    nlinarith
  have hcs : ∀ u v a b, s(u, v) ∈ B → n ≤ 2 * κ₀ * (K.Cs u v a b).card := by
    intro u v a b huvB
    have hfe := hB huvB
    have h1 := htri _ hfe
    have h2 : ((triOn H F s(u, v)).card : ℝ) ≤ (K.Cs u v a b).card + (4 * d + 2) := by
      exact_mod_cast card_triOn_le_cs (α := α) (hh := hh) (u := u) (v := v) (a := a) (b := b) hdeg
    nlinarith
  have hpos : ∀ (s : Finset V), n ≤ 2 * κ₀ * s.card → s.Nonempty := by
    intro s hs
    rw [← card_pos]
    by_contra h0
    push_neg at h0
    have : s.card = 0 := by omega
    rw [this, Nat.cast_zero, mul_zero] at hs
    linarith
  have hfamne : ∀ {u v p q : V}, p ≠ q → IsAllowed H F {u, v, p} → IsAllowed H F {u, v, q} →
      s(p, q) ∉ B → (K.fam u v p q).Nonempty := by
    intro u v p q hpq hTp hTq hpqB
    obtain ⟨i, -, -, hsz⟩ := provK_fam hcond hdeg hd1 hn hpq hTp hTq hpqB
    rw [← card_pos]
    have : (0 : ℝ) < (K.fam u v p q).card :=
      lt_of_lt_of_le (mul_pos (by positivity) (pow_pos hn _)) hsz
    exact_mod_cast this
  have hTb : ∀ u v b, s(u, v) ∈ B → b ∈ K.Piv s(u, v) → IsAllowed H F {u, v, b} := by
    intro u v b _ hb
    rw [tri_eq_insert_toFinset]; exact (mem_filter.1 hb).2.1
  have hcsmem : ∀ {u v a b c : V}, c ∈ K.Cs u v a b → IsAllowed H F {u, v, c} ∧ c ≠ a ∧
      c ≠ b ∧ s(u, c) ∉ B ∧ s(v, c) ∉ B ∧ s(a, c) ∉ B ∧ s(c, b) ∉ B :=
    fun hc => (mem_filter.1 hc).2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hpiv, ?_, ?_, ?_⟩⟩
  · exact fun f hf => hpos _ (hpiv f hf)
  · exact fun f _ b hb => (mem_filter.1 hb).2
  · exact fun u v a huvB _ b _ => hpos _ (hcs u v a b huvB)
  · intro u v a _ _ b _ c hc
    obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hcsmem hc
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro u v a _ hTa b _ c hc
    obtain ⟨hTc, hca, -, -, -, hacB, -⟩ := hcsmem hc
    exact hfamne (Ne.symm hca) hTa hTc hacB
  · intro u v a _ _ b _ c _ J hJ
    have := (mem_filter.1 hJ)
    simp only [hinges, mem_filter, mem_univ, true_and] at this
    exact ⟨this.1.1, this.2⟩
  · intro u v a huvB _ b hb c hc
    obtain ⟨hTc, -, hcb, -, -, -, hcbB⟩ := hcsmem hc
    exact hfamne hcb hTc (hTb u v b huvB hb) hcbB
  · intro u v a _ _ b _ c _ J hJ
    have := (mem_filter.1 hJ)
    simp only [hinges, mem_filter, mem_univ, true_and] at this
    exact ⟨this.1.1, this.2⟩
  · exact fun u v a huvB _ b _ => hcs u v a b huvB
  · intro u v a _ hTa b _ c hc
    obtain ⟨hTc, hca, -, -, -, hacB, -⟩ := hcsmem hc
    exact provK_fam hcond hdeg hd1 hn (Ne.symm hca) hTa hTc hacB
  · intro u v a huvB _ b hb c hc
    obtain ⟨hTc, -, hcb, -, -, -, hcbB⟩ := hcsmem hc
    exact provK_fam hcond hdeg hd1 hn hcb hTc (hTb u v b huvB hb) hcbB

end TypedTriangle
