/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RobustHinge

@[expose] public section

/-!
# A2 — Puente de dos bisagras (bisagra compuesta robusta)

Para `T_a = uva`, `T_b = uvb` se elige un ápice `t` y bisagras `H₁ : uva → uvt`,
`H₂ : uvt → uvb`; `Hcomp = H₁ ∪ W_t ∪ H₂` es una bisagra para `(T_a, T_b)` que evita un
grafo prohibido `B` (de grado acotado) y las seis parejas entre `u, v, a, b`, aunque `ab`
esté en `B`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma support_union (J K : Finset (Sym2 V)) : support (J ∪ K) = support J ∪ support K := by
  ext x
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

lemma support_wedge (u v t : V) : support (wedge u v t) = {u, v, t} := by
  ext x
  simp only [support, wedge, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, Sym2.mem_iff]
  tauto

lemma not_mem_of_not_mem_support {J : Finset (Sym2 V)} {x y : V} (hx : x ∉ support J) :
    s(x, y) ∉ J := fun h => hx (mem_support_of_mem h (by simp))

lemma not_mem_of_not_mem_support' {J : Finset (Sym2 V)} {x y : V} (hy : y ∉ support J) :
    s(x, y) ∉ J := fun h => hy (mem_support_of_mem h (by simp))

omit [Fintype V] in
lemma wedge_disjoint {u v a t : V} (hut : u ≠ t) (hvt : v ≠ t) (hat : a ≠ t) : Disjoint (wedge u v a) (wedge u v t) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with h | h <;> simp only [Sym2.eq_iff] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first | exact hat h2 | exact hut h1 | exact hvt h1

omit [Fintype V] in
lemma mem3_of {u v a b x : V} (hx : x ∈ ({u, v, b} : Finset V)) (hxb : x ≠ b) :
    x ∈ ({u, v, a} : Finset V) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with h | h | h
  exacts [Or.inl h, Or.inr (Or.inl h), absurd h hxb]

omit [Fintype V] in
lemma mem3_of' {u v a t x : V} (hx : x ∈ ({u, v, a} : Finset V)) (hxa : x ≠ a) :
    x ∈ ({u, v, t} : Finset V) := mem3_of hx hxa

/-- **Combinador A2.** Si `H₁` es bisagra para `(uva, uvt)` que no toca `b`, `H₂` es bisagra
para `(uvt, uvb)` que no toca `a`, y sus soportes sólo comparten vértices de `{u,v,t}`,
entonces `H₁ ∪ W_t ∪ H₂` es bisagra para `(uva, uvb)`, no contiene `ab` y su soporte es la
unión de ambos soportes. -/
theorem composite_hinge_of {H : Host V I} {F : Set (Multiset I)} {u v a b t : V}
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b})
    (hTt : IsAllowed H F {u, v, t}) (hat : a ≠ t) (hbt : b ≠ t)
    {H₁ H₂ : Finset (Sym2 V)} (h₁ : IsHinge H F u v a t H₁) (h₁b : b ∉ support H₁)
    (h₂ : IsHinge H F u v t b H₂) (h₂a : a ∉ support H₂)
    (h₁₂ : ∀ x ∈ support H₁, x ∈ support H₂ → x ∈ ({u, v, t} : Finset V)) :
    IsHinge H F u v a b (H₁ ∪ wedge u v t ∪ H₂) ∧ s(a, b) ∉ H₁ ∪ wedge u v t ∪ H₂ ∧
      support (H₁ ∪ wedge u v t ∪ H₂) = support H₁ ∪ support H₂ := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  obtain ⟨-, hut, hvt⟩ := distinct_of_card_three hTt.1
  have hT1 := h₁.isTransformer huv hua hva hut hvt
  have hT2 := h₂.isTransformer huv hut hvt hub hvb
  -- `u, v, t` están en el soporte de `H₁`
  have hR1 := (hinge_order_ge_six hat hTa hTt h₁).1
  have hu1 : u ∈ support H₁ := hR1 (by simp)
  have hv1 : v ∈ support H₁ := hR1 (by simp)
  have ht1 : t ∈ support H₁ := hR1 (by simp)
  have ha1 : a ∈ support H₁ := hR1 (by simp)
  -- disjunciones
  have h12 : Disjoint H₁ H₂ := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    induction e using Sym2.ind with
    | _ x y =>
    have hx := h₁₂ x (mem_support_of_mem he1 (by simp)) (mem_support_of_mem he2 (by simp))
    have hy := h₁₂ y (mem_support_of_mem he1 (by simp)) (mem_support_of_mem he2 (by simp))
    have hxy : x ≠ y := fun h => h₁.not_isDiag _ he1 (by simp [h])
    exact Finset.disjoint_left.1 h₁.2.1 he1
      (Finset.mem_union_right _ (mem_triEdges.2 ⟨hx, hy, hxy⟩))
  have h1Wb : Disjoint H₁ (wedge u v b) := by
    simp only [wedge, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨not_mem_of_not_mem_support' h₁b, not_mem_of_not_mem_support' h₁b⟩
  have h2Wa : Disjoint H₂ (wedge u v a) := by
    simp only [wedge, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨not_mem_of_not_mem_support' h₂a, not_mem_of_not_mem_support' h₂a⟩
  have hWaWt := wedge_disjoint hut hvt hat
  have hWtWb := wedge_disjoint hub hvb hbt.symm
  have hcomp := hT1.compose hT2 h12 h1Wb h2Wa hWaWt hWtWb
  have hsupp : support (H₁ ∪ wedge u v t ∪ H₂) = support H₁ ∪ support H₂ := by
    rw [support_union, support_union, support_wedge]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((h | h | h | h) | h)
      · exact Or.inl h
      · exact Or.inl (h ▸ hu1)
      · exact Or.inl (h ▸ hv1)
      · exact Or.inl (h ▸ ht1)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have hWt_edges : wedge u v t ⊆ edges H := by
    intro e he
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl
    · exact hTt.2.1 u (by simp) t (by simp) hut
    · exact hTt.2.1 v (by simp) t (by simp) hvt
  have hab_not : s(a, b) ∉ H₁ ∪ wedge u v t ∪ H₂ := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨not_mem_of_not_mem_support' h₁b, ?_⟩, not_mem_of_not_mem_support h₂a⟩
    intro h
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at h
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hbt h2
    · exact hat h1
    · exact hbt h2
    · exact hat h1
  refine ⟨⟨?_, ?_, hcomp.2.2.1, hcomp.2.2.2⟩, hab_not, hsupp⟩
  · exact Finset.union_subset (Finset.union_subset h₁.1 hWt_edges) h₂.1
  · rw [Finset.disjoint_left]
    intro e he hT
    rw [Finset.mem_union] at hT
    -- toda arista de `E(T_a) ∪ E(T_b)` distinta de `ab` tiene ambos extremos en `{u,v,a,b}`
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := by
      rcases hT with hT | hT <;> exact (mem_triEdges.1 hT).2.2
    simp only [Finset.mem_union] at he
    rcases he with (he | he) | he
    · -- `H₁`: disjunto de `E(uva)`, y no toca `b`
      rcases hT with hT | hT
      · exact Finset.disjoint_left.1 h₁.2.1 he (Finset.mem_union_left _ hT)
      · obtain ⟨hx, hy, -⟩ := mem_triEdges.1 hT
        have hxb : x ≠ b := fun h => h₁b (h ▸ mem_support_of_mem he (by simp))
        have hyb : y ≠ b := fun h => h₁b (h ▸ mem_support_of_mem he (by simp))
        have : s(x, y) ∈ triEdges ({u, v, a} : Finset V) := by
          rw [mem_triEdges]
          exact ⟨mem3_of hx hxb, mem3_of hy hyb, hxy⟩
        exact Finset.disjoint_left.1 h₁.2.1 he (Finset.mem_union_left _ this)
    · have ht : x = t ∨ y = t := by
        simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at he
        tauto
      have htT : t ∈ ({u, v, a} : Finset V) ∨ t ∈ ({u, v, b} : Finset V) := by
        rcases hT with hT | hT <;> obtain ⟨hx, hy, -⟩ := mem_triEdges.1 hT <;>
          rcases ht with h | h
        exacts [Or.inl (h ▸ hx), Or.inl (h ▸ hy), Or.inr (h ▸ hx), Or.inr (h ▸ hy)]
      simp only [Finset.mem_insert, Finset.mem_singleton] at htT
      rcases htT with (h | h | h) | (h | h | h)
      exacts [hut h.symm, hvt h.symm, hat h.symm, hut h.symm, hvt h.symm, hbt h.symm]
    · rcases hT with hT | hT
      · obtain ⟨hx, hy, -⟩ := mem_triEdges.1 hT
        have hxa : x ≠ a := fun h => h₂a (h ▸ mem_support_of_mem he (by simp))
        have hya : y ≠ a := fun h => h₂a (h ▸ mem_support_of_mem he (by simp))
        have : s(x, y) ∈ triEdges ({u, v, t} : Finset V) := by
          rw [mem_triEdges]
          exact ⟨mem3_of' hx hxa, mem3_of' hy hya, hxy⟩
        exact Finset.disjoint_left.1 h₂.2.1 he (Finset.mem_union_left _ this)
      · exact Finset.disjoint_left.1 h₂.2.1 he (Finset.mem_union_right _ hT)

/-- **Bisagra robusta desde (H4).** Con `(|Z| + 5d) 2^{C(h,2)} ≤ (α/2) n`, existe una bisagra
de orden `i ∈ [6,h]` que evita `Z` fuera de las raíces y es disjunta de `B`
(grado `≤ d`, `ab ∉ B`). -/
theorem exists_robust_hinge {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH4 : HingeCond H F α h) {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (hB : s(a, b) ∉ B)
    (hwin : ((Z.card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ i, 6 ≤ i ∧ i ≤ h ∧ ∃ J ∈ hinges H F u v a b i,
      (∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) ∧ Disjoint J B := by
  obtain ⟨i, hi6, hih, hsupply⟩ := hH4 u v a b hab hTa hTb
  have hn : (0 : ℝ) < Fintype.card V := by
    have : Nonempty V := ⟨u⟩
    exact_mod_cast Fintype.card_pos
  have hpow : (Fintype.card V : ℝ) ^ (i - 4) =
      Fintype.card V * (Fintype.card V : ℝ) ^ (i - 5) := by
    rw [← pow_succ']; congr 1; omega
  have hchoose : (2 : ℝ) ^ Nat.choose i 2 ≤ 2 ^ Nat.choose h 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hwin' : ((Z.card : ℝ) + 5 * d) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose i 2 ≤
      α / 2 * (Fintype.card V : ℝ) ^ (i - 4) := by
    rw [hpow]
    have hp : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (i - 5) := by positivity
    have hZ : (0 : ℝ) ≤ (Z.card : ℝ) + 5 * d := by positivity
    calc ((Z.card : ℝ) + 5 * d) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose i 2
        ≤ ((Z.card : ℝ) + 5 * d) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose h 2 :=
          mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = (((Z.card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2) * (Fintype.card V : ℝ) ^ (i - 5) := by
          ring
      _ ≤ (α / 2 * Fintype.card V) * (Fintype.card V : ℝ) ^ (i - 5) :=
          mul_le_mul_of_nonneg_right hwin hp
      _ = α / 2 * (Fintype.card V * (Fintype.card V : ℝ) ^ (i - 5)) := by ring
  have hgood := robust_fresh_hinges hab hTa hTb i hi6 α Z B d hdeg hB hsupply hwin'
  have hpos : (0 : ℝ) < α / 2 * (Fintype.card V : ℝ) ^ (i - 4) := by positivity
  obtain ⟨J, hJ⟩ : ((hinges H F u v a b i).filter (fun J =>
      (∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) ∧ Disjoint J B)).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hpos.trans_le hgood
  rw [Finset.mem_filter] at hJ
  exact ⟨i, hi6, hih, J, hJ.1, hJ.2⟩

/-- Un vecino común `t` de `u, v` con la etiqueta de `a` da un triángulo permitido `uvt`. -/
lemma allowed_of_commonNbr {H : Host V I} {F : Set (Multiset I)} {u v a t : V}
    (hTa : IsAllowed H F {u, v, a}) (ht : t ∈ commonNbrs H (H.lab a) u v) :
    IsAllowed H F {u, v, t} := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hut, hvt, hlab⟩ := ht
  have hut' : u ≠ t := hut.ne
  have hvt' : v ≠ t := hvt.ne
  have huvadj : H.G.Adj u v := hTa.2.1 u (by simp) v (by simp) huv
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [huv, hut']),
      Finset.card_insert_of_notMem (by simp [hvt']), Finset.card_singleton]
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
  · have h1 : ({u, v, t} : Finset V).val.map H.lab = ({u, v, a} : Finset V).val.map H.lab := by
      rw [Finset.insert_val_of_notMem (by simp [huv, hut']),
        Finset.insert_val_of_notMem (by simp [hvt']),
        Finset.insert_val_of_notMem (by simp [huv, hua]),
        Finset.insert_val_of_notMem (by simp [hva])]
      simp [hlab]
    rw [h1]; exact hTa.2.2

/-- **Ápice fresco desde (H3).** Si `|X| < α n`, existe `t ∉ X` con `uvt` permitido. -/
lemma exists_fresh_apex {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) {u v a : V} (hTa : IsAllowed H F {u, v, a}) (X : Finset V)
    (hX : (X.card : ℝ) < α * Fintype.card V) :
    ∃ t, IsAllowed H F {u, v, t} ∧ t ∉ X := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  have hlab : ({H.lab u, H.lab v, H.lab a} : Multiset I) ∈ F := by
    have := hTa.2.2
    rwa [Finset.insert_val_of_notMem (by simp [huv, hua]),
      Finset.insert_val_of_notMem (by simp [hva])] at this
  have hc := hH3 u v huv (H.lab a) hlab
  have hlt : X.card < (commonNbrs H (H.lab a) u v).card := by
    exact_mod_cast hX.trans_le hc
  obtain ⟨t, ht, htX⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨t, allowed_of_commonNbr hTa ht, htX⟩

/-- **A2: bisagra compuesta robusta.** Bajo (H3), (H4) y las ventanas
`|U| + 2 + 4d < α n` y `(|U| + h + 5d) 2^{C(h,2)} ≤ (α/2) n`, para cada par
`T_a = uva`, `T_b = uvb` existe una bisagra `J` que es disjunta del grafo prohibido `B`
(grado `≤ d`; puede contener `ab`, `uv` y las cuñas originales), no contiene `ab`,
evita el historial `U` fuera de las raíces y tiene orden `≤ 2h − 3`. -/
theorem exists_robust_composite_hinge {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {u v a b : V}
    (hab : a ≠ b) (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b})
    (U : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hwin2 : ((U.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ J, IsHinge H F u v a b J ∧ Disjoint J B ∧ s(a, b) ∉ J ∧
      (∀ z ∈ U, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) ∧
      (support J).card ≤ 2 * h - 3 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  -- 1. ápice `t`
  set X := U ∪ {a, b} ∪ (nbrIn B u ∪ nbrIn B v ∪ nbrIn B a ∪ nbrIn B b) with hXdef
  have hXc : (X.card : ℝ) < α * Fintype.card V := by
    have h1 : X.card ≤ U.card + 2 + 4 * d := by
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_le_two) _)) ?_)
      refine (Finset.card_union_le _ _).trans ?_
      refine (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _).trans ?_
      have := fun x => (card_nbrIn_le B x).trans (hdeg x)
      linarith [this u, this v, this a, this b]
    have h2 : (X.card : ℝ) ≤ U.card + 2 + 4 * d := by exact_mod_cast h1
    linarith
  obtain ⟨t, hTt, htX⟩ := exists_fresh_apex hH3 hTa X hXc
  obtain ⟨-, hut, hvt⟩ := distinct_of_card_three hTt.1
  simp only [hXdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or,
    nbrIn, Finset.mem_filter, Finset.mem_univ, true_and] at htX
  obtain ⟨⟨htU, hta, htb⟩, ⟨⟨htBu, htBv⟩, htBa⟩, htBb⟩ := htX
  have hat : a ≠ t := Ne.symm hta
  have hbt : b ≠ t := Ne.symm htb
  have hnB : ∀ x, s(x, t) ∉ B → s(t, x) ∉ B := fun x hx => by rwa [Sym2.eq_swap]
  -- 2. primera bisagra `H₁ : uva → uvt`
  have hwinZ1 : (((insert b U).card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V := by
    have : ((insert b U).card : ℝ) ≤ U.card + h := by
      have := Finset.card_insert_le b U
      have h6 : (1 : ℝ) ≤ h := by
        obtain ⟨i, hi6, hih, -⟩ := hH4 u v a b hab hTa hTb
        exact_mod_cast (show 1 ≤ h by omega)
      have : ((insert b U).card : ℝ) ≤ U.card + 1 := by exact_mod_cast this
      linarith
    refine le_trans ?_ hwin2
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨i₁, -, hi₁h, H₁, hH₁, hH₁Z, hH₁B⟩ :=
    exists_robust_hinge hα hH4 hat hTa hTt (insert b U) B d hdeg htBa hwinZ1
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hH₁
  have hb1 : b ∉ support H₁ := by
    intro hb
    have := hH₁Z b (Finset.mem_insert_self _ _) hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h' | h' | h'
    exacts [hub h'.symm, hvb h'.symm, hab h'.symm, hbt h']
  -- 3. segunda bisagra `H₂ : uvt → uvb`
  set Z₂ := U ∪ (support H₁).filter (fun x => x ∉ ({u, v, t} : Finset V)) with hZ₂
  have hR1 := (hinge_order_ge_six hat hTa hTt hH₁.1).1
  have hZ₂c : (Z₂.card : ℝ) ≤ U.card + h := by
    have h3 : ({u, v, t} : Finset V).card = 3 := hTt.1
    have hfilt : ((support H₁).filter (fun x => x ∉ ({u, v, t} : Finset V))).card + 3 ≤
        (support H₁).card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := support H₁)
        (fun x => x ∉ ({u, v, t} : Finset V))
      have hsub : ({u, v, t} : Finset V) ⊆ (support H₁).filter
          (fun x => ¬ x ∉ ({u, v, t} : Finset V)) := by
        intro x hx
        refine Finset.mem_filter.2 ⟨hR1 ?_, fun h' => h' hx⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
      have := Finset.card_le_card hsub
      omega
    have : Z₂.card ≤ U.card + h := by
      refine (Finset.card_union_le _ _).trans ?_
      omega
    exact_mod_cast this
  have hwinZ2 : ((Z₂.card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2
  obtain ⟨i₂, -, hi₂h, H₂, hH₂, hH₂Z, hH₂B⟩ :=
    exists_robust_hinge hα hH4 hbt.symm hTt hTb Z₂ B d hdeg (hnB b htBb) hwinZ2
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hH₂
  have ha2 : a ∉ support H₂ := by
    intro ha
    have haZ : a ∈ Z₂ := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR1 (by simp), by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hua.symm, hva.symm, hat⟩⟩)
    have := hH₂Z a haZ ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h' | h' | h'
    exacts [hua h'.symm, hva h'.symm, hat h', hab h']
  have h₁₂ : ∀ x ∈ support H₁, x ∈ support H₂ → x ∈ ({u, v, t} : Finset V) := by
    intro x hx1 hx2
    by_contra hxn
    have := hH₂Z x (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx1, hxn⟩)) hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this hxn
    rcases this with h' | h' | h' | h'
    · exact hxn (Or.inl h')
    · exact hxn (Or.inr (Or.inl h'))
    · exact hxn (Or.inr (Or.inr h'))
    · exact hb1 (h' ▸ hx1)
  -- 4. composición
  obtain ⟨hJ, habJ, hsupp⟩ := composite_hinge_of hTa hTb hTt hat hbt hH₁.1 hb1 hH₂.1 ha2 h₁₂
  refine ⟨_, hJ, ?_, habJ, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hH₁B, ?_⟩, hH₂B⟩
    simp only [wedge, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨htBu, htBv⟩
  · intro z hzU hz
    rw [hsupp, Finset.mem_union] at hz
    have hzt : z ≠ t := fun h' => htU (h' ▸ hzU)
    rcases hz with hz | hz
    · have := hH₁Z z (Finset.mem_insert_of_mem hzU) hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h' | h' | h' | h'
      exacts [Or.inl h', Or.inr (Or.inl h'), Or.inr (Or.inr (Or.inl h')), absurd h' hzt]
    · have := hH₂Z z (Finset.mem_union_left _ hzU) hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h' | h' | h' | h'
      exacts [Or.inl h', Or.inr (Or.inl h'), absurd h' hzt, Or.inr (Or.inr (Or.inr h'))]
  · rw [hsupp]
    have hsub : ({u, v, t} : Finset V) ⊆ support H₁ ∩ support H₂ := by
      have hR2 := (hinge_order_ge_six hbt.symm hTt hTb hH₂.1).1
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine Finset.mem_inter.2 ⟨hR1 ?_, hR2 ?_⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
    have h3 : ({u, v, t} : Finset V).card = 3 := hTt.1
    have := Finset.card_union_add_card_inter (support H₁) (support H₂)
    have := Finset.card_le_card hsub
    omega

end TypedTriangle
