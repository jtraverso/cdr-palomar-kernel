/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Master.Assembly
public import CDRBicolour.L156.Theorem
public import CDRBicolour.L181.MaxMatching
public import CDRBicolour.Prefix.StageB
public import CDRBicolour.EdgeColouring.Basic
public import Mathlib.Tactic.LinearCombination
public import OneFactor.Plantholt67

/-!
# L159, equitable form: the AAC-free master criterion

A variant of the master criterion of L159 in which the AAB class sizes are **equitable**
(`⌊E/B⌋` or `⌈E/B⌉`, `E = A(A-1)/2`) instead of prescribed, so the class-size (majorization)
lemma is not needed:

1. an equitable proper colouring of `K_A` by the `B` points has multiplicities `m` and `m+2`,
   `m+2 = A - 2⌊E/B⌋`; L181 (`l181_noAnchor`, proved) completes all ABB rows;
2. the BB graph left over has degrees `B-1-mult`; an equitable colouring by the `C` points has
   all classes of size `K' = (A+B+1-C)/2` (exactly, by the admissibility identity);
3. every `C` point then has multiplicity `C-A-1`; L156 (`l156`, proved) completes all BCC rows;
4. the CC graph left over is `A`-regular of even order `C` with `12A ≥ 11C`; it is
   1-factorizable by Chetwynd–Hilton 1985 (constant `6/7`)
   (`OneFactor.lineGraph_colorable_of_isRegular`, Palomar PALOMAR-2026-11-04-000016), giving the
   ACC blocks (`oneFactor_67`).

`eqMaster_realises : AdmissibleProfile A B C → EqMasterHyp A B C → Realises A B C`, with no
external hypothesis.
-/

@[expose] public section

namespace CDRBicolour.Master

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions
  CDRBicolour.Prefix CDRBicolour.L184

universe u

/-- **Chetwynd–Hilton (1985)**, *Regular graphs of high degree are 1-factorizable*,
Proc. London Math. Soc. 50 (1985) 193–206: a simple `d`-regular graph of even order `N` with
`d ≥ 6N/7` is 1-factorizable (equivalently, `d`-edge-colourable).  External hypothesis. -/
def ChetwyndHilton_1985 : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    Even (Fintype.card V) → (∀ v, G.degree v = d) → 6 * Fintype.card V ≤ 7 * d →
      EdgeColourable G d

/-- **Chetwynd–Hilton 1985: regular graphs of degree at least `6/7` of the (even) order are
1-factorizable** (Palomar, `OneFactor.lineGraph_colorable_of_isRegular67`). -/
theorem oneFactor_67 {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hev : Even (Fintype.card V)) (hreg : ∀ v, G.degree v = d)
    (h : 6 * Fintype.card V ≤ 7 * d) : EdgeColourable G d := by
  obtain ⟨k, hk⟩ := hev
  exact OneFactor.lineGraph_colorable_of_isRegular67 G (n := k) (by omega)
    (fun v => by convert hreg v) (by omega)

/-- The scalar hypotheses of the equitable master criterion, for the class order `(A,B,C)`. -/
def EqMasterHyp (A B C : ℕ) : Prop :=
  C % 2 = 0 ∧ A < C ∧ A < B ∧ (B - A) % 2 = 1 ∧ 3 ≤ B - A ∧ 6 * (C - A - 1) ≤ C ∧
    6 * C ≤ 7 * A ∧ 6 * (A - 2 * (A * (A - 1) / 2 / B)) ≤ B ∧
    B + 5 ≤ A - 2 * (A * (A - 1) / 2 / B) + C

instance (A B C : ℕ) : Decidable (EqMasterHyp A B C) := by unfold EqMasterHyp; infer_instance

/-- `Σ_v mult v = Σ_j |miss j|`. -/
theorem sum_mult_eq {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) :
    ∑ v, mult G χ v = ∑ j, (miss G χ j).card := by
  simp only [mult, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← card_filter]; congr 1; ext v; simp

/-- Equitable sizes with sum `N·q` are all equal to `q`. -/
theorem equitable_const {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (heq : ∀ x y, s x ≤ s y + 1) (q : ℕ) (hN : 0 < Fintype.card ι)
    (hsum : ∑ x, s x = Fintype.card ι * q) : ∀ x, s x = q := by
  obtain ⟨h1, h2⟩ := equitable_sizes s heq (q + 1) (Fintype.card ι) hN le_rfl (by omega)
    (by rw [hsum]; ring)
  have hall := (card_filter_eq_iff (s := (univ : Finset ι))).1 (by rw [h2, card_univ])
  intro x; have := hall x (mem_univ x); omega

/-- Relabelling the palette through an equivalence. -/
theorem colourClass_equiv {W Cl : Type*} [DecidableEq W] [DecidableEq Cl] {k : ℕ}
    (E : Finset (Sym2 W)) (c : Sym2 W → Fin k) (e : Cl ≃ Fin k) (v : Cl) :
    colourClass E (e.symm ∘ c) v = colourClass E c (e v) := by
  ext x; simp [mem_colourClass, Equiv.symm_apply_eq]

/-- The non-degenerate pairs inside a finite set. -/
def pairsOf {Cl : Type*} [DecidableEq Cl] (S : Finset Cl) : Finset (Sym2 Cl) :=
  S.sym2.filter fun e => ¬ e.IsDiag

theorem pairsOf_pair {Cl : Type*} [DecidableEq Cl] {x y : Cl} (hxy : x ≠ y) :
    pairsOf ({x, y} : Finset Cl) = {s(x, y)} := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [pairsOf, mem_filter, mem_sym2_iff, Sym2.mem_iff, mem_insert, mem_singleton,
      Sym2.mk_isDiag_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨h, huv⟩
      rcases h u (Or.inl rfl) with rfl | rfl <;> rcases h v (Or.inr rfl) with rfl | rfl
      · exact absurd rfl huv
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl huv
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨fun w hw => by rcases hw with rfl | rfl <;> simp, hxy⟩
      · exact ⟨fun w hw => by rcases hw with rfl | rfl <;> simp, Ne.symm hxy⟩

theorem isPerfectPairing_pairsOf {Cl : Type*} [DecidableEq Cl] {S : Finset Cl}
    (h : S.card = 2) : IsPerfectPairing (pairsOf S) S := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 h
  rw [pairsOf_pair hxy]
  refine ⟨fun e he => by rw [mem_singleton] at he; subst he; exact (Sym2.mk_isDiag_iff).not.2 hxy,
    fun e he v hv => ?_, fun v hv => ⟨s(x, y), ⟨mem_singleton_self _, ?_⟩,
      fun e he => mem_singleton.1 he.1⟩⟩
  · rw [mem_singleton] at he; subst he
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
  · rcases mem_insert.1 hv with rfl | hv
    · exact Sym2.mem_mk_left _ _
    · rw [mem_singleton] at hv; subst hv; exact Sym2.mem_mk_right _ _

theorem pairsOf_disjoint {Cl : Type*} [DecidableEq Cl] {S T : Finset Cl} (hS : S.card = 2)
    (hT : T.card = 2) (hST : S ≠ T) : Disjoint (pairsOf S) (pairsOf T) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hS
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 hT
  rw [pairsOf_pair hxy, pairsOf_pair huv, disjoint_singleton]
  intro h
  apply hST
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pair_comm _ _

/-- **Stages 3–4 of the master criterion and the assembly**, from stage-1 data (a proper
colouring of `K_A` by the `B` points with pair-disjoint perfect pairings of the missing sets: the
AAB and ABB blocks, all multiplicities at least `B - C + 1`) and an equitable proper colouring of
the BB graph left over by the `C` points (the BBC blocks) whose missing sets of size `2` are
pairwise distinct.  Rows missing two colours are packed first, the others by L156. -/
theorem master_core {A B C : ℕ}
    (hadm : AdmissibleProfile A B C) (hC : C % 2 = 0) (hAC : A < C) (hAB : A < B)
    (ht : (B - A) % 2 = 1) (hρ6 : 6 * (C - A - 1) ≤ C) (h76 : 6 * C ≤ 7 * A)
    (χ₁ : Sym2 (AType (col3 A B C)) → BType (col3 A B C))
    (M₁ : AType (col3 A B C) → Finset (Sym2 (BType (col3 A B C))))
    (hχ₁ : ProperOn (⊤ : SimpleGraph (AType (col3 A B C))).edgeFinset χ₁)
    (hM₁ : ∀ i, IsPerfectPairing (M₁ i) (miss ⊤ χ₁ i)) (hM₁d : PairDisjoint M₁)
    (hlo1 : ∀ v, B + 1 ≤ mult ⊤ χ₁ v + C)
    (χ₂ : Sym2 (BType (col3 A B C)) → CType (col3 A B C))
    (hχ₂ : ProperOn (unusedGraph M₁).edgeFinset χ₂)
    (hχ₂e : IsEquitable (unusedGraph M₁).edgeFinset χ₂)
    (hvd : ∀ j j', j ≠ j' → (miss (unusedGraph M₁) χ₂ j).card = 2 →
      miss (unusedGraph M₁) χ₂ j ≠ miss (unusedGraph M₁) χ₂ j') : Realises A B C := by
  classical
  have hcA : Fintype.card (AType (col3 A B C)) = A := card_classA
  have hcB : Fintype.card (BType (col3 A B C)) = B := card_classB
  have hcC : Fintype.card (CType (col3 A B C)) = C := card_classC
  have hdeg1 : ∀ v, (⊤ : SimpleGraph (AType (col3 A B C))).degree v = A - 1 := fun v => by
    have := SimpleGraph.complete_graph_degree (V := AType (col3 A B C)) v
    rw [hcA] at this; exact this
  have hpar1 : ∀ v, mult (⊤ : SimpleGraph (AType (col3 A B C))) χ₁ v % 2 = A % 2 := by
    intro v; have := mult_add_two_mul_class hχ₁ v; rw [hcA] at this; omega
  -- stage 2: the BB graph, equitable colouring by `C` with all classes of size `K'`
  have hdeg2 : ∀ v, (unusedGraph M₁).degree v + mult (⊤ : SimpleGraph (AType (col3 A B C))) χ₁ v = B - 1 := by
    intro v; have := unused_degree_add_mult hM₁ hM₁d v; rw [hcB] at this; exact this
  set K' := (A + B + 1 - C) / 2 with hK'def
  have hK'2 : 2 * K' = A + B + 1 - C := by omega
  have hsummult : ∑ v, mult (⊤ : SimpleGraph (AType (col3 A B C))) χ₁ v = A * (B - A + 1) := by
    rw [sum_mult_eq]
    have : ∀ j, (miss (⊤ : SimpleGraph (AType (col3 A B C))) χ₁ j).card = B - A + 1 := by
      intro j; rw [card_miss hχ₁, hcB, hdeg1]; omega
    rw [sum_congr rfl fun j _ => this j, sum_const, card_univ, hcA, smul_eq_mul]
  have hE2' : 2 * (unusedGraph M₁).edgeFinset.card + A * (B - A + 1) = B * (B - 1) := by
    have h2 : ∑ v, ((unusedGraph M₁).degree v + mult (⊤ : SimpleGraph (AType (col3 A B C))) χ₁ v) = ∑ _v : BType (col3 A B C), (B - 1) :=
      sum_congr rfl fun v _ => hdeg2 v
    rw [sum_add_distrib, sum_const, card_univ, hcB, smul_eq_mul, (unusedGraph M₁).sum_degrees_eq_twice_card_edges,
      hsummult] at h2
    exact h2
  have hadmZ := hadm.2.2.2.2.1
  have hEC2 : (unusedGraph M₁).edgeFinset.card = C * K' := by
    have hz : (2 * (unusedGraph M₁).edgeFinset.card : ℤ) = C * (2 * K' : ℕ) := by
      have h1 : ((2 * (unusedGraph M₁).edgeFinset.card + A * (B - A + 1) : ℕ) : ℤ) = ((B * (B - 1) : ℕ) : ℤ) := by
        rw [hE2']
      rw [hK'2]
      push_cast [Nat.cast_sub (show A ≤ B by omega), Nat.cast_sub (show 1 ≤ B by omega),
        Nat.cast_sub (show C ≤ A + B + 1 by omega)] at h1 ⊢
      linear_combination h1 + hadmZ
    have h2 : 2 * (unusedGraph M₁).edgeFinset.card = C * (2 * K') := by exact_mod_cast hz
    rw [Nat.mul_left_comm] at h2
    omega
  have hs2 := equitable_const (fun v => (colourClass (unusedGraph M₁).edgeFinset χ₂ v).card)
    (fun x y => hχ₂e x y) K'
    (by rw [hcC]; omega)
    (by rw [sum_card_colourClass_univ, hcC, hEC2])
  set ρ := C - A - 1 with hρdef
  have hmult2 : ∀ v, mult (unusedGraph M₁) χ₂ v = ρ := by
    intro v
    have h := mult_add_two_mul_class hχ₂ v
    rw [hcB, hs2 v] at h
    omega
  -- stage 3: rows missing two colours are packed directly, L156 completes the others
  have hmiss2 : ∀ j, 2 ≤ (miss (unusedGraph M₁) χ₂ j).card ∧ (miss (unusedGraph M₁) χ₂ j).card % 2 = 0 := by
    intro j; rw [card_miss hχ₂, hcC]
    have := hdeg2 j; have := hlo1 j; have := hpar1 j; omega
  set D₀ := univ.filter fun j => (miss (unusedGraph M₁) χ₂ j).card = 2 with hD₀
  set M₀ : BType (col3 A B C) → Finset (Sym2 (CType (col3 A B C))) := fun j =>
    if (miss (unusedGraph M₁) χ₂ j).card = 2 then pairsOf (miss (unusedGraph M₁) χ₂ j) else ∅ with hM₀
  obtain ⟨χ₂', hχ₂', hmult2', M₂, hM₂, hM₂d⟩ :=
    CDRBicolour.L156.l156 (unusedGraph M₁) χ₂ ρ univ D₀ M₀ hχ₂
      (fun j => Nat.even_iff.2 (hmiss2 j).2)
      (fun j hj => by
        rw [hD₀, mem_filter] at hj
        simp only [hM₀, if_pos hj.2]; exact isPerfectPairing_pairsOf hj.2)
      (fun j hj => by
        rw [hD₀, mem_filter] at hj
        have h2 : (miss (unusedGraph M₁) χ₂ j).card ≠ 2 := fun h => hj ⟨mem_univ _, h⟩
        refine ⟨by simp only [hM₀, if_neg h2], ?_⟩
        have := hmiss2 j; omega)
      (fun j j' hjj => by
        simp only [hM₀]
        split_ifs with h1 h2
        · exact pairsOf_disjoint h1 h2 (hvd j j' hjj h1)
        · exact disjoint_empty_right _
        · exact disjoint_empty_left _
        · exact disjoint_empty_left _)
      (fun v => (hmult2 v).le) (fun v _ => hmult2 v)
      (by rw [card_univ, hcC]; exact hρ6)
  -- stage 4: the `A`-regular CC residual and Chetwynd–Hilton
  set G₃ : SimpleGraph (CType (col3 A B C)) := unusedGraph M₂ with hG₃
  have hdeg3 : ∀ v, G₃.degree v = A := by
    intro v
    have := unused_degree_add_mult hM₂ hM₂d v
    rw [hcC, hmult2', hmult2] at this
    show (unusedGraph M₂).degree v = A
    omega
  have hEC : EdgeColourable G₃ A :=
    oneFactor_67 G₃ A (by rw [hcC, Nat.even_iff]; exact hC) hdeg3 (by rw [hcC]; exact h76)
  obtain ⟨c₃, hc₃⟩ := exists_properOn_of_edgeColourable G₃ (by omega : 0 < A) hEC
  let eA : AType (col3 A B C) ≃ Fin A := Fintype.equivFinOfCardEq hcA
  set χ₃ : Sym2 (CType (col3 A B C)) → AType (col3 A B C) := eA.symm ∘ c₃ with hχ₃def
  have hχ₃ : ProperOn G₃.edgeFinset χ₃ := properOn_comp hc₃ eA.symm.injective
  have hM₃ : ∀ c, miss G₃ χ₃ c = ∅ := by
    intro c
    rw [← card_eq_zero, card_miss hχ₃, hcA, hdeg3, Nat.sub_self]
  -- assembly
  obtain ⟨S, hS⟩ := master_assembly χ₁ M₁ hχ₁ hM₁ hM₁d χ₂' M₂ hχ₂' hM₂ hM₂d χ₃ hχ₃ hM₃
  refine ⟨S, col3 A B C, hS, ?_, ?_, ?_⟩
  · rw [classSize, ← Fintype.card_subtype]; exact hcA
  · rw [classSize, ← Fintype.card_subtype]; exact hcB
  · rw [classSize, ← Fintype.card_subtype]; exact hcC



/-- **Stages 2–4 of the master criterion and the assembly**, from any stage-1 data whose
multiplicities are at least `B - C + 3` (an equitable colouring of the BB graph by Vizing). -/
theorem master_of_stage1 {A B C : ℕ}
    (hadm : AdmissibleProfile A B C) (hC : C % 2 = 0) (hAC : A < C) (hAB : A < B)
    (ht : (B - A) % 2 = 1) (hρ6 : 6 * (C - A - 1) ≤ C) (h76 : 6 * C ≤ 7 * A)
    (χ₁ : Sym2 (AType (col3 A B C)) → BType (col3 A B C))
    (M₁ : AType (col3 A B C) → Finset (Sym2 (BType (col3 A B C))))
    (hχ₁ : ProperOn (⊤ : SimpleGraph (AType (col3 A B C))).edgeFinset χ₁)
    (hM₁ : ∀ i, IsPerfectPairing (M₁ i) (miss ⊤ χ₁ i)) (hM₁d : PairDisjoint M₁)
    (hlo1 : ∀ v, B + 3 ≤ mult ⊤ χ₁ v + C) : Realises A B C := by
  classical
  have hcB : Fintype.card (BType (col3 A B C)) = B := card_classB
  have hcC : Fintype.card (CType (col3 A B C)) = C := card_classC
  have hdeg2 : ∀ v, (unusedGraph M₁).degree v + mult ⊤ χ₁ v = B - 1 := by
    intro v; have := unused_degree_add_mult hM₁ hM₁d v; rw [hcB] at this; exact this
  have hΔ2 : (unusedGraph M₁).maxDegree + 1 ≤ C := by
    have : ∀ v, (unusedGraph M₁).degree v ≤ C - 1 := by
      intro v; have := hdeg2 v; have := hlo1 v; omega
    have := SimpleGraph.maxDegree_le_of_forall_degree_le _ _ this
    omega
  obtain ⟨c₂, hc₂p, hc₂e, -⟩ := exists_equitable_edge_colouring (unusedGraph M₁) C hΔ2
  let eC : CType (col3 A B C) ≃ Fin C := Fintype.equivFinOfCardEq hcC
  have hχ₂ : ProperOn (unusedGraph M₁).edgeFinset (eC.symm ∘ c₂) :=
    properOn_comp hc₂p eC.symm.injective
  refine master_core hadm hC hAC hAB ht hρ6 h76 χ₁ M₁ hχ₁ hM₁ hM₁d
    (fun v => by have := hlo1 v; omega) (eC.symm ∘ c₂) hχ₂ ?_ ?_
  · intro x y
    rw [colourClass_equiv, colourClass_equiv]; exact hc₂e (eC x) (eC y)
  · intro j j' _ h2
    exfalso
    rw [card_miss hχ₂, hcC] at h2
    have := hdeg2 j; have := hlo1 j; omega

/-- **Equitable master criterion (L159).** -/
theorem eqMaster_realises {A B C : ℕ}
    (hadm : AdmissibleProfile A B C) (h : EqMasterHyp A B C) : Realises A B C := by
  classical
  obtain ⟨hC, hAC, hAB, ht, ht3, hρ6, h76, h6, hlo⟩ := h
  set col := col3 A B C with hcol
  have hcA : Fintype.card (AType col) = A := card_classA
  have hcB : Fintype.card (BType col) = B := card_classB
  have hcC : Fintype.card (CType col) = C := card_classC
  set E := A * (A - 1) / 2 with hEdef
  set K := E / B with hKdef
  have hA7 : 7 ≤ A := by omega
  have hE2 : 2 * E = A * (A - 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self A)
  have hKB : K * B ≤ E := Nat.div_mul_le_self E B
  have hKB' : E < (K + 1) * B := by
    have := Nat.div_add_mod E B
    have := Nat.mod_lt E (by omega : 0 < B)
    rw [hKdef]; nlinarith
  have hK2 : 2 * K + 2 ≤ A := by
    by_contra hcon
    have h1 : (A - 1) * B ≤ (2 * K) * B := Nat.mul_le_mul_right B (by omega)
    have h3 : (A - 1) * A < (A - 1) * B := Nat.mul_lt_mul_of_pos_left hAB (by omega)
    have h4 : (A - 1) * A = A * (A - 1) := mul_comm _ _
    nlinarith
  set m := A - 2 * K - 2 with hm
  -- stage 1: equitable AAB colouring of `K_A`, then L181 for ABB
  have hdeg1 : ∀ v, (⊤ : SimpleGraph (AType col)).degree v = A - 1 := fun v => by
    have := SimpleGraph.complete_graph_degree (V := AType col) v
    rw [hcA] at this; exact this
  have hΔ1 : (⊤ : SimpleGraph (AType col)).maxDegree + 1 ≤ B := by
    have := SimpleGraph.maxDegree_le_of_forall_degree_le (⊤ : SimpleGraph (AType col)) (A - 1) (fun v => (hdeg1 v).le)
    omega
  obtain ⟨c₁, hc₁p, hc₁e, -⟩ := exists_equitable_edge_colouring (⊤ : SimpleGraph (AType col)) B hΔ1
  let eB : BType col ≃ Fin B := Fintype.equivFinOfCardEq hcB
  set χ₁ : Sym2 (AType col) → BType col := eB.symm ∘ c₁ with hχ₁def
  have hχ₁ : ProperOn (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ := properOn_comp hc₁p eB.symm.injective
  have hBK1 : B * (K + 1) = B * K + B := by ring
  have hKB2 : B * K ≤ E := by rw [mul_comm]; exact hKB
  have hKB3 : E < B * K + B := by rw [← hBK1, mul_comm]; exact hKB'
  have hcardE : (⊤ : SimpleGraph (AType col)).edgeFinset.card = E := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcA, Nat.choose_two_right]
  have hcls1 : ∀ v, colourClass (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ v =
      colourClass (⊤ : SimpleGraph (AType col)).edgeFinset c₁ (eB v) :=
    fun v => colourClass_equiv _ c₁ eB v
  have hsum1 : ∑ v, (colourClass (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ v).card +
      (B * (K + 1) - E) = Fintype.card (BType col) * (K + 1) := by
    rw [sum_card_colourClass_univ, hcardE, hcB]
    omega
  obtain ⟨hs1, -⟩ := equitable_sizes (fun v => (colourClass (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ v).card)
    (fun x y => by
      show (colourClass _ χ₁ x).card ≤ (colourClass _ χ₁ y).card + 1
      rw [hcls1, hcls1]; exact hc₁e (eB x) (eB y))
    (K + 1) (B * (K + 1) - E) (by omega) (by rw [hcB]; omega) (by omega) hsum1
  have hmult1 : ∀ v, mult (⊤ : SimpleGraph (AType col)) χ₁ v = m ∨ mult (⊤ : SimpleGraph (AType col)) χ₁ v = m + 2 := by
    intro v
    have h := mult_add_two_mul_class hχ₁ v
    rw [hcA] at h
    have hs1' : (colourClass (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ v).card = K + 1 ∨
        (colourClass (⊤ : SimpleGraph (AType col)).edgeFinset χ₁ v).card + 1 = K + 1 := hs1 v
    rcases hs1' with h' | h' <;> omega
  obtain ⟨χ₁', hχ₁', hmult1', -, M₁, hM₁, hM₁d⟩ :=
    CDRBicolour.L181.l181_noAnchor.{0} (AType col) (BType col) (⊤ : SimpleGraph (AType col)) χ₁ m hχ₁
      (fun j => by
        rw [card_miss hχ₁, hcB, hdeg1, Nat.even_iff]
        exact ⟨by omega, by omega⟩)
      hmult1 (by rw [hcB]; omega)
  exact master_of_stage1 hadm hC hAC hAB ht hρ6 h76 χ₁' M₁ hχ₁' hM₁ hM₁d
    (fun v => by rcases hmult1' v with h | h <;> omega)

end CDRBicolour.Master
