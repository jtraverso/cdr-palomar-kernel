/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Master.Equitable

/-!
# L167–L168: the family `b = a + 4` with odd largest class

Profiles `(a, a+4, a+4+y)` with `y` odd, `3a = y² + 3y + 8`.  With roles `(A, B, C) = (a, c, b)`
the master construction applies, except that the stage-2 colouring must be
**vertex-distinguishing**: about half of the BCC rows miss only two colours, and their pairs must
be distinct.  Two published theorems supply such a colouring, stated here as literal hypotheses:

* `BKLS_Corollary_12` (Balister–Kostochka–Li–Schelp, JCTB 90 (2004), Cor. 12):
  `δ ≥ 5`, `Δ ≥ √(2|V|) + 4` ⇒ `χ'_vd ≤ k₀ + 1`, `k₀` the least `k` with
  `C(k, d) ≥ n_d` for every degree `d`;
* `RS_Theorem_3_1` (Rudašová–Soták, Discrete Math. 308 (2008), Thm 3.1): for `k ≥ χ'_vd`
  there is an equitable vertex-distinguishing proper `k`-edge-colouring.

Stage 1 is the equitable colouring of `K_a` by the `c` points (multiplicities `y+1`, `y+3`) and
L181; stages 3–4 are `master_core` (rows missing two colours packed first, L156, Chetwynd–Hilton).
-/

@[expose] public section

namespace CDRBicolour.Master

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions
  CDRBicolour.Prefix CDRBicolour.L184

universe u

/-- Vertex-distinguishing proper `k`-edge-colourability: distinct vertices see distinct sets of
colours. -/
def VDColourable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) : Prop :=
  ∃ χ : Sym2 V → Fin k, ProperOn G.edgeFinset χ ∧ ∀ u v, u ≠ v → present G χ u ≠ present G χ v

/-- **Balister–Kostochka–Li–Schelp, Corollary 12** (literal; `Δ ≥ √(2n) + 4` written as
`4 ≤ Δ ∧ 2n ≤ (Δ - 4)²`; `k₀` the least integer with `C(k₀, d) ≥ n_d` for all `d`). -/
def BKLS_Corollary_12 : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k₀ : ℕ),
    (∀ v, 5 ≤ G.degree v) → 4 ≤ G.maxDegree → 2 * Fintype.card V ≤ (G.maxDegree - 4) ^ 2 →
    (∀ d, (univ.filter fun v => G.degree v = d).card ≤ k₀.choose d) →
    (∀ k < k₀, ∃ d, k.choose d < (univ.filter fun v => G.degree v = d).card) →
    VDColourable G (k₀ + 1)

/-- **Rudašová–Soták, Theorem 3.1** (literal): for every `k ≥ χ'_vd(G)` there is an equitable
vertex-distinguishing proper `k`-edge-colouring. -/
def RS_Theorem_3_1 : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    VDColourable G k → ∃ χ : Sym2 V → Fin k, ProperOn G.edgeFinset χ ∧
      (∀ u v, u ≠ v → present G χ u ≠ present G χ v) ∧ IsEquitable G.edgeFinset χ

theorem choose_three_ge (n : ℕ) (h : 6 ≤ n) : n ≤ n.choose 3 := by
  have h1 : n.choose 1 ≤ n.choose 2 := Nat.choose_le_succ_of_lt_half_left (by omega)
  have h2 : n.choose 2 ≤ n.choose 3 := Nat.choose_le_succ_of_lt_half_left (by omega)
  rw [Nat.choose_one_right] at h1
  omega

/-- Arithmetic of the family: `A = y + 3 + 2k`, `6k + 1 = y²`, `B = 2y + 7 + 2k`. -/
theorem x4_count {y k z r B : ℕ} (hB : B = 2 * y + 7 + 2 * k) (h6k : 6 * k + 1 = y * y)
    (hz : 2 * z = (y + 3 + 2 * k) * (y + 2 + 2 * k)) (hr : z + r = B * (k + 1)) :
    6 * r + 3 * y = y * y + 20 := by
  subst hB; nlinarith

theorem x4_zle {y k z B : ℕ} (hB : B = 2 * y + 7 + 2 * k) (h6k : 6 * k + 1 = y * y)
    (hy : 17 ≤ y) (hz : 2 * z = (y + 3 + 2 * k) * (y + 2 + 2 * k)) : z ≤ B * (k + 1) := by
  subst hB
  have hyy : 17 * y ≤ y * y := Nat.mul_le_mul_right y hy
  nlinarith

/-! Small arithmetic steps, kept out of the large context (where `omega` would compare heavy
atoms). -/

theorem x4_mult {A k y mv sv : ℕ} (hk : A = y + 3 + 2 * k) (h : mv + 2 * sv = A)
    (hs : sv = k + 1 ∨ sv + 1 = k + 1) : mv = y + 1 ∨ mv = y + 1 + 2 := by omega

theorem x4_mult_hi {A k y mv sv : ℕ} (hk : A = y + 3 + 2 * k) (h : mv + 2 * sv = A) :
    mv = y + 1 + 2 ↔ sv + 1 = k + 1 := by omega

theorem x4_deg {B C y dv : ℕ} (hBC : B = C + y) (hC : 4 ≤ C) :
    (dv + (y + 1) = B - 1 → dv = C - 2) ∧ (dv + (y + 1 + 2) = B - 1 → dv = C - 4) := by
  constructor <;> intro h <;> omega

theorem x4_r {A B C y k r : ℕ} (hk : A = y + 3 + 2 * k) (hCA : C = A + 4) (hBC : B = C + y)
    (h6k : 6 * k + 1 = y * y) (hyy : 17 * y ≤ y * y) (h6r : 6 * r + 3 * y = y * y + 20) :
    0 < r ∧ r ≤ B ∧ B - r ≤ C - 1 ∧ r ≤ C - 1 ∧ 1 < B - r := by
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem sub_of_add' {r X B : ℕ} (h : r + X = B) : X = B - r := by omega

/-- **L168 core**: roles `(A, B, C) = (a, c, b)`. -/
theorem x4_core (hBK : BKLS_Corollary_12.{0})
    (hRS : RS_Theorem_3_1.{0}) {A B C y : ℕ} (hadm : AdmissibleProfile A B C) (hCA : C = A + 4)
    (hBC : B = C + y) (h3 : 3 * A = y * y + 3 * y + 8) (hy : 17 ≤ y) (hyo : y % 2 = 1) :
    Realises A B C := by
  classical
  have hyy : 17 * y ≤ y * y := Nat.mul_le_mul_right y hy
  have hsq : (y * y) % 2 = 1 := by rw [Nat.mul_mod, hyo]
  obtain ⟨k, hk⟩ : ∃ k, A = y + 3 + 2 * k := ⟨(A - y - 3) / 2, by omega⟩
  have h6k : 6 * k + 1 = y * y := by omega
  have hBk : B = 2 * y + 7 + 2 * k := by omega
  -- all the scalar facts, before any graph enters the context
  have hC0 : C % 2 = 0 := by omega
  have hAC : A < C := by omega
  have hAB : A < B := by omega
  have ht : (B - A) % 2 = 1 := by omega
  have hρ6 : 6 * (C - A - 1) ≤ C := by omega
  have h76 : 6 * C ≤ 7 * A := by omega
  have hC6 : 4 ≤ C - 2 := by omega
  have hd5 : 5 ≤ C - 4 := by omega
  have hd5' : 5 ≤ C - 2 := by omega
  have hC21 : C - 2 = C - 1 - 1 := by omega
  have hC43 : C - 4 = C - 1 - 3 := by omega
  have hC1 : 1 ≤ C - 1 := by omega
  have hC3 : 3 ≤ C - 1 := by omega
  have hC7 : 6 ≤ C - 1 := by omega
  have hC64 : C - 2 - 4 = C - 6 := by omega
  have hC12 : C - 1 = C - 2 + 1 := by omega
  have hCcard : C = C - 1 + 1 := by omega
  have h2B : 2 * B ≤ (C - 6) ^ 2 := by
    rw [show C - 6 = y + 1 + 2 * k by omega, hBk]; nlinarith
  have hloa : B + 1 ≤ y + 1 + C := by omega
  have hlob : B + 1 ≤ y + 1 + 2 + C := by omega
  have hmiss1 : B - (A - 1) = y + 5 := by omega
  have hy5e : (y + 5) % 2 = 0 := by omega
  have hy54 : 4 ≤ y + 5 := by omega
  have hC24 : C - 2 ≠ C - 4 := by omega
  have hyne : y + 1 ≠ y + 1 + 2 := by omega
  have hC4 : 4 ≤ C := by omega
  have h6m : 6 * (y + 1 + 2) ≤ B := by omega
  have hcA : Fintype.card (AType (col3 A B C)) = A := card_classA
  have hcB : Fintype.card (BType (col3 A B C)) = B := card_classB
  have hcC : Fintype.card (CType (col3 A B C)) = C := card_classC
  -- stage 1: equitable colouring of `K_A` by the `B` points
  have hdeg1 : ∀ v, (⊤ : SimpleGraph (AType (col3 A B C))).degree v = A - 1 := fun v => by
    have := SimpleGraph.complete_graph_degree (V := AType (col3 A B C)) v
    rw [hcA] at this; exact this
  have hΔ1 : (⊤ : SimpleGraph (AType (col3 A B C))).maxDegree + 1 ≤ B := by
    have := SimpleGraph.maxDegree_le_of_forall_degree_le (⊤ : SimpleGraph (AType (col3 A B C)))
      (A - 1) (fun v => (hdeg1 v).le)
    omega
  obtain ⟨c₁, hc₁p, hc₁e, -⟩ :=
    exists_equitable_edge_colouring (⊤ : SimpleGraph (AType (col3 A B C))) B hΔ1
  let eB : BType (col3 A B C) ≃ Fin B := Fintype.equivFinOfCardEq hcB
  have hχ₁ : ProperOn (⊤ : SimpleGraph (AType (col3 A B C))).edgeFinset (eB.symm ∘ c₁) :=
    properOn_comp hc₁p eB.symm.injective
  set z := (⊤ : SimpleGraph (AType (col3 A B C))).edgeFinset.card with hzdef
  have hz : 2 * z = (y + 3 + 2 * k) * (y + 2 + 2 * k) := by
    rw [hzdef, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcA, Nat.choose_two_right,
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self A), hk]
    congr 1; omega
  obtain ⟨r, hr⟩ : ∃ r, z + r = B * (k + 1) :=
    ⟨_, Nat.add_sub_of_le (x4_zle hBk h6k hy hz)⟩
  have h6r := x4_count hBk h6k hz hr
  obtain ⟨hr0, hrB, hBr, hr1, hBr2⟩ := x4_r hk hCA hBC h6k hyy h6r
  obtain ⟨hs1, hcnt1⟩ := equitable_sizes
    (fun v => (colourClass (⊤ : SimpleGraph (AType (col3 A B C))).edgeFinset (eB.symm ∘ c₁) v).card)
    (fun x y => by
      show (colourClass _ (eB.symm ∘ c₁) x).card ≤ (colourClass _ (eB.symm ∘ c₁) y).card + 1
      rw [colourClass_equiv, colourClass_equiv]; exact hc₁e (eB x) (eB y))
    (k + 1) r hr0 (by rw [hcB]; exact hrB) (Nat.le_add_left 1 k)
    (by rw [sum_card_colourClass_univ, hcB, ← hzdef]; exact hr)
  have hmult1 : ∀ v, mult ⊤ (eB.symm ∘ c₁) v = y + 1 ∨ mult ⊤ (eB.symm ∘ c₁) v = y + 1 + 2 := by
    intro v
    have h := mult_add_two_mul_class hχ₁ v
    rw [hcA] at h
    exact x4_mult hk h (hs1 v)
  have hhi1 : (univ.filter fun v => mult ⊤ (eB.symm ∘ c₁) v = y + 1 + 2).card = r := by
    rw [← hcnt1]
    refine congrArg Finset.card (filter_congr fun v _ => ?_)
    have h := mult_add_two_mul_class hχ₁ v
    rw [hcA] at h
    exact x4_mult_hi hk h
  obtain ⟨χ₁, hχ₁', hmult1', hcnt', M₁, hM₁, hM₁d⟩ :=
    CDRBicolour.L181.l181_noAnchor.{0} (AType (col3 A B C)) (BType (col3 A B C)) ⊤
      (eB.symm ∘ c₁) (y + 1) hχ₁
      (fun j => by
        rw [card_miss hχ₁, hcB, hdeg1, hmiss1, Nat.even_iff]
        exact ⟨hy5e, hy54⟩)
      hmult1 (by rw [hcB]; exact h6m)
  rw [hhi1] at hcnt'
  clear hmult1 hhi1 hs1 hcnt1 hχ₁ hc₁p hc₁e hΔ1
  -- stage 2: the CC graph (here the BB graph of the roles) and its degrees
  have hdeg2 : ∀ v, (unusedGraph M₁).degree v + mult ⊤ χ₁ v = B - 1 := by
    intro v; have := unused_degree_add_mult hM₁ hM₁d v; rw [hcB] at this; exact this
  have hdeg2' : ∀ v, ((unusedGraph M₁).degree v = C - 2 ∧ mult ⊤ χ₁ v = y + 1) ∨
      ((unusedGraph M₁).degree v = C - 4 ∧ mult ⊤ χ₁ v = y + 1 + 2) := by
    intro v
    have h := hdeg2 v
    rcases hmult1' v with h' | h' <;> rw [h'] at h ⊢
    · left; exact ⟨(x4_deg hBC hC4).1 h, rfl⟩
    · right; exact ⟨(x4_deg hBC hC4).2 h, rfl⟩
  have hlo : (univ.filter fun v => (unusedGraph M₁).degree v = C - 4).card = r := by
    rw [← hcnt']
    refine congrArg Finset.card (filter_congr fun v _ => ?_)
    rcases hdeg2' v with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨fun h => absurd h hC24, fun h => absurd h hyne⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  have hhi : (univ.filter fun v => (unusedGraph M₁).degree v = C - 2).card = B - r := by
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (BType (col3 A B C))))
      (fun v => (unusedGraph M₁).degree v = C - 4)
    rw [card_univ, hcB, hlo] at hsplit
    have hfe : (univ.filter fun v => (unusedGraph M₁).degree v = C - 2) =
        univ.filter fun v => ¬ (unusedGraph M₁).degree v = C - 4 := by
      refine filter_congr fun v _ => ?_
      rcases hdeg2' v with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact ⟨fun _ h => absurd h hC24, fun _ => rfl⟩
      · exact ⟨fun h => absurd h.symm hC24, fun h => absurd rfl h⟩
    rw [hfe]
    exact sub_of_add' hsplit
  -- BKLS with `k₀ = C - 1`
  obtain ⟨v₀, hv₀⟩ : ∃ v, (unusedGraph M₁).degree v = C - 2 := by
    have : 0 < (univ.filter fun v => (unusedGraph M₁).degree v = C - 2).card := by
      rw [hhi]; exact lt_trans Nat.zero_lt_one hBr2
    obtain ⟨v, hv⟩ := card_pos.1 this
    exact ⟨v, (mem_filter.1 hv).2⟩
  have hΔ : C - 2 ≤ (unusedGraph M₁).maxDegree := hv₀ ▸ (unusedGraph M₁).degree_le_maxDegree v₀
  have hVD : VDColourable (unusedGraph M₁) (C - 1 + 1) := by
    refine hBK (BType (col3 A B C)) (unusedGraph M₁) (C - 1) (fun v => ?_) (hC6.trans hΔ) ?_ ?_ ?_
    · rcases hdeg2' v with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact hd5'
      · exact hd5
    · rw [hcB]
      have h1 : C - 6 ≤ (unusedGraph M₁).maxDegree - 4 := hC64 ▸ Nat.sub_le_sub_right hΔ 4
      exact h2B.trans (Nat.pow_le_pow_left h1 2)
    · intro d
      by_cases hd2 : d = C - 2
      · subst hd2
        rw [hhi, hC21, Nat.choose_symm hC1, Nat.choose_one_right]
        exact hBr
      · by_cases hd4 : d = C - 4
        · subst hd4
          rw [hlo, hC43, Nat.choose_symm hC3]
          exact hr1.trans (choose_three_ge (C - 1) hC7)
        · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun v _ => by
            rcases hdeg2' v with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
            · exact fun h => hd2 h.symm
            · exact fun h => hd4 h.symm)]
          exact Nat.zero_le _
    · intro k' hk'
      refine ⟨C - 2, ?_⟩
      rw [hhi]
      rcases Nat.lt_or_ge k' (C - 2) with h | h
      · rw [Nat.choose_eq_zero_of_lt h]; exact lt_trans Nat.zero_lt_one hBr2
      · rw [hC12] at hk'
        have : k' = C - 2 := le_antisymm (Nat.le_of_lt_succ hk') h
        rw [this, Nat.choose_self]; exact hBr2
  -- RS: an equitable vertex-distinguishing colouring by the `C` points
  obtain ⟨c₂, hc₂p, hc₂vd, hc₂e⟩ := hRS (BType (col3 A B C)) (unusedGraph M₁) (C - 1 + 1) hVD
  let eC : CType (col3 A B C) ≃ Fin (C - 1 + 1) :=
    Fintype.equivFinOfCardEq (by rw [hcC]; exact hCcard)
  have hχ₂ : ProperOn (unusedGraph M₁).edgeFinset (eC.symm ∘ c₂) :=
    properOn_comp hc₂p eC.symm.injective
  have hpres : ∀ j, present (unusedGraph M₁) (eC.symm ∘ c₂) j =
      (present (unusedGraph M₁) c₂ j).image eC.symm := fun j => by
    simp only [present, image_image]
  refine master_core hadm hC0 hAC hAB ht hρ6 h76 χ₁ M₁ hχ₁' hM₁ hM₁d
    (fun v => by rcases hmult1' v with h | h <;> rw [h]; exacts [hloa, hlob]) (eC.symm ∘ c₂) hχ₂
    ?_ ?_
  · intro x y'
    rw [colourClass_equiv, colourClass_equiv]; exact hc₂e (eC x) (eC y')
  · intro j j' hjj _ heq
    apply hc₂vd j j' hjj
    have hp : present (unusedGraph M₁) (eC.symm ∘ c₂) j =
        present (unusedGraph M₁) (eC.symm ∘ c₂) j' := by
      rw [← Finset.sdiff_sdiff_eq_self (subset_univ (present (unusedGraph M₁) (eC.symm ∘ c₂) j)),
        ← Finset.sdiff_sdiff_eq_self (subset_univ (present (unusedGraph M₁) (eC.symm ∘ c₂) j'))]
      exact congrArg (univ \ ·) heq
    rw [hpres, hpres] at hp
    exact image_injective eC.symm.injective hp

end CDRBicolour.Master
