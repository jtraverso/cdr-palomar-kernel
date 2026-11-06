/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V25.DeleteCore
@[expose] public section

/-!
# V48 — the V25 post-sampling deletion package as a DETERMINISTIC statement about a given `W`

`S07V25.S07_core_delete` packages the deletion conclusions together with the existential core
of `S07_core_H3H4`, so it cannot be applied to a core produced by a different (enlarged)
sampling argument. `core_delete_det` isolates its deterministic part: for ANY `W` satisfying the
V25 core guarantees (size, pools `≥ qαn/2`, hinges at half the mean, robust odd routes with
window `ε`) and any `S` with `|S| ≤ σ n`, `σ = S07V25.sigmaOf α q ε h`, the set `W ∖ S` satisfies
all seven conclusions of `S07_core_delete`. The proof is the V25 proof, unchanged, with the
sampling step removed; nothing new is assumed.
-/

open Finset

namespace S07V48

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25

open Classical in
/-- **V25 post-sampling deletion, deterministic form** -/
theorem core_delete_det {α q ε : ℝ} {h t : ℕ} (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hε : 0 < ε) (ht : Odd t)
    {V I : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} (hH4 : HingeCond G lab F α h)
    (hn9 : (9 : ℝ) < q * α * Fintype.card V) {W : Finset V}
    (hW1 : q * Fintype.card V / 2 ≤ W.card) (hW2 : (W.card : ℝ) < 2 * q * Fintype.card V)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card)
    (hhinge : ∀ u v a' b' : V, HingeTest G lab F u v a' b' →
      α * q ^ (hOrd hH4 u v a' b' - 4) *
          (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
        ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
          freeV u v a' b' J ⊆ W).card)
    (hroute : ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
      (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
      (d : ℝ) ≤ ε * Fintype.card V →
      ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
          (colG G lab F) v x y →
        ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
          (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
          ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)))
    (S : Finset V) (hS : (S.card : ℝ) ≤ sigmaOf α q ε h * Fintype.card V) :
    q * Fintype.card V / 4 ≤ (W \ S).card ∧
    ((W \ S).card : ℝ) < 2 * q * Fintype.card V ∧
    (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 4 ≤ ((commonNbrs G lab k u v) ∩ (W \ S)).card) ∧
    (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
      α * q ^ (hOrd hH4 u v a' b' - 4) *
          (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 4 ≤
        ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
          freeV u v a' b' J ⊆ W \ S).card) ∧
    (∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
      (Z.card : ℝ) ≤ ε / 2 * Fintype.card V → (∀ u, B.degree u ≤ d) →
      (d : ℝ) ≤ ε * Fintype.card V →
      ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
          (colG G lab F) v x y →
        ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W \ S ∧
          (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
          ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) ∧
    ∀ v, ∀ C ∈ activeComps G lab F v,
      (∀ x ∈ C, q * α * Fintype.card V / 4 ≤
        (univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ (W \ S)).card) ∧
      (∀ x ∈ C ∩ (W \ S), ∀ y ∈ C ∩ (W \ S),
        ∃ p : (link G lab F v).Walk x y, ∀ z ∈ p.support, z ∈ C ∩ (W \ S)) ∧
      (¬ IsBip G lab F (v, C) → ¬ IsBip G lab F (v, C ∩ (W \ S))) := by
  set σ := sigmaOf α q ε h with hσdef
  have hσ := sigmaOf_pos hα hq hε h
  have hσ1 : σ ≤ ε / 2 := min_le_left _ _
  have hσ2 : σ ≤ q / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ3 : σ ≤ q * α / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσ4 : σ ≤ α * q ^ h / (4 * 2 ^ (h.choose 2)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set n := Fintype.card V with hndef
  have hnR : (0 : ℝ) < n := by
    by_contra hc; push_neg at hc
    have : q * α * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hSW := card_sdiff_ge W S
  have hpool' : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      q * α * n / 4 ≤ ((commonNbrs G lab k u v) ∩ (W \ S)).card := by
    intro u v huv k hk
    have h1 := hpool u v huv k hk
    have h2 := card_sdiff_ge ((commonNbrs G lab k u v) ∩ W) S
    have h3 : ((commonNbrs G lab k u v) ∩ W) \ S ⊆ (commonNbrs G lab k u v) ∩ (W \ S) := by
      intro z hz; simp only [mem_sdiff, mem_inter] at hz ⊢; tauto
    have h4 : ((((commonNbrs G lab k u v) ∩ W) \ S).card : ℝ) ≤
        ((commonNbrs G lab k u v) ∩ (W \ S)).card := by exact_mod_cast card_le_card h3
    have : σ * n ≤ q * α / 4 * n := mul_le_mul_of_nonneg_right hσ3 hnR.le
    linarith
  -- routes (S absorbed into the forbidden set)
  have hroute' : ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
      (Z.card : ℝ) ≤ ε / 2 * n → (∀ u, B.degree u ≤ d) → (d : ℝ) ≤ ε * n →
      ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
          (colG G lab F) v x y →
        ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W \ S ∧
          (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
          ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)) := by
    intro Z B _ d hZ hB hd v x y hadm
    have hZS : ((Z ∪ S).card : ℝ) ≤ ε * n := by
      have := card_union_le Z S
      have h' : ((Z ∪ S).card : ℝ) ≤ Z.card + S.card := by exact_mod_cast this
      have : σ * n ≤ ε / 2 * n := mul_le_mul_of_nonneg_right hσ1 hnR.le
      linarith
    obtain ⟨p, hp, hpW, hpZ, hpB⟩ := hroute (Z ∪ S) B d hZS hB hd v x y hadm
    refine ⟨p, hp, fun z hz => ?_, fun i hi => hpZ i (mem_union_left _ hi), hpB⟩
    rw [mem_intlSet] at hz
    obtain ⟨i, rfl⟩ := hz
    refine mem_sdiff.2 ⟨hpW ((mem_intlSet _ _ _).2 ⟨i, rfl⟩), fun hS' => hpZ i (mem_union_right _ hS')⟩
  -- plentiful neighbours
  have hnbr : ∀ v, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, q * α * n / 4 ≤
      (univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ (W \ S)).card := by
    intro v C hC x hx
    obtain ⟨x0, hx0, rfl⟩ := mem_activeComps.1 hC
    obtain ⟨y, hxy⟩ := comp_active hx0 hx
    obtain ⟨hvx, hF⟩ := link_root_ne hxy
    have h1 := hpool' v x hvx (lab y) hF
    have hsub : (commonNbrs G lab (lab y) v x) ∩ (W \ S) ⊆
        univ.filter fun z => (link G lab F v).Adj x z ∧ z ∈ comp G lab F v x0 ∩ (W \ S) := by
      intro z hz
      rw [mem_inter] at hz
      have hadj := commonNbr_link_adj hxy hz.1
      simp only [mem_filter, mem_univ, true_and, mem_inter]
      exact ⟨hadj, comp_closed v x0 x z hx hadj, hz.2⟩
    exact h1.trans (by exact_mod_cast card_le_card hsub)
  have hnbr_ex : ∀ v, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, ∀ w : V,
      ∃ y, (link G lab F v).Adj x y ∧ y ∈ C ∩ (W \ S) ∧ y ≠ w := by
    intro v C hC x hx w
    have h1 := hnbr v C hC x hx
    have h2 : (1 : ℝ) < ((univ.filter fun y => (link G lab F v).Adj x y ∧
        y ∈ C ∩ (W \ S)).card : ℝ) := by linarith
    have h3 : 1 < (univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ (W \ S)).card := by
      exact_mod_cast h2
    obtain ⟨y, hy, hyw⟩ := Finset.exists_mem_ne h3 w
    simp only [mem_filter, mem_univ, true_and] at hy
    exact ⟨y, hy.1, hy.2, hyw⟩
  -- routes inside `C ∩ W'` for admissible pairs
  have hpathC : ∀ v, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C ∩ (W \ S), ∀ y ∈ C ∩ (W \ S),
      AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F) v x y →
      ∃ p ∈ pathsLen (link G lab F v) t x y, ∀ z ∈ p.support, z ∈ C ∩ (W \ S) := by
    intro v C hC x hx y hy hadm
    obtain ⟨p, hp, hpW, -, -⟩ := hroute' ∅ ⊥ 0 (by simp; positivity) (fun u => by simp)
      (by simp; positivity) v x y hadm
    obtain ⟨x0, -, rfl⟩ := mem_activeComps.1 hC
    refine ⟨p, hp, fun z hz => mem_inter.2 ⟨walk_support_comp p (mem_inter.1 hx).1 z hz, ?_⟩⟩
    rcases support_of_pathsLen hp hz with rfl | rfl | h'
    exacts [(mem_inter.1 hx).2, (mem_inter.1 hy).2, hpW h']
  refine ⟨?_, lt_of_le_of_lt (by exact_mod_cast card_le_card sdiff_subset) hW2, hpool',
    ?_, hroute', fun v C hC => ⟨hnbr v C hC, ?_, ?_⟩⟩
  · have : σ * n ≤ q / 4 * n := mul_le_mul_of_nonneg_right hσ2 hnR.le
    linarith
  · -- hinges
    intro u v a' b' hT
    obtain ⟨hi6, hih, -⟩ := hOrd_spec hH4 hT
    set i := hOrd hH4 u v a' b'
    have h1 := hhinge u v a' b' hT
    have h2 := hinge_delete (G := G) (lab := lab) (F := F) (roots_distinct hT) i W S
    have hp5 : (n : ℝ) ^ (i - 4) = n * (n : ℝ) ^ (i - 5) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 ≤ (n : ℝ) ^ (i - 5) := by positivity
    have hC2 : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (h.choose 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
    have hqh : q ^ h ≤ q ^ (i - 4) := pow_le_pow_of_le_one hq.le hq1 (by omega)
    have hloss : (S.card : ℝ) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5)) ≤
        α * q ^ (i - 4) * (n : ℝ) ^ (i - 4) / 4 := by
      have e1 : (S.card : ℝ) * 2 ^ (i.choose 2) ≤ σ * n * 2 ^ (h.choose 2) :=
        mul_le_mul hS hC2 (by positivity) (by positivity)
      have e2 : σ * 2 ^ (h.choose 2) ≤ α * q ^ h / 4 := by
        rw [le_div_iff₀ (by positivity)] at hσ4; nlinarith
      have e3 : α * q ^ h / 4 ≤ α * q ^ (i - 4) / 4 := by
        have := mul_le_mul_of_nonneg_left hqh hα.le; linarith
      calc (S.card : ℝ) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5))
          = ((S.card : ℝ) * 2 ^ (i.choose 2)) * (n : ℝ) ^ (i - 5) := by ring
        _ ≤ (σ * n * 2 ^ (h.choose 2)) * (n : ℝ) ^ (i - 5) := mul_le_mul_of_nonneg_right e1 hpos
        _ = (σ * 2 ^ (h.choose 2)) * (n * (n : ℝ) ^ (i - 5)) := by ring
        _ ≤ (α * q ^ (i - 4) / 4) * (n * (n : ℝ) ^ (i - 5)) :=
            mul_le_mul_of_nonneg_right (e2.trans e3) (by positivity)
        _ = α * q ^ (i - 4) * (n : ℝ) ^ (i - 4) / 4 := by rw [hp5]; ring
    linarith
  · -- component survival
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_activeComps.1 hC
    by_cases hxy : x = y
    · subst hxy; exact ⟨.nil, by simpa using hx⟩
    by_cases hcol : IsBip G lab F (v, comp G lab F v x0) → colG G lab F v x ≠ colG G lab F v y
    · obtain ⟨p, -, hp⟩ := hpathC v _ hC x hx y hy ⟨_, hC, (mem_inter.1 hx).1, (mem_inter.1 hy).1,
        hxy, hcol⟩
      exact ⟨p, hp⟩
    · push_neg at hcol
      obtain ⟨hb, hceq⟩ := hcol
      obtain ⟨z, hxz, hz, -⟩ := hnbr_ex v _ hC x (mem_inter.1 hx).1 x
      have hczx : colG G lab F v x ≠ colG G lab F v z :=
        colG_proper hb (mem_inter.1 hx).1 (mem_inter.1 hz).1 hxz
      have hzy : z ≠ y := by rintro rfl; exact hczx hceq
      obtain ⟨p, -, hp⟩ := hpathC v _ hC z hz y hy ⟨_, hC, (mem_inter.1 hz).1,
        (mem_inter.1 hy).1, hzy, fun _ => by rw [← hceq]; exact hczx.symm⟩
      refine ⟨.cons hxz p, fun w hw => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      exacts [hx, hp w hw]
  · -- odd components stay odd
    intro hnb ⟨c, hc⟩
    obtain ⟨x0, hx0, rfl⟩ := mem_activeComps.1 hC
    have hx0C : x0 ∈ comp G lab F v x0 := by simp [comp]
    obtain ⟨x, -, hx, -⟩ := hnbr_ex v _ hC x0 hx0C x0
    obtain ⟨y, hxy, hy, -⟩ := hnbr_ex v _ hC x (mem_inter.1 hx).1 x
    obtain ⟨z, hyz, hz, hzx⟩ := hnbr_ex v _ hC y (mem_inter.1 hy).1 x
    obtain ⟨p, hp, hps⟩ := hpathC v _ hC x hx z hz ⟨_, hC, (mem_inter.1 hx).1,
      (mem_inter.1 hz).1, hzx.symm, fun h' => absurd h' hnb⟩
    have hc' : ∀ u ∈ ((comp G lab F v x0 ∩ (W \ S) : Finset V) : Set V),
        ∀ w ∈ ((comp G lab F v x0 ∩ (W \ S) : Finset V) : Set V),
        (link G lab F v).Adj u w → c u ≠ c w := fun u hu w hw huw => hc u hu w hw huw
    have hlen : p.length = t := by
      simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1
    have e1 := col_parity hc' p (fun w hw => hps w hw)
    have e2 := col_parity hc' (.cons hxy (.cons hyz .nil) : (link G lab F v).Walk x z)
      (fun w hw => by
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        exacts [hx, hy, hz])
    have hev : Even (SimpleGraph.Walk.cons hxy (.cons hyz .nil) : (link G lab F v).Walk x z).length :=
      ⟨1, rfl⟩
    rw [hlen] at e1
    have := e1.1 (e2.2 hev)
    exact (Nat.not_even_iff_odd.2 ht) this

end S07V48
