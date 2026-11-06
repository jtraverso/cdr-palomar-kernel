/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork

/-!
# Degree facts in `Δ`-critical graphs and CCJS Lemma 2.5

* `val_crit`, `deg_add`: VAL for every edge of a `Δ`-critical graph.
* Counting colours for a colouring of `G − ab` with `d(b) = Δ`: `|A| = Δ − d(a) + 2`, and each
  vertex has at most `d(a) − 2` edges coloured outside `A`.
* `degree_dichotomy` (CCJS Lemma 2.5, first part) and `card_missing_inA_le_one` (second part).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### VAL in `Δ`-critical graphs -/

theorem val_crit (hG : IsDeltaCritical G) {x y : V} (hxy : G.Adj x y) :
    G.maxDegree + 1 ≤ G.degree y +
      #((G.neighborFinset x).filter fun z => z ≠ y ∧ G.degree z = G.maxDegree) := by
  obtain ⟨c, hcm⟩ := exists_colMinus_of_colorable hxy (hG.2.2 s(x, y) (G.mem_edgeSet.2 hxy))
  exact val hG.2.1 hcm

theorem card_maxNbrs_le {x y : V} (hxy : G.Adj x y) :
    #((G.neighborFinset x).filter fun z => z ≠ y ∧ G.degree z = G.maxDegree) + 1 ≤
      G.degree x := by
  have hsub : ((G.neighborFinset x).filter fun z => z ≠ y ∧ G.degree z = G.maxDegree) ⊆
      (G.neighborFinset x).erase y := fun z hz => by
    simp only [mem_filter] at hz
    exact mem_erase.2 ⟨hz.2.1, hz.1⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hxy), card_neighborFinset_eq_degree] at h1
  have : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).2 ⟨y, hxy⟩
  omega

/-- The degrees of adjacent vertices of a `Δ`-critical graph sum to at least `Δ + 2`. -/
theorem deg_add (hG : IsDeltaCritical G) {x y : V} (hxy : G.Adj x y) :
    G.maxDegree + 2 ≤ G.degree x + G.degree y := by
  have := val_crit hG hxy
  have := card_maxNbrs_le hxy
  omega

/-- Every non-isolated vertex has a neighbour of maximum degree other than a given neighbour. -/
theorem exists_maxdeg_nbr (hG : IsDeltaCritical G) {x y : V} (hxy : G.Adj x y) :
    ∃ z, G.Adj x z ∧ z ≠ y ∧ G.degree z = G.maxDegree := by
  have h1 := val_crit hG hxy
  have h2 := G.degree_le_maxDegree y
  obtain ⟨z, hz⟩ : ((G.neighborFinset x).filter fun z => z ≠ y ∧ G.degree z = G.maxDegree).Nonempty
    := card_pos.1 (by omega)
  simp only [mem_filter, mem_neighborFinset] at hz
  exact ⟨z, hz.1, hz.2.1, hz.2.2⟩

/-! ### Counting colours -/

section Count

variable {c : PEC G (Fin G.maxDegree)} {a b : V}

theorem IsColMinus.card_missing_end (hcm : IsColMinus c a b) {v : V} (hv : v = a ∨ v = b) :
    #(missing c v) + G.degree v = G.maxDegree + 1 := by
  have e1 := card_missing_add_colNbrs c v
  have e2 := hcm.card_colNbrs v
  simp only [hv, if_true] at e2
  omega

theorem IsColMinus.card_missing_other (hcm : IsColMinus c a b) {v : V} (hva : v ≠ a)
    (hvb : v ≠ b) : #(missing c v) + G.degree v = G.maxDegree := by
  have e1 := card_missing_add_colNbrs c v
  have e2 := hcm.card_colNbrs v
  simp only [hva, hvb, or_self, if_false, add_zero] at e2
  omega

open Classical in
/-- Colours outside `A`. -/
noncomputable def nonA (c : PEC G (Fin G.maxDegree)) (a b : V) : Finset (Fin G.maxDegree) :=
  univ.filter fun θ => ¬ InA c a b θ

theorem mem_nonA {θ : Fin G.maxDegree} : θ ∈ nonA c a b ↔ ¬ InA c a b θ := by
  classical
  simp [nonA]

theorem IsColMinus.card_nonA (hG : IsClassTwo G) (hcm : IsColMinus c a b) :
    #(nonA c a b) + #(missing c a) + #(missing c b) = G.maxDegree := by
  obtain ⟨hdis, -⟩ := hcm.ab_facts hG
  have hd : Disjoint (missing c a) (missing c b) :=
    disjoint_left.2 fun θ ha hb => hdis θ (mem_missing.1 ha) (mem_missing.1 hb)
  have hun : nonA c a b ∪ (missing c a ∪ missing c b) = univ := by
    ext θ
    simp only [mem_union, mem_nonA, mem_missing, mem_univ, iff_true, InA]
    tauto
  have hd2 : Disjoint (nonA c a b) (missing c a ∪ missing c b) := by
    refine disjoint_left.2 fun θ h1 h2 => ?_
    rw [mem_nonA] at h1
    rcases mem_union.1 h2 with h | h
    · exact h1 (Or.inl (mem_missing.1 h))
    · exact h1 (Or.inr (mem_missing.1 h))
  have := card_union_of_disjoint hd2
  rw [hun, card_union_of_disjoint hd, card_univ, Fintype.card_fin] at this
  omega

open Classical in
/-- Edges at `x` coloured outside `A`. -/
noncomputable def badNbrs (c : PEC G (Fin G.maxDegree)) (a b x : V) : Finset V :=
  univ.filter fun w => ∃ θ, c.col x w = some θ ∧ ¬ InA c a b θ

theorem mem_badNbrs {x w : V} :
    w ∈ badNbrs c a b x ↔ ∃ θ, c.col x w = some θ ∧ ¬ InA c a b θ := by
  classical
  simp [badNbrs]

theorem card_badNbrs_le (x : V) : #(badNbrs c a b x) ≤ #(nonA c a b) := by
  classical
  have hinj : Set.InjOn (fun w => c.col x w) (badNbrs c a b x : Set V) := by
    intro w hw w' hw' he
    obtain ⟨θ, h1, -⟩ := mem_badNbrs.1 (mem_coe.1 hw)
    obtain ⟨θ', h2, -⟩ := mem_badNbrs.1 (mem_coe.1 hw')
    simp only at he
    exact c.col_proper h1 (he.symm.trans h1)
  have hsub : (badNbrs c a b x).image (fun w => c.col x w) ⊆ (nonA c a b).image some := by
    intro o ho
    obtain ⟨w, hw, rfl⟩ := mem_image.1 ho
    obtain ⟨θ, h1, h2⟩ := mem_badNbrs.1 hw
    exact mem_image.2 ⟨θ, mem_nonA.2 h2, h1.symm⟩
  have := card_le_card hsub
  rwa [card_image_of_injOn hinj, card_image_of_injective _ (Option.some_injective _)] at this

end Count

theorem card_erase_add (s : Finset V) (x : V) :
    #(s.erase x) + (if x ∈ s then 1 else 0) = #s := by
  split_ifs with h
  · rw [card_erase_of_mem h]
    have := card_pos.2 ⟨x, h⟩
    omega
  · rw [erase_eq_of_notMem h]; rfl

theorem card_univ_erase3 {a b v : V} (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) :
    #(((univ.erase a).erase b).erase v) + 3 = Fintype.card V := by
  rw [card_erase_of_mem (by simp [hav.symm, hbv.symm]), card_erase_of_mem (by simp [hab.symm]),
    card_erase_of_mem (mem_univ a), card_univ]
  have : 3 ≤ Fintype.card V := by
    have := card_le_univ ({a, b, v} : Finset V)
    rw [card_insert_of_notMem (by simp [hab, hav]), card_insert_of_notMem (by simp [hbv]),
      card_singleton] at this
    exact this
  omega

/-- A colour of `A` on the edge `xw`. -/
def Good {k : ℕ} (c : PEC G (Fin k)) (a b x w : V) : Prop :=
  ∃ θ, c.col x w = some θ ∧ InA c a b θ

theorem not_good_mem_bad {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b)
    {x w : V} (hxw : G.Adj x w) (hne : s(x, w) ≠ s(a, b)) (h : ¬ Good c a b x w) :
    w ∈ badNbrs c a b x := by
  obtain ⟨θ, hθ⟩ := Option.ne_none_iff_exists'.1 (hcm.total x w hxw hne)
  exact mem_badNbrs.2 ⟨θ, hθ, fun hA => h ⟨θ, hθ, hA⟩⟩

theorem sym2_ne_ab {a b x w : V} (h : x ≠ a ∧ x ≠ b) : s(x, w) ≠ s(a, b) := by
  intro he
  rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h.1 rfl
  · exact h.2 rfl

/-- **Two-centre count.** If `v ∉ {a, b}` and the edge `bv` (if any) is not coloured in `A`,
then for `d(v) + Δ` large there is `w ∉ {a, b, v}` adjacent to `b` and `v` with both edges
coloured in `A`. -/
theorem exists_good_common₂ (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {v : V} (hva : v ≠ a) (hvb : v ≠ b)
    (hbv : G.Adj b v → ¬ Good c a b b v)
    (hcnt : Fintype.card V + 2 * (#(nonA c a b) + 2) + (if G.Adj v a then 1 else 0) ≤
      G.degree v + G.degree b + 5) :
    ∃ w, w ≠ a ∧ w ≠ b ∧ w ≠ v ∧ G.Adj b w ∧ G.Adj v w ∧ Good c a b b w ∧ Good c a b v w := by
  classical
  have hab : a ≠ b := hcm.adj.ne
  set A := ((G.neighborFinset v).erase a).erase b with hA
  set B := ((G.neighborFinset b).erase a).erase v with hB
  set U := ((univ.erase a).erase b).erase v with hU
  have hU3 : #U + 3 = Fintype.card V := card_univ_erase3 hab hva.symm hvb.symm
  have hAB : A ∪ B ⊆ U := by
    intro w hw
    simp only [hA, hB, hU, mem_union, mem_erase, mem_neighborFinset, mem_univ, and_true] at hw ⊢
    rcases hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨fun e => (e ▸ h3).ne rfl, h1, h2⟩
    · exact ⟨h1, fun e => (e ▸ h3).ne rfl, h2⟩
  have hcardA : #A + (if b ∈ (G.neighborFinset v).erase a then 1 else 0) =
      #((G.neighborFinset v).erase a) := card_erase_add _ b
  have hcardA' := card_erase_add (G.neighborFinset v) a
  have hcardB : #B + (if v ∈ (G.neighborFinset b).erase a then 1 else 0) =
      #((G.neighborFinset b).erase a) := card_erase_add _ v
  have hcardB' := card_erase_add (G.neighborFinset b) a
  rw [card_neighborFinset_eq_degree] at hcardA' hcardB'
  have haNb : a ∈ G.neighborFinset b := (mem_neighborFinset _ _ _).2 hcm.adj.symm
  have hinter := card_union_add_card_inter A B
  have hunion := card_le_card hAB
  -- the bad vertices inside `A ∩ B`
  set bb := badNbrs c a b b
  set bv := badNbrs c a b v
  have hbad_b : #bb ≤ #(nonA c a b) := card_badNbrs_le b
  have hbad_v : #bv ≤ #(nonA c a b) := card_badNbrs_le v
  have hsubb : (A ∩ B) ∩ bb ⊆ bb.erase v := fun w hw => by
    simp only [mem_inter, hB, mem_erase] at hw
    exact mem_erase.2 ⟨hw.1.2.1, hw.2⟩
  have hsubv : (A ∩ B) ∩ bv ⊆ bv.erase b := fun w hw => by
    simp only [mem_inter, hA, mem_erase] at hw
    exact mem_erase.2 ⟨hw.1.1.1, hw.2⟩
  have hcb := card_erase_add bb v
  have hcv := card_erase_add bv b
  have e1 := card_le_card hsubb
  have e2 := card_le_card hsubv
  -- membership of `v`, `b` in each other's bad sets when adjacent
  have hadj_bad : G.Adj b v → v ∈ bb ∧ b ∈ bv := fun h => by
    refine ⟨not_good_mem_bad hcm h (by rw [Sym2.eq_swap]; exact sym2_ne_ab ⟨hva, hvb⟩) (hbv h),
      ?_⟩
    refine not_good_mem_bad hcm h.symm (sym2_ne_ab ⟨hva, hvb⟩) fun ⟨θ, hθ, hθA⟩ =>
        hbv h ⟨θ, by rw [c.col_symm]; exact hθ, hθA⟩
  -- the good vertices
  set Gd := (A ∩ B) \ (bb ∪ bv) with hGdef
  have hcover : A ∩ B ⊆ Gd ∪ ((A ∩ B) ∩ bb) ∪ ((A ∩ B) ∩ bv) := by
    intro w hw
    by_cases h1 : w ∈ bb
    · exact mem_union_left _ (mem_union_right _ (mem_inter.2 ⟨hw, h1⟩))
    by_cases h2 : w ∈ bv
    · exact mem_union_right _ (mem_inter.2 ⟨hw, h2⟩)
    exact mem_union_left _ (mem_union_left _ (mem_sdiff.2 ⟨hw, by simp [h1, h2]⟩))
  have e3 := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hGd : 0 < #Gd := by
    have hvb' : (v ∈ G.neighborFinset b) ↔ G.Adj b v := mem_neighborFinset _ _ _
    have hbv' : (b ∈ G.neighborFinset v) ↔ G.Adj b v := by
      rw [mem_neighborFinset]; exact ⟨fun h => h.symm, fun h => h.symm⟩
    have hav' : (a ∈ G.neighborFinset v) ↔ G.Adj v a := mem_neighborFinset _ _ _
    have haA : (b ∈ (G.neighborFinset v).erase a) ↔ G.Adj b v := by
      rw [mem_erase, hbv']; exact ⟨fun h => h.2, fun h => ⟨hab.symm, h⟩⟩
    have hvB : (v ∈ (G.neighborFinset b).erase a) ↔ G.Adj b v := by
      rw [mem_erase, hvb']; exact ⟨fun h => h.2, fun h => ⟨hva, h⟩⟩
    rw [if_pos haNb] at hcardB'
    simp only [hav'] at hcardA'
    by_cases hadj : G.Adj b v
    · obtain ⟨h1, h2⟩ := hadj_bad hadj
      rw [if_pos (haA.2 hadj)] at hcardA
      rw [if_pos (hvB.2 hadj)] at hcardB
      rw [if_pos h1] at hcb
      rw [if_pos h2] at hcv
      split_ifs at hcardA' hcnt <;> omega
    · rw [if_neg (fun h => hadj (haA.1 h))] at hcardA
      rw [if_neg (fun h => hadj (hvB.1 h))] at hcardB
      split_ifs at hcardA' hcnt hcb hcv <;> omega
  obtain ⟨w, hw⟩ := card_pos.1 hGd
  simp only [hGdef, mem_sdiff, mem_inter, mem_union, not_or, hA, hB, mem_erase,
    mem_neighborFinset] at hw
  obtain ⟨⟨⟨hwb, hwa, hvw⟩, hwv, -, hbw⟩, hwbb, hwbv⟩ := hw
  refine ⟨w, hwa, hwb, hwv, hbw, hvw, ?_, ?_⟩
  · by_contra hn
    exact hwbb (not_good_mem_bad hcm hbw (by rw [Sym2.eq_swap]; exact sym2_ne_ab ⟨hwa, hwb⟩) hn)
  · by_contra hn
    exact hwbv (not_good_mem_bad hcm hvw (sym2_ne_ab ⟨hva, hvb⟩) hn)

end Overfull
