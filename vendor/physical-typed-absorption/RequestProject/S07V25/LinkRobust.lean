/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.HingePath
public import RequestProject.S07V25.RobustAbstract

@[expose] public section

/-!
# V25 — the link `L_v` is locally robust (from the ORIGINAL H4) and has linear degrees (H3)

* `hinge_free_deg2` — hinges of order `i` with two prescribed free vertices: `≤ 2^(i choose 2) n^(i-6)`.
* `good_hinge` — if `(|S| + 3d) 2^(i choose 2) n^(i-5) < α n^(i-4) ≤ #hinges`, some hinge has
  no free vertex in `S` and no edge of `B` (max degree `≤ d`) between two of its vertices one of
  which is free.
* `link_evenRobust` — from `HingeCond G lab F α h` (H4, unchanged): if
  `(s + 3d) 2^(h choose 2) < α n` and `n > 0`, then `EvenRobustLocal (link G lab F v) s d` for
  every root `v`.
* `link_degree_ge` — from `CommonNbrCond G lab F α` (H3, unchanged): every non-isolated vertex
  of `L_v` has `L_v`-degree `≥ α n`.
-/

open Finset Classical

namespace S07V25

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24

variable {V I : Type*} [Fintype V]

lemma hinge_free_deg2 {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) (i : ℕ) {x y : V} (hxy : x ≠ y) :
    (((hinges G lab F u v a b i).filter fun J => x ∈ freeV u v a b J ∧ y ∈ freeV u v a b J).card
      : ℝ) ≤ 2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 6) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  by_cases hz : x ∈ ({u, v, a, b} : Finset V) ∨ y ∈ ({u, v, a, b} : Finset V)
  · have : ((hinges G lab F u v a b i).filter fun J =>
        x ∈ freeV u v a b J ∧ y ∈ freeV u v a b J) = ∅ := by
      apply Finset.filter_false_of_mem; intro J _ hJ
      simp only [freeV, Finset.mem_sdiff] at hJ
      rcases hz with hz | hz
      exacts [hJ.1.2 hz, hJ.2.2 hz]
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · push_neg at hz
    have hW : Disjoint ({x, y} : Finset V) {u, v, a, b} := by
      rw [Finset.disjoint_left]; intro z hz'
      simp only [mem_insert, mem_singleton] at hz'
      rcases hz' with rfl | rfl
      exacts [hz.1, hz.2]
    have := S10V23.card_hinges_forced huv hua hva hub hvb hab i {x, y} hW
      ((hinges G lab F u v a b i).filter fun J => x ∈ freeV u v a b J ∧ y ∈ freeV u v a b J)
      (Finset.filter_subset _ _)
      (fun J hJ => by
        simp only [Finset.mem_filter, freeV, Finset.mem_sdiff] at hJ
        intro z hz'
        simp only [mem_insert, mem_singleton] at hz'
        rcases hz' with rfl | rfl
        exacts [hJ.2.1.1, hJ.2.2.1])
    have hc : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy
    rw [hc] at this
    convert this using 1

/-- edges of `B` from a free vertex to a free vertex or to `a`, `b` -/
def BadB (B : Finset (Sym2 V)) (u v a b : V) (J : Finset (Sym2 V)) : Prop :=
  ∃ x y, s(x, y) ∈ B ∧ x ≠ y ∧ x ∈ freeV u v a b J ∧ (y ∈ freeV u v a b J ∨ y = a ∨ y = b)

lemma card_pairs_le (B : Finset (Sym2 V)) (d : ℕ) (hB : ∀ x, degB B x ≤ d) :
    (((univ ×ˢ univ).filter (fun p : V × V => s(p.1, p.2) ∈ B ∧ p.1 ≠ p.2)).card : ℝ) ≤
      Fintype.card V * d := by
  have h1 : ((univ ×ˢ univ).filter (fun p : V × V => s(p.1, p.2) ∈ B ∧ p.1 ≠ p.2)) ⊆
      univ.biUnion (fun x => (univ.filter (fun y => s(x, y) ∈ B)).image (fun y => (x, y))) := by
    intro p hp
    simp only [mem_filter, mem_product, mem_univ, true_and] at hp
    exact mem_biUnion.2 ⟨p.1, mem_univ _, mem_image.2 ⟨p.2, by simp [hp.1], rfl⟩⟩
  have h2 : ∀ x, (univ.filter (fun y => s(x, y) ∈ B)).card ≤ d := by
    intro x
    refine le_trans ?_ (hB x)
    unfold degB
    refine Finset.card_le_card_of_injOn (fun y => s(x, y)) ?_ ?_
    · intro y hy; simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
      simp [hy]
    · intro y _ y' _ h; exact Sym2.congr_right.1 h
  have := (card_le_card h1).trans card_biUnion_le
  have h3 : ∑ x : V, ((univ.filter (fun y => s(x, y) ∈ B)).image (fun y => (x, y))).card ≤
      ∑ _x : V, d := Finset.sum_le_sum fun x _ => card_image_le.trans (h2 x)
  rw [Finset.sum_const, smul_eq_mul, card_univ] at h3
  exact_mod_cast this.trans h3

lemma card_nbr_le (B : Finset (Sym2 V)) (d : ℕ) (hB : ∀ x, degB B x ≤ d) (a : V) :
    ((univ.filter (fun x => s(x, a) ∈ B)).card : ℝ) ≤ d := by
  have : (univ.filter (fun x => s(x, a) ∈ B)).card ≤ d := by
    refine le_trans ?_ (hB a)
    unfold degB
    refine Finset.card_le_card_of_injOn (fun x => s(x, a)) ?_ ?_
    · intro y hy; simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
      simp [hy]
    · intro y _ y' _ h; exact Sym2.congr_left.1 h
  exact_mod_cast this

/-- **a good hinge exists** -/
theorem good_hinge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) {i : ℕ} (hi : 6 ≤ i) {α : ℝ}
    (hcount : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges G lab F u v a b i).card)
    (S : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hB : ∀ x, degB B x ≤ d)
    (hlt : ((S.card : ℝ) + 3 * d) * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) <
      α * (Fintype.card V : ℝ) ^ (i - 4)) :
    ∃ J ∈ hinges G lab F u v a b i, (∀ z ∈ S, z ∉ freeV u v a b J) ∧ ¬ BadB B u v a b J := by
  set n := Fintype.card V
  set 𝓗 := hinges G lab F u v a b i
  set K5 : ℝ := 2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5)
  set P := (univ ×ˢ univ).filter (fun p : V × V => s(p.1, p.2) ∈ B ∧ p.1 ≠ p.2)
  set Na := univ.filter (fun x => s(x, a) ∈ B)
  set Nb := univ.filter (fun x => s(x, b) ∈ B)
  set bad := (S.biUnion fun z => 𝓗.filter fun J => z ∈ freeV u v a b J) ∪
    (P.biUnion fun p => 𝓗.filter fun J => p.1 ∈ freeV u v a b J ∧ p.2 ∈ freeV u v a b J) ∪
    (Na.biUnion fun x => 𝓗.filter fun J => x ∈ freeV u v a b J) ∪
    (Nb.biUnion fun x => 𝓗.filter fun J => x ∈ freeV u v a b J)
  have hsum : ∀ (X : Finset V), ((X.biUnion fun z => 𝓗.filter fun J => z ∈ freeV u v a b J).card
      : ℝ) ≤ X.card * K5 := by
    intro X
    calc _ ≤ ((∑ z ∈ X, (𝓗.filter fun J => z ∈ freeV u v a b J).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ z ∈ X, ((𝓗.filter fun J => z ∈ freeV u v a b J).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _z ∈ X, K5 := Finset.sum_le_sum fun z _ => by convert hinge_free_deg hd i z
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hP : ((P.biUnion fun p => 𝓗.filter fun J =>
      p.1 ∈ freeV u v a b J ∧ p.2 ∈ freeV u v a b J).card : ℝ) ≤ d * K5 := by
    have hK : (n : ℝ) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 6)) = K5 := by
      simp only [K5]
      have : (n : ℝ) ^ (i - 5) = (n : ℝ) ^ (i - 6) * n := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; ring
    calc _ ≤ ((∑ p ∈ P, (𝓗.filter fun J =>
            p.1 ∈ freeV u v a b J ∧ p.2 ∈ freeV u v a b J).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ p ∈ P, ((𝓗.filter fun J =>
            p.1 ∈ freeV u v a b J ∧ p.2 ∈ freeV u v a b J).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _p ∈ P, (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 6)) := Finset.sum_le_sum fun p hp => by
          have : p.1 ≠ p.2 := by simp only [P, mem_filter] at hp; exact hp.2.2
          convert hinge_free_deg2 hd i this
      _ = P.card * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 6)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n * d) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 6)) :=
          mul_le_mul_of_nonneg_right (card_pairs_le B d hB) (by positivity)
      _ = d * K5 := by rw [← hK]; ring
  have hK5 : 0 ≤ K5 := by positivity
  have hbad : (bad.card : ℝ) ≤ ((S.card : ℝ) + 3 * d) * K5 := by
    have h1 := hsum S
    have h3 := (hsum Na).trans (mul_le_mul_of_nonneg_right (card_nbr_le B d hB a) hK5)
    have h4 := (hsum Nb).trans (mul_le_mul_of_nonneg_right (card_nbr_le B d hB b) hK5)
    have hu : (bad.card : ℝ) ≤
        ((S.biUnion fun z => 𝓗.filter fun J => z ∈ freeV u v a b J).card : ℝ) +
        ((P.biUnion fun p => 𝓗.filter fun J =>
          p.1 ∈ freeV u v a b J ∧ p.2 ∈ freeV u v a b J).card : ℝ) +
        ((Na.biUnion fun x => 𝓗.filter fun J => x ∈ freeV u v a b J).card : ℝ) +
        ((Nb.biUnion fun x => 𝓗.filter fun J => x ∈ freeV u v a b J).card : ℝ) := by
      exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _)) _)
    linarith
  have hlt' : (bad.card : ℝ) < 𝓗.card := lt_of_le_of_lt hbad (lt_of_lt_of_le hlt hcount)
  have : (𝓗 \ bad).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff bad 𝓗
    have h' : bad.card < 𝓗.card := by exact_mod_cast hlt'
    omega
  obtain ⟨J, hJ⟩ := this
  rw [mem_sdiff] at hJ
  refine ⟨J, hJ.1, fun z hz hzJ => hJ.2 ?_, fun hb => hJ.2 ?_⟩
  · simp only [bad, mem_union, mem_biUnion, mem_filter]
    exact Or.inl (Or.inl (Or.inl ⟨z, hz, hJ.1, hzJ⟩))
  · obtain ⟨x, y, hxyB, hxy, hx, hy⟩ := hb
    simp only [bad, mem_union, mem_biUnion, mem_filter]
    rcases hy with hy | rfl | rfl
    · exact Or.inl (Or.inl (Or.inr ⟨(x, y), by simp [P, hxyB, hxy], hJ.1, hx, hy⟩))
    · exact Or.inl (Or.inr ⟨x, by simp [Na, hxyB], hJ.1, hx⟩)
    · exact Or.inr ⟨x, by simp [Nb, hxyB], hJ.1, hx⟩

/-- **local robustness of the link from the ORIGINAL H4** -/
theorem link_evenRobust {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hH4 : HingeCond G lab F α h) (v : V) (s d : ℕ)
    (hsd : ((s : ℝ) + 3 * d) * 2 ^ (h.choose 2) < α * Fintype.card V) :
    EvenRobustLocal (link G lab F v) s d := by
  intro u a b hua hub hab S hS B hB
  set n := Fintype.card V
  have hA : IsAllowed G lab F {u, v, a} := by rw [Finset.insert_comm]; exact hua.2
  have hB' : IsAllowed G lab F {u, v, b} := by rw [Finset.insert_comm]; exact hub.2
  obtain ⟨huv, hua', hva⟩ := distinct_of_allowed hA
  obtain ⟨-, hub', hvb⟩ := distinct_of_allowed hB'
  have hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b := ⟨huv, hua', hva, hub', hvb, hab⟩
  obtain ⟨i, hi6, hih, hcount⟩ := hH4 u v a b hab hA hB'
  have hn : 0 < n := Fintype.card_pos_iff.2 ⟨u⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : ((S.card : ℝ) + 3 * d) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5)) <
      α * (n : ℝ) ^ (i - 4) := by
    have h1 : ((S.card : ℝ) + 3 * d) ≤ (s : ℝ) + 3 * d := by
      have : (S.card : ℝ) ≤ s := by exact_mod_cast hS
      linarith
    have h2 : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (h.choose 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
    have hpow : (n : ℝ) ^ (i - 4) = n * (n : ℝ) ^ (i - 5) := by
      rw [← pow_succ']; congr 1; omega
    have hp : 0 < (n : ℝ) ^ (i - 5) := by positivity
    calc ((S.card : ℝ) + 3 * d) * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5))
        ≤ ((s : ℝ) + 3 * d) * 2 ^ (h.choose 2) * (n : ℝ) ^ (i - 5) := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hp.le
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ < α * n * (n : ℝ) ^ (i - 5) := mul_lt_mul_of_pos_right hsd hp
      _ = α * (n : ℝ) ^ (i - 4) := by rw [hpow]; ring
  obtain ⟨J, hJ, hJS, hJB⟩ := good_hinge hd hi6 hcount S B d hB hlt
  have hJ' : IsHinge G lab F u v a b J := (Finset.mem_filter.1 hJ).2.1
  obtain ⟨p, hp, hpe, hps, hpab⟩ := hinge_path hJ' hd
  have hfree : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ freeV u v a b J := by
    intro x hx hxa hxb
    obtain ⟨h1, h2, h3⟩ := hps x hx
    simp only [freeV, mem_sdiff, mem_insert, mem_singleton]
    tauto
  refine ⟨p, hp, hpe, fun x hx hxS => ?_, fun e he heB => ?_⟩
  · by_contra hne; push_neg at hne
    exact hJS x hxS (hfree x hx hne.1 hne.2)
  · induction e using Sym2.ind with
    | _ x y =>
    have hx := p.fst_mem_support_of_mem_edges he
    have hy := p.snd_mem_support_of_mem_edges he
    have hxy : x ≠ y := (p.adj_of_mem_edges he).ne
    have hne := hpab _ he
    apply hJB
    by_cases hxf : x ∈ freeV u v a b J
    · refine ⟨x, y, heB, hxy, hxf, ?_⟩
      by_cases hya : y = a
      · exact Or.inr (Or.inl hya)
      by_cases hyb : y = b
      · exact Or.inr (Or.inr hyb)
      exact Or.inl (hfree y hy hya hyb)
    · have hxab : x = a ∨ x = b := by
        by_contra hc; push_neg at hc; exact hxf (hfree x hx hc.1 hc.2)
      have hyf : y ∈ freeV u v a b J := by
        by_contra hyf
        have hyab : y = a ∨ y = b := by
          by_contra hc; push_neg at hc; exact hyf (hfree y hy hc.1 hc.2)
        apply hne
        rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl
        · exact absurd rfl hxy
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hxy
      refine ⟨y, x, by rw [Sym2.eq_swap]; exact heB, hxy.symm, hyf, Or.inr hxab⟩

/-- **linear link degrees from the ORIGINAL H3** -/
theorem link_degree_ge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond G lab F α) (v w : V) (hw : ∃ y, (link G lab F v).Adj w y) :
    α * Fintype.card V ≤ (link G lab F v).degree w := by
  obtain ⟨y, hwy, hall⟩ := hw
  obtain ⟨hvw, hvy, hwy'⟩ := distinct_of_card_three hall.1
  have hval : ∀ z, v ≠ z → w ≠ z →
      ((({v, w, z} : Finset V).val.map lab) = ({lab v, lab w, lab z} : Multiset I)) := by
    intro z hvz hwz
    rw [Finset.insert_val_of_notMem (by simp [hvw, hvz]),
      Finset.insert_val_of_notMem (by simp [hwz])]
    simp
  have hF : ({lab v, lab w, lab y} : Multiset I) ∈ F := by
    rw [← hval y hvy hwy']; exact hall.2.2
  have hsub : commonNbrs G lab (lab y) v w ⊆ (link G lab F v).neighborFinset w := by
    intro z hz
    simp only [commonNbrs, mem_filter, mem_univ, true_and] at hz
    obtain ⟨hvz, hwz, hlz⟩ := hz
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨hwz.ne, card_three_of_distinct hvw hvz.ne hwz.ne, ?_, ?_⟩
    · intro x hx x' hx' hxx'
      simp only [mem_insert, mem_singleton] at hx hx'
      have hGvw : G.Adj v w := hall.2.1 v (by simp) w (by simp) hvw
      rcases hx with rfl | rfl | rfl <;> rcases hx' with rfl | rfl | rfl
      all_goals first | exact absurd rfl hxx' | assumption | exact SimpleGraph.Adj.symm ‹_›
    · rw [hval z hvz.ne hwz.ne, hlz]; exact hF
  have := card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  calc α * Fintype.card V ≤ (commonNbrs G lab (lab y) v w).card := hH3 v w hvw (lab y) hF
    _ ≤ _ := by exact_mod_cast this

end S07V25
