/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Transport
public import RequestProject.S07.HingeCore
@[expose] public section

/-!
# V42 §1 — H3 and H4 survive a small vertex deletion on the TRUE induced subhost

`ι : Y → X` is injective with image exactly the complement of a small set `Zx ⊆ X`; `G` is a host
on `X` and `G.comap ι` is the actual induced host on `Y` (for `X = {x // x ∈ W}`,
`Y = {x // x ∈ W \ Z}` this is `H[W \ Z]` as a true subtype host).

* `exists_pull_decomposition`: a decomposition in `G` of an edge set coming from `Y` is the image
  of a decomposition in `G.comap ι`.
* `isHinge_pull`: a hinge of `G` whose edges come from `Y` is the image of a hinge of
  `G.comap ι` (same support size).
* `commonNbr_deletion`: H3 with `β` for `G` and `|Zx| ≤ δ |X|`, `δ ≤ β / 2` give H3 with `β / 2`
  for `G.comap ι` (with `n = |Y|`).
* `hinge_deletion`: H4 with `(β, h)` for `G` and `|Zx| ≤ δ |X|`, `δ · 2^(h choose 2) ≤ β / 2` give
  H4 with `(β / 2, h)` for `G.comap ι`.
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge

variable {X Y I : Type*}

section pull

variable {ι : Y → X} (hι : Function.Injective ι) {G : SimpleGraph X} {lab : X → I}
  {F : Set (Multiset I)}

include hι in
lemma mem_range_of_triEdges_sub {T : Finset X} (hT : T.card = 3) {K : Finset (Sym2 Y)}
    (hK : triEdges T ⊆ K.map (emb2 hι)) : ∀ x ∈ T, ∃ y, ι y = x := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ T, z ≠ x := by
    by_contra hcon
    push_neg at hcon
    have : T ⊆ {x} := fun b hb => Finset.mem_singleton.2 (hcon b hb)
    have := Finset.card_le_card this
    rw [hT, Finset.card_singleton] at this
    omega
  have he : s(x, z) ∈ triEdges T := mem_triEdges.2 ⟨hx, hz, hzx.symm⟩
  obtain ⟨e', -, he'⟩ := Finset.mem_map.1 (hK he)
  induction e' using Sym2.ind with
  | h a b =>
    rw [emb2_apply, Sym2.map_mk, Sym2.eq_iff] at he'
    rcases he' with ⟨h1, -⟩ | ⟨-, h2⟩
    exacts [⟨a, h1⟩, ⟨b, h2⟩]

include hι in
lemma exists_map_of_range {T : Finset X} (hT : ∀ x ∈ T, ∃ y, ι y = x) :
    ∃ T' : Finset Y, T'.map (emb hι) = T := by
  refine ⟨T.preimage ι hι.injOn, ?_⟩
  ext a
  simp only [Finset.mem_map, Finset.mem_preimage, emb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro ha
    obtain ⟨x, rfl⟩ := hT a ha
    exact ⟨x, ha, rfl⟩

/-- **Pull-back of decompositions.** -/
theorem exists_pull_decomposition {K : Finset (Sym2 Y)} {D : Finset (Finset X)}
    (hD : IsDecomposition G lab F (K.map (emb2 hι)) D) :
    ∃ D' : Finset (Finset Y), IsDecomposition (G.comap ι) (lab ∘ ι) F K D' := by
  have hrange : ∀ T ∈ D, ∃ T' : Finset Y, T'.map (emb hι) = T := fun T hT =>
    exists_map_of_range hι (mem_range_of_triEdges_sub hι (hD.1 T hT).1
      (by rw [← hD.2.2]; exact Finset.subset_biUnion_of_mem triEdges hT))
  let D' : Finset (Finset Y) := D.preimage (fun T' => T'.map (emb hι))
    ((Finset.map_injective (emb hι)).injOn)
  have hD' : D'.map (Finset.mapEmbedding (emb hι)).toEmbedding = D := by
    ext T
    simp only [D', Finset.mem_map, Finset.mem_preimage, RelEmbedding.coe_toEmbedding,
      Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨T', hT', rfl⟩; exact hT'
    · intro hT
      obtain ⟨T', rfl⟩ := hrange T hT
      exact ⟨T', hT, rfl⟩
  refine ⟨D', ⟨fun T' hT' => ?_, ?_, ?_⟩⟩
  · rw [isAllowed_comap_iff hι]
    exact hD.1 _ (by rw [← hD']; exact Finset.mem_map_of_mem _ hT')
  · intro T₁ h₁ T₂ h₂ hne
    have h₁' : T₁.map (emb hι) ∈ D := by rw [← hD']; exact Finset.mem_map_of_mem _ h₁
    have h₂' : T₂.map (emb hι) ∈ D := by rw [← hD']; exact Finset.mem_map_of_mem _ h₂
    have hne' : T₁.map (emb hι) ≠ T₂.map (emb hι) := fun h => hne (Finset.map_injective _ h)
    have := hD.2.1 h₁' h₂' hne'
    simp only [Function.onFun, triEdges_map] at this
    exact (Finset.disjoint_map _).1 this
  · apply Finset.map_injective (emb2 hι)
    rw [← hD.2.2, ← hD']
    ext e
    simp only [Finset.mem_map, Finset.mem_biUnion, RelEmbedding.coe_toEmbedding,
      Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨e', ⟨T, hT, he'⟩, rfl⟩
      exact ⟨T.map (emb hι), ⟨T, hT, rfl⟩, by rw [triEdges_map]; exact Finset.mem_map_of_mem _ he'⟩
    · rintro ⟨_, ⟨T, hT, rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
      exact ⟨e', ⟨T, hT, he'⟩, rfl⟩

lemma wedge_map (u v a : Y) :
    wedge (ι u) (ι v) (ι a) = (wedge u v a).map (emb2 hι) := by
  simp [wedge, emb2_apply, Finset.map_insert, Finset.map_singleton]

lemma triple_map (u v a : Y) :
    ({ι u, ι v, ι a} : Finset X) = ({u, v, a} : Finset Y).map (emb hι) := by
  simp [Finset.map_insert, Finset.map_singleton, emb_apply]

lemma support_map [Fintype X] [Fintype Y] (J : Finset (Sym2 Y)) :
    support (J.map (emb2 hι)) = (support J).map (emb hι) := by
  ext x
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    emb2_apply, emb_apply]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hx⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.map_mk, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨a, ⟨s(a, b), he, Sym2.mem_mk_left a b⟩, rfl⟩
      · exact ⟨b, ⟨s(a, b), he, Sym2.mem_mk_right a b⟩, rfl⟩
  · rintro ⟨y, ⟨e, he, hy⟩, rfl⟩
    exact ⟨Sym2.map ι e, ⟨e, he, rfl⟩, Sym2.mem_map.2 ⟨y, hy, rfl⟩⟩

/-- **Pull-back of hinges.** -/
theorem isHinge_pull [Fintype X] [Fintype Y] {u v a b : Y} {J : Finset (Sym2 Y)}
    (hJ : IsHinge G lab F (ι u) (ι v) (ι a) (ι b) (J.map (emb2 hι))) :
    IsHinge (G.comap ι) (lab ∘ ι) F u v a b J := by
  obtain ⟨h1, h2, ⟨D₁, hD₁⟩, ⟨D₂, hD₂⟩⟩ := hJ
  refine ⟨fun e he => (mem_edges_comap e).2 (h1 (Finset.mem_map_of_mem _ he)), ?_, ?_, ?_⟩
  · rw [triple_map hι, triple_map hι, triEdges_map, triEdges_map, ← Finset.map_union] at h2
    exact (Finset.disjoint_map _).1 h2
  · rw [wedge_map hι, ← Finset.map_union] at hD₁
    exact exists_pull_decomposition hι hD₁
  · rw [wedge_map hι, ← Finset.map_union] at hD₂
    exact exists_pull_decomposition hι hD₂

end pull

/-! ### H3 and H4 under small deletion -/

section deletion

variable [Fintype X] [Fintype Y] {ι : Y → X} (hι : Function.Injective ι) {Zx : Finset X}
  (hrange : ∀ x, (∃ y, ι y = x) ↔ x ∉ Zx) {G : SimpleGraph X} {lab : X → I}
  {F : Set (Multiset I)}

include hι in
lemma card_le_of_range : Fintype.card Y ≤ Fintype.card X :=
  Fintype.card_le_of_injective ι hι

include hι hrange in
/-- **H3 survives a small deletion on the true induced subhost.** -/
theorem commonNbr_deletion {β δ : ℝ} (hβ : 0 < β) (hH3 : CommonNbrCond G lab F β)
    (hZ : (Zx.card : ℝ) ≤ δ * Fintype.card X) (hδ : δ ≤ β / 2) :
    CommonNbrCond (G.comap ι) (lab ∘ ι) F (β / 2) := by
  intro u v huv k hk
  have hne : ι u ≠ ι v := fun h => huv (hι h)
  have h0 := hH3 (ι u) (ι v) hne k hk
  have hsub : commonNbrs G lab k (ι u) (ι v) \ Zx ⊆
      (commonNbrs (G.comap ι) (lab ∘ ι) k u v).map (emb hι) := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨y, rfl⟩ := (hrange w).2 hw.2
    have := hw.1
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at this
    refine Finset.mem_map.2 ⟨y, ?_, rfl⟩
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.comap_adj, Function.comp]
    exact this
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_map] at h1
  have h2 : ((commonNbrs G lab k (ι u) (ι v)).card : ℝ) - Zx.card ≤
      ((commonNbrs G lab k (ι u) (ι v) \ Zx).card : ℝ) := by
    have := Finset.le_card_sdiff Zx (commonNbrs G lab k (ι u) (ι v))
    have h3 := Finset.card_le_card (Finset.inter_subset_left (s₁ := Zx)
      (s₂ := commonNbrs G lab k (ι u) (ι v)))
    have : (commonNbrs G lab k (ι u) (ι v)).card ≤
        (commonNbrs G lab k (ι u) (ι v) \ Zx).card + Zx.card := by
      have := Finset.card_sdiff_add_card_inter (commonNbrs G lab k (ι u) (ι v)) Zx
      have h4 := Finset.card_le_card (Finset.inter_subset_right (s₁ := commonNbrs G lab k
        (ι u) (ι v)) (s₂ := Zx))
      omega
    have : ((commonNbrs G lab k (ι u) (ι v)).card : ℝ) ≤
        ((commonNbrs G lab k (ι u) (ι v) \ Zx).card : ℝ) + Zx.card := by exact_mod_cast this
    linarith
  have hYX : (Fintype.card Y : ℝ) ≤ Fintype.card X := by
    exact_mod_cast card_le_of_range hι
  have hX0 : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  have h1' : ((commonNbrs G lab k (ι u) (ι v) \ Zx).card : ℝ) ≤
      ((commonNbrs (G.comap ι) (lab ∘ ι) k u v).card : ℝ) := by exact_mod_cast h1
  have : δ * Fintype.card X ≤ β / 2 * Fintype.card X := mul_le_mul_of_nonneg_right hδ hX0
  have : β / 2 * Fintype.card Y ≤ β / 2 * Fintype.card X :=
    mul_le_mul_of_nonneg_left hYX (by linarith)
  linarith

omit [Fintype Y] in
include hι hrange in
/-- every hinge of `G` at roots coming from `Y`, with free vertices outside `Zx`, has all its
edges coming from `Y` -/
lemma hinge_edges_from {u v a b : Y} {J : Finset (Sym2 X)}
    (hfree : S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ \ Zx) :
    ∃ J' : Finset (Sym2 Y), J'.map (emb2 hι) = J := by
  have hv : ∀ x ∈ support J, ∃ y, ι y = x := by
    intro x hx
    by_cases hr : x ∈ ({ι u, ι v, ι a, ι b} : Finset X)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [⟨u, rfl⟩, ⟨v, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩]
    · have : x ∈ S07V24.freeV (ι u) (ι v) (ι a) (ι b) J := Finset.mem_sdiff.2 ⟨hx, hr⟩
      exact (hrange x).2 (Finset.mem_sdiff.1 (hfree this)).2
  refine ⟨J.preimage (Sym2.map ι) (Sym2.map.injective hι).injOn, ?_⟩
  ext e
  simp only [Finset.mem_map, Finset.mem_preimage, emb2_apply]
  constructor
  · rintro ⟨e', he', rfl⟩; exact he'
  · intro he
    induction e using Sym2.ind with
    | h p q =>
      obtain ⟨p', rfl⟩ := hv p (mem_support_of_mem he (Sym2.mem_mk_left p q))
      obtain ⟨q', rfl⟩ := hv q (mem_support_of_mem he (Sym2.mem_mk_right _ q))
      exact ⟨s(p', q'), by simpa using he, by simp⟩

include hι hrange in
/-- hinges of `G` with free vertices outside `Zx` inject into hinges of `G.comap ι` -/
lemma card_hinges_pull_ge (u v a b : Y) (i : ℕ) :
    ((hinges G lab F (ι u) (ι v) (ι a) (ι b) i).filter
        (fun J => S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ \ Zx)).card ≤
      (hinges (G.comap ι) (lab ∘ ι) F u v a b i).card := by
  rw [← Finset.card_map (Finset.mapEmbedding (emb2 hι)).toEmbedding]
  apply Finset.card_le_card
  intro J hJ
  rw [Finset.mem_filter] at hJ
  obtain ⟨J', rfl⟩ := hinge_edges_from hι hrange hJ.2
  have hJ1 := hJ.1
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ1
  refine Finset.mem_map.2 ⟨J', ?_, rfl⟩
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨isHinge_pull hι hJ1.1, ?_⟩
  rw [← hJ1.2, support_map hι, Finset.card_map]

include hι hrange in
/-- **H4 survives a small deletion on the true induced subhost.** -/
theorem hinge_deletion {β δ : ℝ} {h : ℕ} (hβ : 0 < β) (hH4 : HingeCond G lab F β h)
    (hZ : (Zx.card : ℝ) ≤ δ * Fintype.card X) (hδ0 : 0 ≤ δ)
    (hδ : δ * 2 ^ (h.choose 2) ≤ β / 2) :
    HingeCond (G.comap ι) (lab ∘ ι) F (β / 2) h := by
  intro u v a b hab hua hub
  have hua' := (isAllowed_comap_iff hι _).1 hua
  have hub' := (isAllowed_comap_iff hι _).1 hub
  rw [← triple_map hι] at hua' hub'
  have hab' : ι a ≠ ι b := fun h' => hab (hι h')
  obtain ⟨i, hi6, hih, hcount⟩ := hH4 (ι u) (ι v) (ι a) (ι b) hab' hua' hub'
  refine ⟨i, hi6, hih, ?_⟩
  obtain ⟨huv, hua0, hva⟩ := S07V24.distinct_of_allowed hua'
  obtain ⟨-, hub0, hvb⟩ := S07V24.distinct_of_allowed hub'
  have hdel := S07V24.hinge_delete (G := G) (lab := lab) (F := F)
    ⟨huv, hua0, hva, hub0, hvb, hab'⟩ i univ Zx
  have hfilt : (hinges G lab F (ι u) (ι v) (ι a) (ι b) i).filter
      (fun J => S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ) =
      hinges G lab F (ι u) (ι v) (ι a) (ι b) i :=
    Finset.filter_true_of_mem fun J _ => Finset.subset_univ _
  rw [hfilt] at hdel
  have hpull := card_hinges_pull_ge hι hrange (G := G) (lab := lab) (F := F) u v a b i
  have hpull' : ((((hinges G lab F (ι u) (ι v) (ι a) (ι b) i).filter
        (fun J => S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ \ Zx)).card : ℕ) : ℝ) ≤
      ((hinges (G.comap ι) (lab ∘ ι) F u v a b i).card : ℝ) := by exact_mod_cast hpull
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hpowi : n ^ (i - 4) = n ^ (i - 5) * n := by
    rw [← pow_succ]; congr 1; omega
  have hch : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (h.choose 2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hp5 : 0 ≤ n ^ (i - 5) := pow_nonneg hn0 _
  have hbad : (Zx.card : ℝ) * (2 ^ (i.choose 2) * n ^ (i - 5)) ≤ β / 2 * n ^ (i - 4) := by
    calc (Zx.card : ℝ) * (2 ^ (i.choose 2) * n ^ (i - 5))
        ≤ δ * n * (2 ^ (h.choose 2) * n ^ (i - 5)) := by
          apply mul_le_mul hZ (mul_le_mul_of_nonneg_right hch hp5) (by positivity)
            (by positivity)
      _ = δ * 2 ^ (h.choose 2) * (n ^ (i - 5) * n) := by ring
      _ ≤ β / 2 * (n ^ (i - 5) * n) := mul_le_mul_of_nonneg_right hδ (by positivity)
      _ = β / 2 * n ^ (i - 4) := by rw [hpowi]
  have hYX : (Fintype.card Y : ℝ) ^ (i - 4) ≤ n ^ (i - 4) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by rw [hn]; exact_mod_cast card_le_of_range hι) _
  have : β / 2 * (Fintype.card Y : ℝ) ^ (i - 4) ≤ β / 2 * n ^ (i - 4) :=
    mul_le_mul_of_nonneg_left hYX (by linarith)
  linarith

end deletion

end S07V42
