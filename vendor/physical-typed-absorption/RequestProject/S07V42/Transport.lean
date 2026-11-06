/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V37.NativeKernel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V42 §0 — transport along an injective vertex map (true induced subhosts)

Throughout, `ι : X → V` is injective, `G` is a host on `V` and `G.comap ι` is the ACTUAL
induced host on `X` (for `X = {x // x ∈ U}` and `ι = Subtype.val` this is `H[U]` on the true
subtype). Labels are `lab ∘ ι`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal

variable {X V I : Type*}

/-! ### Basic transport of triangles and edges -/

section basic

variable {ι : X → V} (hι : Function.Injective ι)

/-- the embedding attached to `ι` -/
def emb : X ↪ V := ⟨ι, hι⟩

/-- the embedding of unordered pairs -/
def emb2 : Sym2 X ↪ Sym2 V := ⟨Sym2.map ι, Sym2.map.injective hι⟩

lemma emb_apply (x : X) : emb hι x = ι x := rfl

lemma emb2_apply (e : Sym2 X) : emb2 hι e = Sym2.map ι e := rfl

lemma triEdges_map (T : Finset X) :
    triEdges (T.map (emb hι)) = (triEdges T).map (emb2 hι) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Finset.mem_map, emb2, Function.Embedding.coeFn_mk]
    constructor
    · intro he
      obtain ⟨ha, hb, hab⟩ := mem_triEdges.1 he
      simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      exact ⟨s(a', b'), mem_triEdges.2 ⟨ha', hb', fun h => hab (h ▸ rfl)⟩, by simp⟩
    · rintro ⟨e', he', hee⟩
      induction e' using Sym2.ind with
      | h a' b' =>
        obtain ⟨ha', hb', hab'⟩ := mem_triEdges.1 he'
        simp only [Sym2.map_mk] at hee
        rw [← hee]
        refine mem_triEdges.2 ⟨Finset.mem_map_of_mem (emb hι) ha',
          Finset.mem_map_of_mem (emb hι) hb', ?_⟩
        exact fun h => hab' (hι h)

lemma isAllowed_comap_iff {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (T : Finset X) :
    IsAllowed (G.comap ι) (lab ∘ ι) F T ↔ IsAllowed G lab F (T.map (emb hι)) := by
  unfold IsAllowed
  simp only [Finset.card_map, Finset.mem_map, emb, Function.Embedding.coeFn_mk,
    SimpleGraph.comap_adj, Finset.map_val, Multiset.map_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact h2 x hx y hy (fun h => hxy (h ▸ rfl))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx y hy hxy => h2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (fun h => hxy (hι h)), h3⟩

lemma mem_edges_comap {G : SimpleGraph V} [Fintype X] [Fintype V] (e : Sym2 X) :
    e ∈ edges (G.comap ι) ↔ Sym2.map ι e ∈ edges G := by
  induction e using Sym2.ind with
  | h a b => simp [mem_edges]

end basic

/-! ### Zero extension of edge vectors and local profiles -/

section lift

variable {ι : X → V} (hι : Function.Injective ι)

/-- zero extension of an edge vector of `X` to `V` along `Sym2.map ι` -/
def liftE (x : Sym2 X → ℤ) : Sym2 V → ℤ := Function.extend (Sym2.map ι) x 0

include hι in
lemma liftE_map (x : Sym2 X → ℤ) (e : Sym2 X) : liftE (ι := ι) x (Sym2.map ι e) = x e :=
  (Sym2.map.injective hι).extend_apply x 0 e

lemma liftE_of_not (x : Sym2 X → ℤ) {e : Sym2 V} (he : ¬ ∃ e', Sym2.map ι e' = e) :
    liftE (ι := ι) x e = 0 := by
  unfold liftE; rw [Function.extend_apply' _ _ _ he]; rfl

/-- the zero extension as a linear map -/
def liftL (ι : X → V) (hι : Function.Injective ι) : (Sym2 X → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) where
  toFun x := liftE (ι := ι) x
  map_add' x y := by
    funext e
    by_cases he : ∃ e', Sym2.map ι e' = e
    · obtain ⟨e', rfl⟩ := he
      simp [liftE_map hι]
    · simp [liftE_of_not (ι := ι) _ he]
  map_smul' r x := by
    funext e
    by_cases he : ∃ e', Sym2.map ι e' = e
    · obtain ⟨e', rfl⟩ := he
      simp [liftE_map hι]
    · simp [liftE_of_not (ι := ι) _ he]

lemma liftL_apply (x : Sym2 X → ℤ) : liftL ι hι x = liftE (ι := ι) x := rfl

include hι in
lemma l1E_liftE [Fintype X] [Fintype V] (x : Sym2 X → ℤ) : l1E (liftE (ι := ι) x) = l1E x := by
  unfold l1E
  rw [← Finset.sum_subset (Finset.subset_univ (univ.map (emb2 hι)))]
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun e _ => by rw [emb2_apply, liftE_map hι]
  · intro e _ he
    rw [liftE_of_not (ι := ι) x, abs_zero]
    rintro ⟨e', rfl⟩
    exact he (Finset.mem_map_of_mem _ (Finset.mem_univ e'))

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- every edge of `G` has its ends in the image of `ι` -/
def EdgesIn (G : SimpleGraph V) (ι : X → V) : Prop := ∀ a b, G.Adj a b → ∃ x, ι x = a

lemma allowed_subset_range (hG : EdgesIn G ι) {T : Finset V} (hT : IsAllowed G lab F T)
    {v : V} (hv : v ∈ T) : ∀ a ∈ T, ∃ x, ι x = a := by
  intro a ha
  by_cases hav : a = v
  · subst hav
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ T, b ≠ a := by
      by_contra hcon
      push_neg at hcon
      have : T ⊆ {a} := fun b hb => Finset.mem_singleton.2 (hcon b hb)
      have := Finset.card_le_card this
      rw [hT.1, Finset.card_singleton] at this
      omega
    exact hG a b (hT.2.1 a ha b hb hba.symm)
  · exact hG a v (hT.2.1 a ha v hv hav)

include hι in
lemma exists_map_of_allowed (hG : EdgesIn G ι) {T : Finset V} (hT : IsAllowed G lab F T)
    {v : V} (hv : v ∈ T) : ∃ T' : Finset X, T'.map (emb hι) = T := by
  refine ⟨T.preimage ι hι.injOn, ?_⟩
  ext a
  simp only [Finset.mem_map, Finset.mem_preimage, emb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro ha
    obtain ⟨x, rfl⟩ := allowed_subset_range hG hT hv a ha
    exact ⟨x, ha, rfl⟩

/-- the allowed triangles of `G` through `ι v` and `ι w` are the images of those of
`G.comap ι` through `v` and `w` -/
lemma allowedAt_map [Fintype X] [Fintype V] (hG : EdgesIn G ι) (v w : X) :
    ((univ.filter (IsAllowed G lab F)).filter (ι v ∈ ·)).filter (ι w ∈ ·) =
      (((univ.filter (IsAllowed (G.comap ι) (lab ∘ ι) F)).filter (v ∈ ·)).filter
        (w ∈ ·)).map (Finset.mapEmbedding (emb hι)).toEmbedding := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨⟨hT, hv⟩, hw⟩
    obtain ⟨T', rfl⟩ := exists_map_of_allowed hι hG hT hv
    refine ⟨T', ⟨⟨(isAllowed_comap_iff hι T').2 hT, ?_⟩, ?_⟩, rfl⟩
    · obtain ⟨x, hx, hxv⟩ := Finset.mem_map.1 hv
      rw [emb_apply] at hxv; rw [← hι hxv]; exact hx
    · obtain ⟨x, hx, hxw⟩ := Finset.mem_map.1 hw
      rw [emb_apply] at hxw; rw [← hι hxw]; exact hx
  · rintro ⟨T', ⟨⟨hT', hv⟩, hw⟩, rfl⟩
    exact ⟨⟨(isAllowed_comap_iff hι T').1 hT', Finset.mem_map_of_mem (emb hι) hv⟩,
      Finset.mem_map_of_mem (emb hι) hw⟩

lemma allowedAt_empty_of_not [Fintype V] (hG : EdgesIn G ι) {v : V} (hv : ¬ ∃ x, ι x = v) (w : V) :
    ((univ.filter (IsAllowed G lab F)).filter (v ∈ ·)).filter (w ∈ ·) = ∅ := by
  apply Finset.filter_false_of_mem
  intro T hT _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  exact hv (allowed_subset_range hG hT.1 hT.2 v hT.2)

include hι in
/-- the zero extension of a local profile of `G.comap ι` is a local profile of `G` -/
theorem isLocalProfile_liftE [Fintype X] [Fintype V] (hG : EdgesIn G ι) {x : Sym2 X → ℤ}
    (hx : IsLocalProfile (G.comap ι) (lab ∘ ι) F x) :
    IsLocalProfile G lab F (liftE (ι := ι) x) := by
  refine ⟨fun e he => ?_, fun v => ?_⟩
  · by_cases h : ∃ e', Sym2.map ι e' = e
    · obtain ⟨e', rfl⟩ := h
      rw [liftE_map hι]
      exact hx.1 e' fun h' => he ((mem_edges_comap e').1 h')
    · exact liftE_of_not (ι := ι) x h
  · by_cases hv : ∃ v0, ι v0 = v
    · obtain ⟨v0, rfl⟩ := hv
      obtain ⟨c, hc⟩ := hx.2 v0
      refine ⟨fun T => if h : ∃ T' : Finset X, T'.map (emb hι) = T then c h.choose else 0,
        fun w hw => ?_⟩
      by_cases hw' : ∃ w0, ι w0 = w
      · obtain ⟨w0, rfl⟩ := hw'
        have hne : w0 ≠ v0 := fun h => hw (h ▸ rfl)
        rw [allowedAt_map hι hG, Finset.sum_map]
        have : s(ι v0, ι w0) = Sym2.map ι s(v0, w0) := by simp
        rw [this, liftE_map hι, hc w0 hne]
        refine Finset.sum_congr rfl fun T' _ => ?_
        simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
        have hex : ∃ T'' : Finset X, T''.map (emb hι) = T'.map (emb hι) := ⟨T', rfl⟩
        rw [dif_pos hex]
        congr 1
        exact (Finset.map_injective (emb hι) hex.choose_spec).symm
      · rw [liftE_of_not (ι := ι) x]
        · symm
          apply Finset.sum_eq_zero
          intro T hT
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
          exact absurd (allowed_subset_range hG hT.1.1 hT.2 w hT.2) hw'
        · rintro ⟨e', he'⟩
          induction e' using Sym2.ind with
          | h a b =>
            simp only [Sym2.map_mk, Sym2.eq_iff] at he'
            rcases he' with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact hw' ⟨b, rfl⟩
            · exact hw' ⟨a, rfl⟩
    · refine ⟨0, fun w _ => ?_⟩
      rw [liftE_of_not (ι := ι) x]
      · simp
      · rintro ⟨e', he'⟩
        induction e' using Sym2.ind with
        | h a b =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at he'
          rcases he' with ⟨rfl, -⟩ | ⟨-, rfl⟩
          · exact hv ⟨a, rfl⟩
          · exact hv ⟨b, rfl⟩

include hι in
/-- the restriction of a local profile of `G` is a local profile of `G.comap ι`, and its zero
extension gives back the original vector -/
theorem isLocalProfile_pull [Fintype X] [Fintype V] (hG : EdgesIn G ι) {x : Sym2 V → ℤ}
    (hx : IsLocalProfile G lab F x) :
    IsLocalProfile (G.comap ι) (lab ∘ ι) F (x ∘ Sym2.map ι) ∧
      liftE (ι := ι) (x ∘ Sym2.map ι) = x := by
  refine ⟨⟨fun e he => hx.1 _ fun h => he ((mem_edges_comap e).2 h), fun v0 => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hx.2 (ι v0)
    refine ⟨fun T' => c (T'.map (emb hι)), fun w0 hw => ?_⟩
    have hne : ι w0 ≠ ι v0 := fun h => hw (hι h)
    simp only [Function.comp, Sym2.map_mk]
    rw [hc (ι w0) hne, allowedAt_map hι hG, Finset.sum_map]
    rfl
  · funext e
    by_cases h : ∃ e', Sym2.map ι e' = e
    · obtain ⟨e', rfl⟩ := h
      rw [liftE_map hι]; rfl
    · rw [liftE_of_not (ι := ι) _ h]
      symm
      apply hx.1
      intro he
      induction e using Sym2.ind with
      | h a b =>
        have hadj : G.Adj a b := by simpa [mem_edges] using he
        obtain ⟨x0, hx0⟩ := hG a b hadj
        obtain ⟨y0, hy0⟩ := hG b a hadj.symm
        exact h ⟨s(x0, y0), by simp [hx0, hy0]⟩

end lift

end S07V42
