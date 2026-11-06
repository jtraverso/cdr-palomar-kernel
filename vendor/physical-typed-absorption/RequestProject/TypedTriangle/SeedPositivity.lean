/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SeedTransport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# B3 — Cuenta de perturbación y positividad de la semilla transportada

Sea `B` (aquí `Fst`) un grafo de grado `≤ d` con descomposición `Q`, `μ` un peso con
`0 ≤ μ_T ≤ b/n`, y certificados promediados `cbar_T` con `cbar_T = δ_T` si `T` no toca `B` y
`|cbar_T(S)| ≤ L t^{3 − |S ∩ T|}` (en la aplicación `t = D/n`). Para cada triángulo permitido
superviviente `S`:

  `|ψ_S − μ_S| ≤ (b/n) L [n d (n t³ + 3t²) + 3d (n t² + 3t)] + L [n d t³ + 3 d t²]`,

y con `t = D/n`, `1 ≤ D ≤ n`: `|ψ_S − μ_S| ≤ (16 b + 4) L D³ d / n²`
(`seed_perturbation_scaled`). En consecuencia (`seed_positivity`), si `a/n ≤ μ_S ≤ b/n` y
`(16b+4) L D³ d / n² ≤ a/(2n)`, entonces `a/(2n) ≤ ψ_S ≤ (b + a/2)/n`.

Las constantes `16b + 4` son las de esta cuenta (más holgadas que `11b + 5/3` de S05, porque
se usa `|B| ≤ n d` en lugar de `n d / 2` y una sobrecuenta por aristas); el umbral
existencial absorbe esa holgura.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (g : β → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ s.biUnion t, g x ≤ ∑ i ∈ s, ∑ x ∈ t i, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := g)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, g x := Finset.sum_nonneg fun x _ => hg x
    linarith

/-- Peso `t^{3 − |S ∩ T|}`. -/
def ptw (S : Finset V) (t : ℝ) (T : Finset V) : ℝ := t ^ (3 - (S ∩ T).card)

omit [Fintype V] in
lemma ptw_nonneg {S : Finset V} {t : ℝ} (ht : 0 ≤ t) (T : Finset V) : 0 ≤ ptw S t T :=
  pow_nonneg ht _

omit [Fintype V] in
lemma ptw_le_of_le {S : Finset V} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) {T : Finset V} {k : ℕ}
    (hk : (S ∩ T).card ≤ k) (hk3 : k ≤ 3) : ptw S t T ≤ t ^ (3 - k) :=
  pow_le_pow_of_le_one ht ht1 (by omega)

omit [Fintype V] in
lemma card_inter_insert_le {S X : Finset V} {w : V} :
    (S ∩ insert w X).card ≤ (S ∩ X).card + (if w ∈ S then 1 else 0) := by
  split_ifs with h
  · rw [Finset.inter_insert_of_mem h]; exact Finset.card_insert_le _ _
  · rw [Finset.inter_insert_of_notMem h]; simp

/-- Suma de `t^{3 − |S ∩ (X ∪ {w})|}` sobre todos los `w`, con `|S ∩ X| ≤ k ≤ 2`:
a lo sumo `n t^{3−k} + |S| t^{2−k}`. -/
lemma sum_ptw_insert_le {S X : Finset V} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) {k : ℕ}
    (hk2 : k ≤ 2) (hX : (S ∩ X).card ≤ k) :
    ∑ w, ptw S t (insert w X) ≤ Fintype.card V * t ^ (3 - k) + S.card * t ^ (2 - k) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ S)]
  have h1 : ∑ w ∈ Finset.univ.filter (fun w => w ∈ S), ptw S t (insert w X) ≤
      ∑ _w ∈ Finset.univ.filter (fun w => w ∈ S), t ^ (2 - k) := by
    refine Finset.sum_le_sum fun w hw => ?_
    have hw' : w ∈ S := (Finset.mem_filter.1 hw).2
    have := card_inter_insert_le (S := S) (X := X) (w := w)
    rw [if_pos hw'] at this
    have := ptw_le_of_le (S := S) (T := insert w X) ht ht1 (k := k + 1) (by omega) (by omega)
    rwa [show 3 - (k + 1) = 2 - k by omega] at this
  have h2 : ∑ w ∈ Finset.univ.filter (fun w => w ∉ S), ptw S t (insert w X) ≤
      ∑ _w ∈ Finset.univ.filter (fun w => w ∉ S), t ^ (3 - k) := by
    refine Finset.sum_le_sum fun w hw => ?_
    have hw' : w ∉ S := (Finset.mem_filter.1 hw).2
    have := card_inter_insert_le (S := S) (X := X) (w := w)
    rw [if_neg hw'] at this
    exact ptw_le_of_le ht ht1 (by omega) (by omega)
  rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
  have hc1 : ((Finset.univ.filter (fun w => w ∈ S)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (fun w hw => (Finset.mem_filter.1 hw).2)
  have hc2 : ((Finset.univ.filter (fun w => w ∉ S)).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ _
  have hp1 : 0 ≤ t ^ (2 - k) := pow_nonneg ht _
  have hp2 : 0 ≤ t ^ (3 - k) := pow_nonneg ht _
  nlinarith

omit [Fintype V] in
lemma eq_insert_of_mem_triEdges {T : Finset V} (hT3 : T.card = 3) {f : Sym2 V}
    (hf : f ∈ triEdges T) : ∃ w, T = insert w f.toFinset := by
  have hsub : f.toFinset ⊆ T := toFinset_subset_of_mem_triEdges hf
  have h2 := Sym2.card_toFinset_of_not_isDiag f (not_isDiag_of_mem_triEdges hf)
  have hc : (T \ f.toFinset).card = 1 := by rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hc
  refine ⟨w, ?_⟩
  ext x
  simp only [Finset.mem_insert]
  constructor
  · intro hx
    by_cases hxf : x ∈ f.toFinset
    · exact Or.inr hxf
    · left
      have : x ∈ T \ f.toFinset := Finset.mem_sdiff.2 ⟨hx, hxf⟩
      rw [hw] at this; simpa using this
  · rintro (rfl | hx)
    · have : x ∈ T \ f.toFinset := by rw [hw]; simp
      exact (Finset.mem_sdiff.1 this).1
    · exact hsub hx

lemma sum_triOn_ptw_le {H : Host V I} {F : Set (Multiset I)} (S : Finset V) {t : ℝ}
    (ht : 0 ≤ t) (f : Sym2 V) :
    ∑ T ∈ triOn H F f, ptw S t T ≤ ∑ w, ptw S t (insert w f.toFinset) := by
  have hsub : triOn H F f ⊆ Finset.univ.image (fun w => insert w f.toFinset) := by
    intro T hT
    simp only [triOn, allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨w, hw⟩ := eq_insert_of_mem_triEdges hT.1.1 hT.2
    exact Finset.mem_image.2 ⟨w, Finset.mem_univ _, hw.symm⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => ptw_nonneg ht T).trans ?_
  exact Finset.sum_image_le_of_nonneg fun T _ => ptw_nonneg ht T

omit [Fintype V] in
/-- Aristas de `B` que tocan un conjunto `S`: a lo sumo `|S| d`. -/
lemma card_share_le (Fst : Finset (Sym2 V)) {d : ℕ} (hdeg : ∀ x, degIn Fst x ≤ d)
    (S : Finset V) :
    (Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card ≤ S.card * d := by
  have hsub : Fst.filter (fun f => (S ∩ f.toFinset).Nonempty) ⊆
      S.biUnion (fun x => Fst.filter (fun f => x ∈ f)) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨x, hx⟩ := hf.2
    rw [Finset.mem_inter, Sym2.mem_toFinset] at hx
    exact Finset.mem_biUnion.2 ⟨x, hx.1, Finset.mem_filter.2 ⟨hf.1, hx.2⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ x ∈ S, (Fst.filter (fun f => x ∈ f)).card ≤ ∑ _x ∈ S, d :=
        Finset.sum_le_sum fun x _ => hdeg x
    _ = S.card * d := by rw [Finset.sum_const, smul_eq_mul]

omit [Fintype V] in
lemma mem_triEdges_of_toFinset_subset {S : Finset V} {f : Sym2 V} (hf : ¬ f.IsDiag)
    (h : f.toFinset ⊆ S) : f ∈ triEdges S := by
  induction f using Sym2.ind with
  | _ x y =>
  rw [mem_triEdges]
  exact ⟨h (by simp), h (by simp), fun hxy => hf (by simp [hxy])⟩

/-- **Fuentes que tocan `B`.** Para `S` superviviente (`E(S) ∩ B = ∅`, `|S| = 3`),
`Σ_{T toca B} t^{3−|S∩T|} ≤ n d (n t³ + 3t²) + 3 d (n t² + 3 t)`. -/
theorem touching_sum_le {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (hFst : Fst ⊆ edges H) {d : ℕ} (hdeg : ∀ x, degIn Fst x ≤ d) {S : Finset V}
    (hS3 : S.card = 3) (hSs : Disjoint (triEdges S) Fst) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ T ∈ (allowed H F).filter (fun T => ¬ Disjoint (triEdges T) Fst), ptw S t T ≤
      (Fintype.card V * d) * (Fintype.card V * t ^ 3 + 3 * t ^ 2) +
        3 * d * (Fintype.card V * t ^ 2 + 3 * t) := by
  set n := (Fintype.card V : ℝ)
  have hsub : (allowed H F).filter (fun T => ¬ Disjoint (triEdges T) Fst) ⊆
      Fst.biUnion (triOn H F) := by
    intro T hT
    rw [Finset.mem_filter, Finset.not_disjoint_iff] at hT
    obtain ⟨hTa, f, hfT, hfF⟩ := hT
    exact Finset.mem_biUnion.2 ⟨f, hfF, Finset.mem_filter.2 ⟨hTa, hfT⟩⟩
  have hnd : ∀ f ∈ Fst, ¬ f.IsDiag := fun f hf => by
    have := hFst hf
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact H.G.not_isDiag_of_mem_edgeSet this
  have hper : ∀ f ∈ Fst, ∑ w, ptw S t (insert w f.toFinset) ≤
      if (S ∩ f.toFinset).Nonempty then n * t ^ 2 + 3 * t else n * t ^ 3 + 3 * t ^ 2 := by
    intro f hf
    split_ifs with hsh
    · have hk : (S ∩ f.toFinset).card ≤ 1 := by
        by_contra hk
        push_neg at hk
        have h2 := Sym2.card_toFinset_of_not_isDiag f (hnd f hf)
        have heq : S ∩ f.toFinset = f.toFinset := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_right (by omega)
        have hsubS : f.toFinset ⊆ S := heq ▸ Finset.inter_subset_left
        exact Finset.disjoint_left.1 hSs (mem_triEdges_of_toFinset_subset (hnd f hf) hsubS) hf
      have := sum_ptw_insert_le (S := S) (X := f.toFinset) ht ht1 (k := 1) (by norm_num) hk
      rw [hS3] at this; norm_num at this; linarith
    · have hk : (S ∩ f.toFinset).card ≤ 0 := by
        rw [Nat.le_zero, Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.1 hsh
      have := sum_ptw_insert_le (S := S) (X := f.toFinset) ht ht1 (k := 0) (by norm_num) hk
      rw [hS3] at this; norm_num at this; linarith
  have hA : 0 ≤ n * t ^ 3 + 3 * t ^ 2 := by positivity
  have hB : 0 ≤ n * t ^ 2 + 3 * t := by positivity
  calc ∑ T ∈ (allowed H F).filter (fun T => ¬ Disjoint (triEdges T) Fst), ptw S t T
      ≤ ∑ T ∈ Fst.biUnion (triOn H F), ptw S t T :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => ptw_nonneg ht T
    _ ≤ ∑ f ∈ Fst, ∑ T ∈ triOn H F f, ptw S t T :=
        sum_biUnion_le_of_nonneg _ _ _ (ptw_nonneg ht)
    _ ≤ ∑ f ∈ Fst, ∑ w, ptw S t (insert w f.toFinset) :=
        Finset.sum_le_sum fun f _ => sum_triOn_ptw_le S ht f
    _ ≤ ∑ f ∈ Fst, (if (S ∩ f.toFinset).Nonempty then n * t ^ 2 + 3 * t
          else n * t ^ 3 + 3 * t ^ 2) := Finset.sum_le_sum hper
    _ ≤ ∑ f ∈ Fst, ((n * t ^ 3 + 3 * t ^ 2) +
          if (S ∩ f.toFinset).Nonempty then n * t ^ 2 + 3 * t else 0) := by
        refine Finset.sum_le_sum fun f _ => ?_
        split_ifs <;> linarith
    _ = Fst.card * (n * t ^ 3 + 3 * t ^ 2) +
          (Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card * (n * t ^ 2 + 3 * t) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n * d) * (n * t ^ 3 + 3 * t ^ 2) + 3 * d * (n * t ^ 2 + 3 * t) := by
        have h1 : (Fst.card : ℝ) ≤ n * d := by
          have := (card_le_sum_degIn Fst).trans (Finset.sum_le_sum fun x _ => hdeg x)
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at this
          have h' : ((Fst.card : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) * d := by exact_mod_cast this
          simpa [n] using h'
        have h2 : ((Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card : ℝ) ≤ 3 * d := by
          have := card_share_le Fst hdeg S
          rw [hS3] at this; exact_mod_cast this
        nlinarith

/-- Peso por arista de `B`: `t²` si toca `S`, `t³` si no. -/
def edgeW (S : Finset V) (t : ℝ) (f : Sym2 V) : ℝ :=
  if (S ∩ f.toFinset).Nonempty then t ^ 2 else t ^ 3

omit [Fintype V] in
lemma edgeW_nonneg {S : Finset V} {t : ℝ} (ht : 0 ≤ t) (f : Sym2 V) : 0 ≤ edgeW S t f := by
  unfold edgeW; split_ifs <;> positivity

omit [Fintype V] in
/-- Un triángulo de la descomposición de `B` corta a un superviviente `S` en `≤ 1` vértice. -/
lemma card_inter_le_one_of_disjoint {S T : Finset V} {Fst : Finset (Sym2 V)}
    (hT : triEdges T ⊆ Fst) (hSs : Disjoint (triEdges S) Fst) : (S ∩ T).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
  rw [Finset.mem_inter] at hx hy
  have h1 : s(x, y) ∈ triEdges S := mem_triEdges.2 ⟨hx.1, hy.1, hxy⟩
  have h2 : s(x, y) ∈ triEdges T := mem_triEdges.2 ⟨hx.2, hy.2, hxy⟩
  exact Finset.disjoint_left.1 hSs h1 (hT h2)

omit [Fintype V] in
lemma ptw_le_sum_edgeW {S T : Finset V} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hT3 : T.card = 3) (hST : (S ∩ T).card ≤ 1) :
    ptw S t T ≤ ∑ f ∈ triEdges T, edgeW S t f := by
  by_cases hne : (S ∩ T).Nonempty
  · obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter] at hx
    obtain ⟨y, hyT, hyx⟩ : ∃ y ∈ T, y ≠ x := by
      by_contra hc
      push_neg at hc
      have : T ⊆ {x} := fun z hz => Finset.mem_singleton.2 (hc z hz)
      have := Finset.card_le_card this
      simp at this; omega
    have hf : s(x, y) ∈ triEdges T := mem_triEdges.2 ⟨hx.2, hyT, hyx.symm⟩
    have hw : edgeW S t s(x, y) = t ^ 2 := by
      unfold edgeW
      rw [if_pos ⟨x, Finset.mem_inter.2 ⟨hx.1, by simp⟩⟩]
    have hp : ptw S t T ≤ t ^ 2 := by
      have := ptw_le_of_le (S := S) (T := T) ht ht1 hST (by norm_num)
      simpa using this
    calc ptw S t T ≤ edgeW S t s(x, y) := hw ▸ hp
      _ ≤ ∑ f ∈ triEdges T, edgeW S t f :=
        Finset.single_le_sum (fun f _ => edgeW_nonneg ht f) hf
  · have h0 : (S ∩ T).card ≤ 0 := by
      rw [Nat.le_zero, Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.1 hne
    have hp : ptw S t T ≤ t ^ 3 := by
      have := ptw_le_of_le (S := S) (T := T) ht ht1 h0 (by norm_num)
      simpa using this
    obtain ⟨x, hxT⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨y, hyT, hyx⟩ : ∃ y ∈ T, y ≠ x := by
      by_contra hc
      push_neg at hc
      have : T ⊆ {x} := fun z hz => Finset.mem_singleton.2 (hc z hz)
      have := Finset.card_le_card this
      simp at this; omega
    have hf : s(x, y) ∈ triEdges T := mem_triEdges.2 ⟨hxT, hyT, hyx.symm⟩
    have hw : t ^ 3 ≤ edgeW S t s(x, y) := by
      unfold edgeW; split_ifs
      · exact pow_le_pow_of_le_one ht ht1 (by norm_num)
      · exact le_rfl
    calc ptw S t T ≤ edgeW S t s(x, y) := hp.trans hw
      _ ≤ ∑ f ∈ triEdges T, edgeW S t f :=
        Finset.single_le_sum (fun f _ => edgeW_nonneg ht f) hf

/-- **Fuentes del packing.** Para `S` superviviente y `Q` descomposición de `B`,
`Σ_{T∈Q} t^{3−|S∩T|} ≤ (n d) t³ + 3 d t²`. -/
theorem packing_sum_le {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    {Q : Finset (Finset V)} (hQ : IsDecomposition H F Fst Q) {d : ℕ}
    (hdeg : ∀ x, degIn Fst x ≤ d) {S : Finset V} (hS3 : S.card = 3)
    (hSs : Disjoint (triEdges S) Fst) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ T ∈ Q, ptw S t T ≤ (Fintype.card V * d) * t ^ 3 + 3 * d * t ^ 2 := by
  have hTsub : ∀ T ∈ Q, triEdges T ⊆ Fst := fun T hT => by
    rw [← hQ.2.2]; exact Finset.subset_biUnion_of_mem _ hT
  calc ∑ T ∈ Q, ptw S t T ≤ ∑ T ∈ Q, ∑ f ∈ triEdges T, edgeW S t f :=
        Finset.sum_le_sum fun T hT => ptw_le_sum_edgeW ht ht1 (hQ.1 T hT).1
          (card_inter_le_one_of_disjoint (hTsub T hT) hSs)
    _ = ∑ f ∈ Fst, edgeW S t f := by rw [← hQ.2.2, Finset.sum_biUnion hQ.2.1]
    _ = ∑ f ∈ Fst, (t ^ 3 + if (S ∩ f.toFinset).Nonempty then t ^ 2 - t ^ 3 else 0) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        unfold edgeW; split_ifs <;> ring
    _ = Fst.card * t ^ 3 +
          (Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card * (t ^ 2 - t ^ 3) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card V * d) * t ^ 3 + 3 * d * t ^ 2 := by
        have h1 : (Fst.card : ℝ) ≤ Fintype.card V * d := by
          have := (card_le_sum_degIn Fst).trans (Finset.sum_le_sum fun x _ => hdeg x)
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at this
          exact_mod_cast this
        have h2 : ((Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card : ℝ) ≤ 3 * d := by
          have := card_share_le Fst hdeg S
          rw [hS3] at this; exact_mod_cast this
        have h3 : 0 ≤ t ^ 3 := by positivity
        have h4 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht ht1 (by norm_num)
        have h5 : t ^ 2 - t ^ 3 ≤ t ^ 2 := by linarith
        have h6 : 0 ≤ ((Fst.filter (fun f => (S ∩ f.toFinset).Nonempty)).card : ℝ) := by
          positivity
        nlinarith

/-- **Perturbación de la semilla transportada (B3).** Sea `Q` una descomposición de `B`
(grado `≤ d`), `μ` con `0 ≤ μ_T ≤ b/n` en los triángulos permitidos, y certificados con
`cert_T = δ_T` si `T` no toca `B` y `|cert_T(S)| ≤ L t^{3−|S∩T|}` si lo toca. Para todo
triángulo permitido superviviente `S`,
`|ψ_S − μ_S| ≤ (b/n) L [n d (n t³ + 3t²) + 3d (n t² + 3t)] + L [n d t³ + 3 d t²]`. -/
theorem seed_perturbation {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (hFst : Fst ⊆ edges H) {Q : Finset (Finset V)} (hQ : IsDecomposition H F Fst Q) {d : ℕ}
    (hdeg : ∀ x, degIn Fst x ≤ d) {μ : Finset V → ℝ} {b : ℝ}
    (hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T) (hμb : ∀ T ∈ allowed H F, μ T ≤ b / Fintype.card V)
    (cert : Finset V → Finset V → ℝ) {L t : ℝ} (hL0 : 0 ≤ L) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hδ : ∀ T ∈ allowed H F, Disjoint (triEdges T) Fst → ∀ S, cert T S = if S = T then 1 else 0)
    (hL : ∀ T ∈ allowed H F, ¬ Disjoint (triEdges T) Fst → ∀ S, |cert T S| ≤ L * ptw S t T)
    {S : Finset V} (hS : S ∈ allowed H F) (hSs : Disjoint (triEdges S) Fst) :
    |transported H F μ Q cert S - μ S| ≤
      b / Fintype.card V * L * ((Fintype.card V * d) * (Fintype.card V * t ^ 3 + 3 * t ^ 2) +
        3 * d * (Fintype.card V * t ^ 2 + 3 * t)) +
      L * ((Fintype.card V * d) * t ^ 3 + 3 * d * t ^ 2) := by
  have hS3 : S.card = 3 := by
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hS; exact hS.1
  have hQa : ∀ T ∈ Q, T ∈ allowed H F := fun T hT => by simpa [allowed] using hQ.1 T hT
  have hQt : ∀ T ∈ Q, ¬ Disjoint (triEdges T) Fst := fun T hT hdis => by
    have hsub : triEdges T ⊆ Fst := by rw [← hQ.2.2]; exact Finset.subset_biUnion_of_mem _ hT
    have hne : (triEdges T).Nonempty := by
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by rw [(hQ.1 T hT).1]; norm_num :
        1 < T.card)
      exact ⟨s(x, y), mem_triEdges.2 ⟨hx, hy, hxy⟩⟩
    obtain ⟨f, hf⟩ := hne
    exact Finset.disjoint_left.1 hdis hf (hsub hf)
  set P := (allowed H F).filter (fun T => ¬ Disjoint (triEdges T) Fst)
  have hsplit : ∑ T ∈ allowed H F, μ T * cert T S =
      μ S + ∑ T ∈ P, μ T * cert T S := by
    rw [← Finset.sum_filter_not_add_sum_filter (allowed H F)
      (fun T => ¬ Disjoint (triEdges T) Fst)]
    congr 1
    rw [Finset.sum_eq_single S]
    · have hd : Disjoint (triEdges S) Fst := hSs
      rw [hδ S hS hd S, if_pos rfl, mul_one]
    · intro T hT hTS
      rw [Finset.mem_filter, not_not] at hT
      rw [hδ T hT.1 hT.2 S, if_neg (Ne.symm hTS), mul_zero]
    · intro h; exact absurd (Finset.mem_filter.2 ⟨hS, not_not.2 hSs⟩) h
  have heq : transported H F μ Q cert S - μ S =
      ∑ T ∈ P, μ T * cert T S - ∑ T ∈ Q, cert T S := by
    unfold transported; rw [hsplit]; ring
  rw [heq]
  have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hb : 0 ≤ b / Fintype.card V := le_trans (hμ0 S hS) (hμb S hS)
  have h1 : |∑ T ∈ P, μ T * cert T S| ≤ b / Fintype.card V * L * ∑ T ∈ P, ptw S t T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    rw [Finset.mem_filter] at hT
    rw [abs_mul, abs_of_nonneg (hμ0 T hT.1), mul_assoc]
    exact mul_le_mul (hμb T hT.1) (hL T hT.1 hT.2 S) (abs_nonneg _) hb
  have h2 : |∑ T ∈ Q, cert T S| ≤ L * ∑ T ∈ Q, ptw S t T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun T hT => hL T (hQa T hT) (hQt T hT) S
  have h3 := touching_sum_le (F := F) hFst hdeg hS3 hSs ht ht1
  have h4 := packing_sum_le hQ hdeg hS3 hSs ht ht1
  have hbL : 0 ≤ b / Fintype.card V * L := mul_nonneg hb hL0
  calc |∑ T ∈ P, μ T * cert T S - ∑ T ∈ Q, cert T S|
      ≤ |∑ T ∈ P, μ T * cert T S| + |∑ T ∈ Q, cert T S| := abs_sub _ _
    _ ≤ b / Fintype.card V * L * ∑ T ∈ P, ptw S t T + L * ∑ T ∈ Q, ptw S t T :=
        add_le_add h1 h2
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h3 hbL) (mul_le_mul_of_nonneg_left h4 hL0)

/-- Cuenta escalada: con `t = D/n`, `1 ≤ D ≤ n`, la cota de `seed_perturbation` es
`≤ (16 b + 4) L D³ d / n²`. -/
lemma perturbation_bound_scaled {n D b L d : ℝ} (hn : 0 < n) (hD1 : 1 ≤ D) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hd : 0 ≤ d) :
    b / n * L * ((n * d) * (n * (D / n) ^ 3 + 3 * (D / n) ^ 2) +
        3 * d * (n * (D / n) ^ 2 + 3 * (D / n))) +
      L * ((n * d) * (D / n) ^ 3 + 3 * d * (D / n) ^ 2) ≤
      (16 * b + 4) * L * D ^ 3 * d / n ^ 2 := by
  have hexp : b / n * L * ((n * d) * (n * (D / n) ^ 3 + 3 * (D / n) ^ 2) +
        3 * d * (n * (D / n) ^ 2 + 3 * (D / n))) +
      L * ((n * d) * (D / n) ^ 3 + 3 * d * (D / n) ^ 2) =
      (b * L * d * (D ^ 3 + 6 * D ^ 2 + 9 * D) + L * d * (D ^ 3 + 3 * D ^ 2)) / n ^ 2 := by
    field_simp; ring
  rw [hexp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hD2 : D ^ 2 ≤ D ^ 3 := by nlinarith
  have hD : D ≤ D ^ 3 := by nlinarith
  have hbLd : 0 ≤ b * L * d := by positivity
  have hLd : 0 ≤ L * d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hD2 hbLd, mul_le_mul_of_nonneg_left hD hbLd,
    mul_le_mul_of_nonneg_left hD2 hLd]

/-- **Perturbación escalada (B3).** Con `t = D/n`, `1 ≤ D ≤ n`:
`|ψ_S − μ_S| ≤ (16 b + 4) L D³ d / n²`. -/
theorem seed_perturbation_scaled {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (hFst : Fst ⊆ edges H) {Q : Finset (Finset V)} (hQ : IsDecomposition H F Fst Q) {d : ℕ}
    (hdeg : ∀ x, degIn Fst x ≤ d) {μ : Finset V → ℝ} {b : ℝ}
    (hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T) (hμb : ∀ T ∈ allowed H F, μ T ≤ b / Fintype.card V)
    (cert : Finset V → Finset V → ℝ) {L D : ℝ} (hL0 : 0 ≤ L) (hD1 : 1 ≤ D)
    (hDn : D ≤ Fintype.card V)
    (hδ : ∀ T ∈ allowed H F, Disjoint (triEdges T) Fst → ∀ S, cert T S = if S = T then 1 else 0)
    (hL : ∀ T ∈ allowed H F, ¬ Disjoint (triEdges T) Fst → ∀ S,
      |cert T S| ≤ L * ptw S (D / Fintype.card V) T)
    {S : Finset V} (hS : S ∈ allowed H F) (hSs : Disjoint (triEdges S) Fst) :
    |transported H F μ Q cert S - μ S| ≤ (16 * b + 4) * L * D ^ 3 * d / Fintype.card V ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card V := by linarith
  have ht : 0 ≤ D / Fintype.card V := by positivity
  have ht1 : D / Fintype.card V ≤ 1 := (div_le_one hn).2 hDn
  have hb : 0 ≤ b := by
    have := le_trans (hμ0 S hS) (hμb S hS)
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hn)
  refine (seed_perturbation hFst hQ hdeg hμ0 hμb cert hL0 ht ht1 hδ hL hS hSs).trans ?_
  exact perturbation_bound_scaled hn hD1 hb hL0 (by positivity)

/-- **Positividad de la semilla transportada (B3).** Si `a/n ≤ μ_S ≤ b/n` y
`(16b+4) L D³ d / n² ≤ a/(2n)`, entonces `a/(2n) ≤ ψ_S ≤ (b + a/2)/n`. -/
theorem seed_positivity {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (hFst : Fst ⊆ edges H) {Q : Finset (Finset V)} (hQ : IsDecomposition H F Fst Q) {d : ℕ}
    (hdeg : ∀ x, degIn Fst x ≤ d) {μ : Finset V → ℝ} {a b : ℝ}
    (hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T) (hμb : ∀ T ∈ allowed H F, μ T ≤ b / Fintype.card V)
    (cert : Finset V → Finset V → ℝ) {L D : ℝ} (hL0 : 0 ≤ L) (hD1 : 1 ≤ D)
    (hDn : D ≤ Fintype.card V)
    (hδ : ∀ T ∈ allowed H F, Disjoint (triEdges T) Fst → ∀ S, cert T S = if S = T then 1 else 0)
    (hL : ∀ T ∈ allowed H F, ¬ Disjoint (triEdges T) Fst → ∀ S,
      |cert T S| ≤ L * ptw S (D / Fintype.card V) T)
    (hsmall : (16 * b + 4) * L * D ^ 3 * d / Fintype.card V ^ 2 ≤ a / (2 * Fintype.card V))
    {S : Finset V} (hS : S ∈ allowed H F) (hSs : Disjoint (triEdges S) Fst)
    (hμa : a / Fintype.card V ≤ μ S) :
    a / (2 * Fintype.card V) ≤ transported H F μ Q cert S ∧
      transported H F μ Q cert S ≤ (b + a / 2) / Fintype.card V := by
  have h := (seed_perturbation_scaled hFst hQ hdeg hμ0 hμb cert hL0 hD1 hDn hδ hL hS
    hSs).trans hsmall
  have hn : (0 : ℝ) < Fintype.card V := by linarith
  have e1 : a / Fintype.card V = a / (2 * Fintype.card V) + a / (2 * Fintype.card V) := by
    field_simp; ring
  have e2 : (b + a / 2) / Fintype.card V = b / Fintype.card V + a / (2 * Fintype.card V) := by
    field_simp
  have hb := hμb S hS
  rw [abs_le] at h
  constructor <;> linarith

end TypedTriangle
