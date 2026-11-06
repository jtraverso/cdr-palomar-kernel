/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalBlockSampling
public import RequestProject.TypedTriangle.Packing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Actual packing incidence for sampling entire basal blocks. Owners refer to
real triangles in the supplied packing; no hypothetical block provider occurs. -/

noncomputable section
open Finset Classical
namespace TypedTriangle.BasalIncidence
variable {V I : Type*} [Fintype V]

def cover (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion triEdges

def owner (P : Finset (Finset V)) (e : Sym2 V) (he : e ∈ cover P) : P :=
  ⟨Classical.choose (mem_biUnion.mp he), (Classical.choose_spec (mem_biUnion.mp he)).1⟩

lemma owner_edge (P : Finset (Finset V)) (e : Sym2 V) (he : e ∈ cover P) :
    e ∈ triEdges (owner P e he).val := (Classical.choose_spec (mem_biUnion.mp he)).2

def good (H : Host V I) (F : Set (Multiset I)) (P : Finset (Finset V)) (u v : V) : Finset V :=
  univ.filter fun w => IsAllowed H F {u,v,w} ∧ s(u,w) ∈ cover P ∧ s(v,w) ∈ cover P

def dep (H : Host V I) (F : Set (Multiset I)) (P : Finset (Finset V)) (u v w : V) : Finset P :=
  if hw : w ∈ good H F P u v then
    {owner P s(u,w) (mem_filter.mp hw).2.2.1,
     owner P s(v,w) (mem_filter.mp hw).2.2.2}
  else ∅

def stock {P : Finset (Finset V)} (W : Finset P) : Finset (Sym2 V) :=
  W.biUnion fun T => triEdges T.val

def selected {P : Finset (Finset V)} (W : Finset P) : Finset (Finset V) := W.image Subtype.val

lemma stock_eq_selected {P : Finset (Finset V)} (W : Finset P) :
    stock W = (selected W).biUnion triEdges := by rw [selected, image_biUnion]; rfl

lemma selected_subset {P : Finset (Finset V)} (W : Finset P) : selected W ⊆ P := by
  intro T hT
  obtain ⟨b, _, rfl⟩ := mem_image.mp hT
  exact b.property

theorem selected_decomposition {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (W : Finset P) :
    IsDecomposition H F (stock W) (selected W) := by
  rw [stock_eq_selected]
  apply IsPacking.isDecomposition
  exact ⟨fun T hT => hP.1 T (selected_subset W hT),
    fun T hT U hU hne => hP.2 (selected_subset W hT) (selected_subset W hU) hne⟩

lemma dep_card (H : Host V I) (F : Set (Multiset I)) (P : Finset (Finset V)) (u v w : V) :
    (dep H F P u v w).card ≤ 2 := by
  unfold dep
  split_ifs
  · exact card_le_two
  · simp

lemma dep_support {H : Host V I} {F : Set (Multiset I)} {P : Finset (Finset V)} {u v w : V}
    {b : P} (hb : b ∈ dep H F P u v w) : w ∈ b.val := by
  unfold dep at hb
  split_ifs at hb with hw
  · rcases mem_insert.mp hb with hb | hb
    · subst b
      exact (mem_triEdges.mp (owner_edge P s(u,w) (mem_filter.mp hw).2.2.1)).2.1
    · have hb' := mem_singleton.mp hb
      subst b
      exact (mem_triEdges.mp (owner_edge P s(v,w) (mem_filter.mp hw).2.2.2)).2.1
  · exact False.elim (notMem_empty b hb)

theorem dep_load_le_four {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (u v : V) (b : P) :
    (((good H F P u v).filter (fun w => b ∈ dep H F P u v w)).card : ℝ) ≤ 4 := by
  apply BasalSampling.completion_load_le_four (good H F P u v) (dep H F P u v) Subtype.val
  · intro w _ b hb
    exact dep_support hb
  · intro b
    exact (hP.1 b.val b.property).1.le

theorem retained_wings {H : Host V I} {F : Set (Multiset I)} {P : Finset (Finset V)}
    {u v w : V} (hw : w ∈ good H F P u v) (W : Finset P)
    (hret : dep H F P u v w ⊆ W) :
    IsAllowed H F {u,v,w} ∧ s(u,w) ∈ stock W ∧ s(v,w) ∈ stock W := by
  have hh := (mem_filter.mp hw).2
  refine ⟨hh.1, ?_, ?_⟩
  · have hb : owner P s(u,w) hh.2.1 ∈ dep H F P u v w := by simp [dep, hw]
    exact mem_biUnion.mpr ⟨_,hret hb,owner_edge P s(u,w) hh.2.1⟩
  · have hb : owner P s(v,w) hh.2.2 ∈ dep H F P u v w := by simp [dep, hw]
    exact mem_biUnion.mpr ⟨_,hret hb,owner_edge P s(v,w) hh.2.2⟩

lemma root_block_card {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (v : V) :
    ((univ : Finset P).filter (fun b => v ∈ b.val)).card ≤ Fintype.card V := by
  let A : Finset P := univ.filter fun b => v ∈ b.val
  have hex : ∀ b : P, v ∈ b.val → ∃ w ∈ b.val, w ≠ v := by
    intro b _
    exact exists_mem_ne (by rw [(hP.1 b.val b.property).1]; norm_num) v
  let f : P → V := fun b => if hv : v ∈ b.val then Classical.choose (hex b hv) else v
  have hf : ∀ b ∈ A, f b ∈ b.val ∧ f b ≠ v := by
    intro b hb
    have hv : v ∈ b.val := (mem_filter.mp hb).2
    simpa only [f, dif_pos hv] using Classical.choose_spec (hex b hv)
  have hinj : Set.InjOn f (A : Set P) := by
    intro b hb c hc heq
    apply Subtype.ext
    by_contra hne
    have hd := hP.2 b.property c.property hne
    have hbe : s(v,f b) ∈ triEdges b.val :=
      mem_triEdges.mpr ⟨(mem_filter.mp hb).2,(hf b hb).1,(hf b hb).2.symm⟩
    have hce : s(v,f b) ∈ triEdges c.val := by
      rw [heq]
      exact mem_triEdges.mpr ⟨(mem_filter.mp hc).2,(hf c hc).1,(hf c hc).2.symm⟩
    exact disjoint_left.mp hd hbe hce
  calc
    A.card ≤ (univ : Finset V).card := card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj
    _ = Fintype.card V := card_univ

lemma vertex_mem_of_edge {T : Finset V} {e : Sym2 V} {v : V}
    (he : e ∈ triEdges T) (hv : v ∈ e) : v ∈ T := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (mem_triEdges.mp he).1
    · exact (mem_triEdges.mp he).2.1

theorem stock_degree_le {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (W : Finset P) (v : V) :
    ((stock W).filter (fun e => v ∈ e)).card ≤
      3 * (W.filter (fun b => v ∈ b.val)).card := by
  unfold stock
  rw [filter_biUnion]
  calc
    _ ≤ ∑ b ∈ W, ((triEdges b.val).filter (fun e => v ∈ e)).card := card_biUnion_le
    _ ≤ ∑ b ∈ W, if v ∈ b.val then 3 else 0 := by
      apply sum_le_sum
      intro b _
      by_cases hv : v ∈ b.val
      · rw [if_pos hv]
        exact (card_filter_le _ _).trans (by rw [card_triEdges_three (hP.1 b.val b.property).1])
      · rw [if_neg hv, Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
        intro e he hve
        exact hv (vertex_mem_of_edge he hve)
    _ = _ := by
      rw [card_filter, mul_sum]
      apply sum_congr rfl
      intro b _
      by_cases hv : v ∈ b.val <;> simp [hv]

lemma selected_load_eq {P : Finset (Finset V)} (W : Finset P) (v : V) :
    S07V24.ccount ((univ : Finset P).filter (fun b => v ∈ b.val))
      (fun b => {b}) W = (W.filter (fun b => v ∈ b.val)).card := by
  unfold S07V24.ccount
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, singleton_subset_iff]
  tauto

/-- The actual graph-valued reserve: a selected subpacking is exactly basal,
locally sparse and retains many completion wings. The supply premise is an
intermediate interface; its derivation from H1/H3 is a separate obligation. -/
theorem sample_packing (q β : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (I : Type) (H : Host V I)
      (F : Set (Multiset I)) (P : Finset (Finset V)), IsPacking H F P →
      n₀ ≤ Fintype.card V → ∀ (τ : Type) [Fintype τ] (u v : τ → V),
      Fintype.card τ ≤ Fintype.card V ^ 2 →
      (∀ t, β * Fintype.card V ≤ (good H F P (u t) (v t)).card) →
      ∃ D ⊆ P, IsDecomposition H F (cover D) D ∧
        (∀ x, (((cover D).filter (fun e => x ∈ e)).card : ℝ) < 6 * q * Fintype.card V) ∧
        ∀ t, β * Fintype.card V * q ^ 2 / 2 ≤ (good H F D (u t) (v t)).card := by
  obtain ⟨n₀, hn₀⟩ := BasalSampling.sampling_window hq hβ
  refine ⟨n₀, ?_⟩
  intro V _ I H F P hP hn τ _ u v hτ hmass
  let S : V → Finset P := fun x => univ.filter (fun b => x ∈ b.val)
  let J : τ → Finset V := fun t => good H F P (u t) (v t)
  let d : τ → V → Finset P := fun t => dep H F P (u t) (v t)
  obtain ⟨W, hsmall, hcenters⟩ := BasalSampling.simultaneous_sample
    q (Fintype.card V) (β * Fintype.card V) hq hq1 S J d
    (fun x => by exact_mod_cast root_block_card hP x) hmass
    (fun t w _ => dep_card H F P (u t) (v t) w)
    (fun t b => dep_load_le_four hP (u t) (v t) b)
    (hn₀ (Fintype.card V) (Fintype.card V) (Fintype.card τ) hn le_rfl hτ)
  refine ⟨selected W, selected_subset W, ?_, ?_, ?_⟩
  · simpa only [cover, stock_eq_selected] using selected_decomposition hP W
  · intro x
    have hNat := stock_degree_le hP W x
    rw [stock_eq_selected] at hNat
    have hBound : (((cover (selected W)).filter (fun e => x ∈ e)).card : ℝ) ≤
        3 * ((W.filter (fun b => x ∈ b.val)).card : ℝ) := by exact_mod_cast hNat
    have hSmall : ((W.filter (fun b => x ∈ b.val)).card : ℝ) < 2 * q * Fintype.card V := by
      simpa only [S, selected_load_eq] using hsmall x
    linarith
  · intro t
    have hsub : (J t).filter (fun w => d t w ⊆ W) ⊆ good H F (selected W) (u t) (v t) := by
      intro w hw
      obtain ⟨hwJ, hret⟩ := mem_filter.mp hw
      have hh := retained_wings hwJ W hret
      refine mem_filter.mpr ⟨mem_univ _, hh.1, ?_, ?_⟩
      · simpa only [stock_eq_selected, cover] using hh.2.1
      · simpa only [stock_eq_selected, cover] using hh.2.2
    exact (hcenters t).trans (by exact_mod_cast card_le_card hsub)

end TypedTriangle.BasalIncidence
