/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.Theorem12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone
variable {E ι : Type*} [Fintype E] [Fintype ι]

abbrev Copy (m : ι → ℕ) := Σ i, Fin (m i)

/-- A private tag keeps copies distinct as hyperedges without changing the
original conflicts. This prevents Finset from silently collapsing copies. -/
def packet (P : ι → Finset E) (m : ι → ℕ) (c : Copy m) : Finset (E ⊕ Copy m) :=
  (P c.1).map Function.Embedding.inl ∪ {Sum.inr c}

lemma mem_packet_left (P : ι → Finset E) (m : ι → ℕ) (c : Copy m) (e : E) :
    Sum.inl e ∈ packet P m c ↔ e ∈ P c.1 := by simp [packet]

lemma mem_packet_right (P : ι → Finset E) (m : ι → ℕ) (c d : Copy m) :
    Sum.inr c ∈ packet P m d ↔ c=d := by simp [packet]

lemma packet_injective (P : ι → Finset E) (m : ι → ℕ) :
    Function.Injective (packet P m) := by
  intro c d h
  apply (mem_packet_right P m c d).mp
  rw [←h]
  exact (mem_packet_right P m c c).mpr rfl

lemma packet_card (P : ι → Finset E) (m : ι → ℕ) (c : Copy m) :
    (packet P m c).card=(P c.1).card+1 := by
  rw [packet,card_union_of_disjoint]
  · simp
  · apply disjoint_singleton_right.mpr
    simp

lemma packet_disjoint (P : ι → Finset E) (m : ι → ℕ) {c d : Copy m} (hcd : c≠d) :
    Disjoint (packet P m c) (packet P m d) ↔ Disjoint (P c.1) (P d.1) := by
  constructor
  · intro h
    apply disjoint_left.mpr
    intro e he hf
    exact disjoint_left.mp h ((mem_packet_left P m c e).mpr he) ((mem_packet_left P m d e).mpr hf)
  · intro h
    apply disjoint_left.mpr
    intro v hv hw
    cases v with
    | inl e => exact disjoint_left.mp h ((mem_packet_left P m c e).mp hv) ((mem_packet_left P m d e).mp hw)
    | inr a => exact hcd (((mem_packet_right P m a c).mp hv).symm.trans ((mem_packet_right P m a d).mp hw))

def hypergraph (P : ι → Finset E) (m : ι → ℕ) : Finset (Finset (E ⊕ Copy m)) :=
  univ.image (packet P m)

lemma hypergraph_uniform (P : ι → Finset E) (m : ι → ℕ) {r : ℕ}
    (hr : ∀ i, (P i).card=r) : Pseudorandom.IsUniform (hypergraph P m) (r+1) := by
  intro T hT
  obtain ⟨c,_,rfl⟩ := mem_image.mp hT
  rw [packet_card,hr]

def liftedWeight (P : ι → Finset E) (m : ι → ℕ) (w : ι → ℝ)
    (T : Finset (E ⊕ Copy m)) : ℝ :=
  if hc : ∃ c : Copy m, packet P m c=T then w (Classical.choose hc).1 else 0

lemma liftedWeight_packet (P : ι → Finset E) (m : ι → ℕ) (w : ι → ℝ) (c : Copy m) :
    liftedWeight P m w (packet P m c)=w c.1 := by
  rw [liftedWeight,dif_pos ⟨c,rfl⟩]
  have h := packet_injective P m (Classical.choose_spec (show ∃ d, packet P m d=packet P m c from ⟨c,rfl⟩))
  rw [h]

lemma weight_hypergraph (P : ι → Finset E) (m : ι → ℕ) (w : ι → ℝ) :
    Pseudorandom.weight (liftedWeight P m w) (hypergraph P m)=∑ i, (m i:ℝ)*w i := by
  unfold Pseudorandom.weight hypergraph
  rw [sum_image]
  · simp_rw [liftedWeight_packet]
    rw [Fintype.sum_sigma]
    simp [smul_eq_mul]
  · intro c _ d _ h
    exact packet_injective P m h

lemma extract_matching (P : ι → Finset E) (m : ι → ℕ)
    {M : Finset (Finset (E ⊕ Copy m))} (hM : M⊆hypergraph P m)
    (hMatch : Pseudorandom.IsMatching M) :
    ∃ C : Finset (Copy m), M=C.image (packet P m) ∧
      (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) ∧
      ∀ w : ι → ℝ, Pseudorandom.weight (liftedWeight P m w) M=∑ c ∈ C, w c.1 := by
  let C := univ.filter (fun c => packet P m c ∈ M)
  have heq : M=C.image (packet P m) := by
    ext T
    constructor
    · intro hT
      obtain ⟨c,_,hc⟩ := mem_image.mp (hM hT)
      exact mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,hc ▸ hT⟩,hc⟩
    · rintro hT
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hT
      exact (mem_filter.mp hc).2
  refine ⟨C,heq,?_,?_⟩
  · intro c hc d hd hcd
    exact (packet_disjoint P m hcd).mp (hMatch _ (mem_filter.mp hc).2 _ (mem_filter.mp hd).2
      (fun h => hcd (packet_injective P m h)))
  · intro w
    rw [heq,Pseudorandom.weight,sum_image]
    · exact sum_congr rfl fun c _ => liftedWeight_packet P m w c
    · intro c _ d _ h
      exact packet_injective P m h

lemma degree_left (P : ι → Finset E) (m : ι → ℕ) (e : E) :
    Pseudorandom.degree (hypergraph P m) (Sum.inl e)=
      ∑ i, if e∈P i then m i else 0 := by
  unfold Pseudorandom.degree hypergraph
  rw [filter_image,card_image_of_injective _ (packet_injective P m)]
  simp_rw [mem_packet_left]
  rw [card_filter]
  rw [Fintype.sum_sigma]
  simp only [sum_const,smul_eq_mul]
  apply sum_congr rfl
  intro i _
  by_cases hi : e∈P i <;> simp [hi]

lemma degree_right (P : ι → Finset E) (m : ι → ℕ) (c : Copy m) :
    Pseudorandom.degree (hypergraph P m) (Sum.inr c)=1 := by
  unfold Pseudorandom.degree hypergraph
  rw [filter_image,card_image_of_injective _ (packet_injective P m)]
  simp_rw [mem_packet_right]
  have hf : (univ.filter (fun d : Copy m => c=d))={c} := by
    ext d
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact eq_comm
  exact (congrArg Finset.card hf).trans (card_singleton c)

lemma codegree_left (P : ι → Finset E) (m : ι → ℕ) (e f : E) :
    Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inl f)=
      ∑ i, if e∈P i ∧ f∈P i then m i else 0 := by
  unfold Pseudorandom.codegree hypergraph
  rw [filter_image,card_image_of_injective _ (packet_injective P m)]
  simp_rw [mem_packet_left]
  rw [card_filter,Fintype.sum_sigma]
  simp only [sum_const,smul_eq_mul]
  apply sum_congr rfl
  intro i _
  by_cases hi : e∈P i ∧ f∈P i <;> simp [hi]

lemma codegree_mixed_le (P : ι → Finset E) (m : ι → ℕ) (e : E) (c : Copy m) :
    Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c)≤1 := by
  unfold Pseudorandom.codegree
  have hs : (hypergraph P m).filter (fun T => Sum.inl e∈T ∧ Sum.inr c∈T) ⊆
      (hypergraph P m).filter (fun T => Sum.inr c∈T) := by
    intro T hT
    exact mem_filter.mpr ⟨(mem_filter.mp hT).1,(mem_filter.mp hT).2.2⟩
  apply (card_le_card hs).trans
  exact le_of_eq (degree_right P m c)

lemma codegree_right_eq_zero (P : ι → Finset E) (m : ι → ℕ) {c d : Copy m} (hcd : c≠d) :
    Pseudorandom.codegree (hypergraph P m) (Sum.inr c) (Sum.inr d)=0 := by
  unfold Pseudorandom.codegree
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro T hT hv
  obtain ⟨a,_,rfl⟩ := mem_image.mp hT
  exact hcd (((mem_packet_right P m c a).mp hv.1).trans ((mem_packet_right P m d a).mp hv.2).symm)

lemma hypergraph_card (P : ι → Finset E) (m : ι → ℕ) :
    (hypergraph P m).card=∑ i, m i := by
  rw [hypergraph,card_image_of_injective _ (packet_injective P m),card_univ,Fintype.card_sigma]
  simp

end TypedTriangle.WeightedClone
