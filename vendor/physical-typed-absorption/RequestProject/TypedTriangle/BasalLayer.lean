/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalEnvelope
public import RequestProject.Selectors.SimulSchedule
@[expose] public section

/-! Paying the empty mode of a finite simultaneous layer with one common envelope.
The payment is chosen before the demand; every allowed mode retains an exact positive
partition, bounded degree and the actual integer physical lattice. This does not
construct the random core required to remove a majority of the host's roots. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Envelope
open SelSimul SelBridge
variable {V I : Type*} [Fintype V]

lemma triE_eq_triEdges {H : Host V I} {F : Set (Multiset I)} {v x y : V}
    (hT : IsAllowed H F {v,x,y}) : triE v s(x,y) = triEdges {v,x,y} := by
  obtain ⟨hvx,hvy,hxy⟩ := distinct_of_card_three hT.1
  rw [triEdges_eq_insert_wedge hvx hvy hxy]
  ext e
  simp only [triE,Sym2.lift_mk,wedge,mem_insert,mem_singleton]
  tauto

/-- Convert the indexed typed packing of V21 into a genuine basal edge set. -/
theorem rooted_packing_basal {H : Host V I} {F : Set (Multiset I)}
    (D : Finset (V × Sym2 V))
    (hD : (D : Set (V × Sym2 V)).PairwiseDisjoint (fun p => triE p.1 p.2))
    (ht : ∀ p ∈ D, ∃ x y, p.2 = s(x,y) ∧ IsAllowed H F {p.1,x,y}) :
    Basal H F (packEdges D) := by
  apply basal_biUnion D (fun p => triE p.1 p.2) ?_ hD
  intro p hp
  obtain ⟨x,y,he,hT⟩ := ht p hp
  rw [he,triE_eq_triEdges hT]
  exact basal_triEdges hT

lemma extend_mode {R L P Y W : Finset (Sym2 V)}
    (hpart : R ∪ L = P ∪ Y) (hd : Disjoint P Y) (hW : Disjoint W (R ∪ L)) :
    (R ∪ W) ∪ L = P ∪ (Y ∪ W) ∧ Disjoint P (Y ∪ W) := by
  have hP : P ⊆ R ∪ L := by rw [hpart]; exact subset_union_left
  refine ⟨?_,disjoint_union_right.mpr ⟨hd,(hW.mono_right hP).symm⟩⟩
  calc (R ∪ W) ∪ L = (R ∪ L) ∪ W := by ext e; simp only [mem_union]; tauto
    _ = P ∪ (Y ∪ W) := by rw [hpart,union_assoc]

lemma mode_residue_physical {H : Host V I} {F : Set (Multiset I)}
    {R L P Y : Finset (Sym2 V)} (hR : Basal H F R) (hL : IsPhysical H F L)
    (hRL : Disjoint R L) (hP : Basal H F P) (hpart : R ∪ L = P ∪ Y)
    (hd : Disjoint P Y) : IsPhysical H F Y := by
  obtain ⟨DR,hDR⟩ := hR
  obtain ⟨DP,hDP⟩ := hP
  have hphys := isPhysical_union (isPhysical_of_isDecomposition hDR) hL hRL
  have hsub : P ⊆ R ∪ L := by rw [hpart]; exact subset_union_left
  have hleft : (R ∪ L) \ P = Y := by
    rw [hpart]
    ext e
    have hp : e ∈ Y → e ∉ P := fun he => disjoint_left.mp hd.symm he
    simp only [mem_sdiff,mem_union]
    tauto
  rw [← hleft]
  exact isPhysical_sdiff_of_decomposition hphys hDP hsub

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj]
  {Z : Finset V} {Adm : V → Finset V → Prop} {A q : ℕ} {σ : V → SelSimul.LocalSel V}

lemma empty_residual_hasTri (h : SimulFamily G lab F X B0 Z Adm A q σ)
    {e : Sym2 V} (he : e ∈ residual X Z σ ∅) :
    HasTri (⟨G,lab⟩ : Host V I) F e := by
  simp only [SelSimul.residual,filter_empty,union_empty,SelSimul.tokens,mem_biUnion,mem_sdiff] at he
  obtain ⟨v,hv,heP,_⟩ := he
  obtain ⟨x,y,hexy,hxy⟩ := (h.valid v hv).typed e heP
  have ht : IsAllowed (⟨G,lab⟩ : Host V I) F {v,x,y} := hxy.2
  refine ⟨{v,x,y},ht,?_⟩
  rw [hexy]
  exact mem_triEdges.mpr ⟨by simp,by simp,hxy.1⟩

lemma assignment_wings_avoid {H : Host V I} {F : Set (Multiset I)}
    {E B : Finset (Sym2 V)} {Z : Finset V} {q : ℕ} {ap : Sym2 V → V}
    (h : Assignment H F E B Z q E ap)
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∉ Z) :
    ∀ f ∈ wings E ap, ∀ v ∈ f, v ∉ Z := by
  intro f hf v hv
  obtain ⟨e,he,hf⟩ := mem_biUnion.mp hf
  obtain ⟨u,hu,rfl⟩ := mem_wedgeOf.mp hf
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact hE e he _ hu
  · exact h.avoid e he

/-- One common payment makes the fuel and its empty residual basal, and works
for every admissible demand. No assumption that the original fuel is basal is made.
The displayed window is for a finite small-root layer, not the all-root S07 layer. -/
theorem paid_simultaneous_family (h : SimulFamily G lab F X B0 Z Adm A q σ)
    {α : ℝ} (hH3 : CommonNbrCond (⟨G,lab⟩ : Host V I) F α)
    {r b p : ℕ} (hp : 0 < p)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    (hwin : ((Z.card + (residual X Z σ ∅).card / p +
      2 * (max (A * r) (60 * r + 61 * q) + r + b +
        3 * (61 * r + 60 * q) + 2 * p) : ℕ) : ℝ) < α * Fintype.card V) :
    ∃ W : Finset (Sym2 V),
      Disjoint W (fuelU Z σ ∪ X.edgeFinset ∪ B0.edgeFinset) ∧
      Disjoint (fuelU Z σ ∪ W) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ W) ∧
      Basal (⟨G,lab⟩ : Host V I) F (residual X Z σ ∅ ∪ W) ∧
      (∀ f ∈ W, ∀ v ∈ f, v ∉ Z) ∧
      (∀ v, edeg W v ≤ 2 * (61 * r + 60 * q + p)) ∧
      (∀ v, edeg (fuelU Z σ ∪ W) v ≤ max (A * r) (60 * r + 61 * q) +
        2 * (61 * r + 60 * q + p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset →
        (∀ v ∈ Z, Adm v (demand X L v)) →
        (fuelU Z σ ∪ W) ∪ L = packEdges (packing X Z σ L) ∪ (residual X Z σ L ∪ W) ∧
        Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L ∪ W) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ residual X Z σ L ∪ W, ∀ v ∈ Z, v ∉ f) ∧
        (∀ v, edeg (residual X Z σ L ∪ W) v ≤ 3 * (61 * r + 60 * q) + 2 * p) ∧
        (IsPhysical (⟨G,lab⟩ : Host V I) F L →
          IsPhysical (⟨G,lab⟩ : Host V I) F (residual X Z σ L ∪ W)) := by
  classical
  let R := fuelU Z σ
  let K := residual X Z σ ∅
  let B := R ∪ X.edgeFinset ∪ B0.edgeFinset
  have hadm0 : ∀ v ∈ Z, Adm v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  obtain ⟨_,hpart0,hd0,hpack0,ht0,hKZ,hKd⟩ := h.layer_partition hZ hX (empty_subset _) hadm0
  simp only [union_empty] at hpart0
  have hKsub : K ⊆ R := by
    change residual X Z σ ∅ ⊆ fuelU Z σ
    rw [hpart0]; exact subset_union_right
  have hP0 := rooted_packing_basal (H := (⟨G,lab⟩ : Host V I)) (F := F) (packing X Z σ ∅) hpack0 (fun z hz => by
    obtain ⟨_,x,y,he,hxy,hT⟩ := ht0 z hz; exact ⟨x,y,he,hT⟩)
  have hRK : Basal (⟨G,lab⟩ : Host V I) F (R \ K) := by
    apply hP0.congr
    change packEdges (packing X Z σ ∅) = fuelU Z σ \ residual X Z σ ∅
    rw [hpart0]
    ext e
    have hd : e ∈ packEdges (packing X Z σ ∅) → e ∉ K := fun he => disjoint_left.mp hd0 he
    simp only [mem_sdiff,mem_union]
    tauto
  have hBd : ∀ v, edeg B v ≤ max (A * r) (60 * r + 61 * q) + r + b := by
    intro v
    have h1 := edeg_union_le (R ∪ X.edgeFinset) B0.edgeFinset v
    have h2 := edeg_union_le R X.edgeFinset v
    have h3 := h.fuelU_edeg_le hZ hX v
    change edeg R v ≤ _ at h3
    rw [edeg_edgeFinset] at h1 h2
    have h4 := hX v
    have h5 := hB v
    change edeg B v ≤ _
    dsimp [B]
    omega
  obtain ⟨ap,ha⟩ := assignment_of_H3 hH3 K B Z hp hKd hBd
    (fun e he => empty_residual_hasTri h he) hwin
  let W := wings K ap
  have hWfresh : Disjoint W (K ∪ B) := by
    dsimp only [W,wings]; rw [disjoint_biUnion_left]; exact ha.fresh
  have hWB : Disjoint W B := hWfresh.mono_right subset_union_right
  have hWR : Disjoint W R := hWB.mono_right (fun e he => mem_union_left _ (mem_union_left _ he))
  have hKW : Basal (⟨G,lab⟩ : Host V I) F (K ∪ W) := ha.envelope_basal
  have hRW := pay_empty_mode hKsub hRK hKW hWR
  have hWd : ∀ v, edeg W v ≤ 2 * (61 * r + 60 * q + p) :=
    wings_degree_le K K ap subset_rfl hKd ha.cnt
  have hWZ := assignment_wings_avoid ha (fun e he v hv hvZ => hKZ e he v hvZ hv)
  have hWX : Disjoint W (X.edgeFinset ∪ B0.edgeFinset) := hWB.mono_right (by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_union_right _ he)
    · exact mem_union_right _ he)
  have hFW := disjoint_union_left.mpr ⟨h.fuelU_avoid,hWX⟩
  refine ⟨W,hWB,hFW,hRW,hKW,hWZ,hWd,?_,?_⟩
  · intro v
    exact (edeg_union_le _ _ v).trans
      (Nat.add_le_add (h.fuelU_edeg_le hZ hX v) (hWd v))
  · intro L hL hadm
    obtain ⟨hRL,hpart,hd,hpack,ht,hYZ,hYd⟩ := h.layer_partition hZ hX hL hadm
    have hWL : Disjoint W (R ∪ L) := hWB.mono_right (fun e he => by
      rcases mem_union.mp he with he | he
      · exact mem_union_left _ (mem_union_left _ he)
      · exact mem_union_left _ (mem_union_right _ (hL he)))
    obtain ⟨heq,hdisj⟩ := extend_mode hpart hd hWL
    have hPB := rooted_packing_basal (H := (⟨G,lab⟩ : Host V I)) (F := F) (packing X Z σ L) hpack (fun z hz => by
      obtain ⟨_,x,y,he,hxy,hT⟩ := ht z hz; exact ⟨x,y,he,hT⟩)
    refine ⟨heq,hdisj,hPB,?_,?_,?_⟩
    · intro f hf v hv
      rcases mem_union.mp hf with hf | hf
      · exact hYZ f hf v hv
      · exact fun hvf => hWZ f hf v hvf hv
    · intro v
      have h1 := edeg_union_le (residual X Z σ L) W v
      have h2 := hYd v
      have h3 := hWd v
      omega
    · intro hphys
      have hRWL : Disjoint (R ∪ W) L := disjoint_union_left.mpr
        ⟨hRL,(hWL.mono_right subset_union_right)⟩
      exact mode_residue_physical hRW hphys hRWL hPB heq hdisj

end TypedTriangle.Envelope
