/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PreparedAbsorberSupply
public import RequestProject.TypedTriangle.BasalLayer
public import RequestProject.TypedTriangle.PhysicalSelectorEntry
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! Basal payment of the all-root selector layer on its genuine surviving
core, without a small-root cardinality hypothesis. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open CorePayment PreparedSupply SelSimul SelBridge SelTyped
variable {V I : Type*} [Fintype V]

lemma hasTri_roots {H : Host V I} {F : Set (Multiset I)} {u v : V}
    (he : HasTri H F s(u,v)) : ∃ a, IsAllowed H F {u,v,a} := by
  obtain ⟨x,y,a,heq,ha⟩ := he.exists_tri
  rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨a,ha⟩
  · exact ⟨a,by simpa only [Finset.insert_comm] using ha⟩

/-- An edge with surviving endpoints and an ambient allowed triangle has
an allowed completion inside the actual core, by its H3 condition. -/
lemma hasTri_pull_of_core_H3 {H : Host V I} {F : Set (Multiset I)}
    (Z : Finset V) {α : ℝ} (h3 : CommonNbrCond (restrictedHost H Z) F α)
    (hpos : 0 < α*Fintype.card (Survivors Z))
    {e : Sym2 (Survivors Z)} (he : HasTri H F (edgeLift Z e)) :
    HasTri (restrictedHost H Z) F e := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨a,hTa⟩ := hasTri_roots he
    obtain ⟨huv,hua,hva⟩ := distinct_of_card_three hTa.1
    have hne : u ≠ v := fun h => huv (congrArg Subtype.val h)
    have hlab : ({H.lab u.1,H.lab v.1,H.lab a}:Multiset I) ∈ F := by
      have hh := hTa.2.2
      rwa [Finset.insert_val_of_notMem (by simp [huv,hua]),
        Finset.insert_val_of_notMem (by simp [hva])] at hh
    have hc := h3 u v hne (H.lab a) hlab
    obtain ⟨w,hw⟩ : (commonNbrs (restrictedHost H Z) (H.lab a) u v).Nonempty := by
      apply card_pos.mp
      exact_mod_cast hpos.trans_le hc
    have hw' := (mem_filter.mp hw).2
    have hwamb : w.1 ∈ commonNbrs H (H.lab a) u.1 v.1 :=
      mem_filter.mpr ⟨mem_univ _,hw'⟩
    have hTw := allowed_of_commonNbr hTa hwamb
    have heq : liftVertexSet Z {u,v,w} = {u.1,v.1,w.1} := by
      simp [liftVertexSet,survivingVertexEmbedding]
    have hDel : IsAllowed (vertexDeleted H Z) F (liftVertexSet Z {u,v,w}) := by
      apply (isAllowed_vertexDeleted_iff H F Z _).mpr
      exact ⟨heq.symm ▸ hTw,liftVertexSet_avoids Z _⟩
    have hT := (isAllowed_liftVertexSet_iff H F Z {u,v,w}).mpr hDel
    refine ⟨{u,v,w},hT,?_⟩
    exact mem_triEdges.mpr ⟨by simp,by simp,hne⟩

/-- Pay one simultaneous family entirely inside the surviving core. The
root set can occupy almost the whole host: its cardinality is not charged. -/
theorem paid_core_family {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj]
    {Z : Finset V} {Adm : V → Finset V → Prop} {A q : ℕ} {σ : V → LocalSel V}
    (h : SimulFamily G lab F X B0 Z Adm A q σ) {α : ℝ}
    (hH3 : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F α)
    {r b p : ℕ} (hp : 0 < p)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    (hwin : (((residual X Z σ ∅).card / p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z)) :
    ∃ W : Finset (Sym2 V),
      Disjoint W (fuelU Z σ ∪ X.edgeFinset ∪ B0.edgeFinset) ∧
      Disjoint (fuelU Z σ ∪ W) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ W) ∧
      Basal (⟨G,lab⟩ : Host V I) F (residual X Z σ ∅ ∪ W) ∧
      (∀ f ∈ W, ∀ v ∈ f, v ∉ Z) ∧
      (∀ v, edeg W v ≤ 2*(61*r+60*q+p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset →
        (∀ v ∈ Z, Adm v (demand X L v)) →
        (fuelU Z σ ∪ W) ∪ L = packEdges (packing X Z σ L) ∪ (residual X Z σ L ∪ W) ∧
        Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L ∪ W) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ residual X Z σ L ∪ W, ∀ v ∈ f, v ∉ Z) ∧
        (∀ v, edeg (residual X Z σ L ∪ W) v ≤ 3*(61*r+60*q)+2*p) ∧
        (IsPhysical (⟨G,lab⟩ : Host V I) F L →
          IsPhysical (⟨G,lab⟩ : Host V I) F (residual X Z σ L ∪ W)) := by
  let R := fuelU Z σ
  let K := residual X Z σ ∅
  have hadm0 : ∀ v ∈ Z, Adm v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  obtain ⟨_,hpart0,hd0,hpack0,ht0,hKZ,hKd⟩ := h.layer_partition hZ hX (empty_subset _) hadm0
  simp only [union_empty] at hpart0
  have hKsub : K ⊆ R := by
    change residual X Z σ ∅ ⊆ fuelU Z σ
    rw [hpart0]; exact subset_union_right
  have hP0 := Envelope.rooted_packing_basal (H := (⟨G,lab⟩ : Host V I)) (F := F)
    (packing X Z σ ∅) hpack0 (fun z hz => by
      obtain ⟨_,x,y,he,hxy,hT⟩ := ht0 z hz
      exact ⟨x,y,he,hT⟩)
  have hRK : Basal (⟨G,lab⟩ : Host V I) F (R \ K) := by
    apply hP0.congr
    change packEdges (packing X Z σ ∅) = fuelU Z σ \ residual X Z σ ∅
    rw [hpart0]
    ext e
    have hd : e ∈ packEdges (packing X Z σ ∅) → e ∉ K := fun he => disjoint_left.mp hd0 he
    simp only [mem_sdiff,mem_union]
    tauto
  have hProt : ∀ v, edeg (R ∪ X.edgeFinset ∪ B0.edgeFinset) v ≤
      max (A*r) (60*r+61*q)+r+b := by
    intro v
    have h1 := edeg_union_le (R ∪ X.edgeFinset) B0.edgeFinset v
    have h2 := edeg_union_le R X.edgeFinset v
    have h3 := h.fuelU_edeg_le hZ hX v
    have h4 := hX v
    have h5 := hB v
    rw [edeg_edgeFinset] at h1 h2
    change edeg R v ≤ _ at h3
    omega
  have havoid : ∀ e ∈ K, ∀ v ∈ e, v ∉ Z := fun e he v hv hvZ => hKZ e he v hvZ hv
  have hback := lift_pull_eq Z K havoid
  have hpos : 0 < α*Fintype.card (Survivors Z) :=
    (Nat.cast_nonneg _).trans_lt hwin
  have htri : ∀ e ∈ pullEdges Z K, HasTri (restrictedHost (⟨G,lab⟩ : Host V I) Z) F e := by
    intro e he
    exact hasTri_pull_of_core_H3 Z hH3 hpos
      (Envelope.empty_residual_hasTri h (mem_preimage.mp he))
  have hEdeg : ∀ v, edeg (pullEdges Z K) v ≤ 61*r+60*q := by
    intro v
    simpa only [edeg_eq_classical] using (degree_pull_le Z K v).trans (hKd v.1)
  have hEcard : (pullEdges Z K).card ≤ K.card := by
    rw [pullEdges,card_preimage]; exact card_filter_le _ _
  have hwinE : (((pullEdges Z K).card/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z) := by
    have hh := Nat.add_le_add_right (Nat.div_le_div_right (c := p) hEcard)
      (2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p))
    have hhR : (((pullEdges Z K).card/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        ((K.card/p + 2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) := by
      exact_mod_cast hh
    exact hhR.trans_lt hwin
  obtain ⟨W,hW,hWZ,hRW,hKW,hWd⟩ := basal_payment_inside_core Z hH3 (pullEdges Z K)
    R X.edgeFinset B0.edgeFinset hp (by simpa only [hback] using hKsub)
    (by simpa only [hback] using hRK) hEdeg hProt htri hwinE
  have hWX : Disjoint W (X.edgeFinset ∪ B0.edgeFinset) := hW.mono_right (by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_union_right _ he)
    · exact mem_union_right _ he)
  have hKW' : Basal (⟨G,lab⟩ : Host V I) F (K ∪ W) := by
    simpa only [hback] using hKW
  refine ⟨W,hW,disjoint_union_left.mpr ⟨h.fuelU_avoid,hWX⟩,hRW,hKW',hWZ,hWd,?_⟩
  intro L hL hadm
  obtain ⟨hRL,hpart,hd,hpack,ht,hYZ,hYd⟩ := h.layer_partition hZ hX hL hadm
  have hWL : Disjoint W (R ∪ L) := hW.mono_right (by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_union_left _ he)
    · exact mem_union_left _ (mem_union_right _ (hL he)))
  obtain ⟨heq,hdisj⟩ := Envelope.extend_mode hpart hd hWL
  have hPB := Envelope.rooted_packing_basal (H := (⟨G,lab⟩ : Host V I)) (F := F)
    (packing X Z σ L) hpack (fun z hz => by
      obtain ⟨_,x,y,he,hxy,hT⟩ := ht z hz
      exact ⟨x,y,he,hT⟩)
  refine ⟨heq,hdisj,hPB,?_,?_,?_⟩
  · intro f hf v hv hvZ
    rcases mem_union.mp hf with hf | hf
    · exact hYZ f hf v hvZ hv
    · exact hWZ f hf v hv hvZ
  · intro v
    have h1 := edeg_union_le (residual X Z σ L) W v
    have h2 := hYd v
    have h3 := hWd v
    omega
  · intro hphys
    have hRWL : Disjoint (R ∪ W) L := disjoint_union_left.mpr
      ⟨hRL,hWL.mono_right subset_union_right⟩
    exact Envelope.mode_residue_physical hRW hphys hRWL hPB heq hdisj

lemma card_le_order_mul_degree (E : Finset (Sym2 V)) {r : ℕ}
    (hd : ∀ v, edeg E v ≤ r) : E.card ≤ Fintype.card V*r := by
  have hs : E ⊆ univ.biUnion (fun v : V => E.filter (fun e => v ∈ e)) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v => exact mem_biUnion.mpr ⟨u,mem_univ _,mem_filter.mpr ⟨he,by simp⟩⟩
  calc E.card ≤ (univ.biUnion (fun v : V => E.filter (fun e => v ∈ e))).card := card_le_card hs
    _ ≤ ∑ v : V, (E.filter (fun e => v ∈ e)).card := card_biUnion_le
    _ ≤ ∑ _v : V, r := sum_le_sum (fun v _ => hd v)
    _ = _ := by simp

/-- Construct the routed family and its common basal payment BEFORE every
later physical input. All roots are allowed; the windows do not contain |Z|. -/
theorem selector_paid_layer_host {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} (ht : Odd t) (ht3 : 3 ≤ t)
    {ε α : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : S07V27.RouteProp G lab F t ε W)
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
    (Z : Finset V) (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hZW : Disjoint Z W) (hXG : X ≤ G)
    (hH2 : IsPhysical (⟨G,lab⟩ : Host V I) F (edges (⟨G,lab⟩ : Host V I)))
    (hCore : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F α)
    {A q r b p : ℕ} (hA : 200*(t-1)+8 ≤ A) (hq : 0 < q) (hp : 0 < p)
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hBud : r+b+A*r*Fintype.card V/q+(A+1)*r+10*r+(t-1)*(200*r) ≤ ⌊ε*Fintype.card V⌋₊)
    (hρ : ((b+61*r+60*q+60:ℕ):ℝ) ≤ ε*Fintype.card V)
    (hPay : ((Fintype.card V*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z)) :
    ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)),
      Disjoint (fuelU Z σ ∪ C) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ C) ∧
      Basal (⟨G,lab⟩ : Host V I) F (residual X Z σ ∅ ∪ C) ∧
      (∀ v, edeg (fuelU Z σ ∪ C) v ≤ max (A*r) (60*r+61*q)+2*(61*r+60*q+p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical (⟨G,lab⟩ : Host V I) F L →
        (fuelU Z σ ∪ C) ∪ L = packEdges (packing X Z σ L) ∪ (residual X Z σ L ∪ C) ∧
        Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L ∪ C) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ residual X Z σ L ∪ C, ∀ v ∈ f, v ∉ Z) ∧
        (∀ v, edeg (residual X Z σ L ∪ C) v ≤ 3*(61*r+60*q)+2*p) ∧
        IsPhysical (⟨G,lab⟩ : Host V I) F (residual X Z σ L ∪ C) := by
  have hcov : S07V26.EdgeCovered G lab F := S07V26.H2Phys.edgeCovered hH2
  have hlink : ∀ v ∈ Z, ∀ u, X.Adj v u → ∃ y, (ComponentRows.link G lab F v).Adj u y :=
    fun v _ u hu => S07V27.link_of_edgeCovered hcov hXG hu
  have hAvail : ∀ v ∈ Z, S07V27.CoreAvail G lab F v (X.neighborFinset v)
      (S07V27.rootAdm G lab F X v) A (r+b+A*r*Fintype.card V/q) (b+61*r+60*q) W := by
    intro v hv
    exact S07V27.coreAvail_root ht ht3 hε hroute X v (hlink v hv) hA (hX v) hBud hρ
  obtain ⟨σ,hFam,hAux⟩ := S07V27.schedule_core G lab F X B0 Z W hZW
    (S07V27.rootAdm G lab F X) hAvail hq hX hB le_rfl le_rfl
  have hAdm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v ∅ :=
    fun v _ => S07V27.rootAdm_empty G lab F X v
  have hadm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  have hKd := (hFam.layer_partition hZ hX (empty_subset _) hadm0).2.2.2.2.2.2
  have hKcard := card_le_order_mul_degree (residual X Z σ ∅) hKd
  have hPay' : (((residual X Z σ ∅).card/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z) := by
    have hn := Nat.add_le_add_right (Nat.div_le_div_right (c := p) hKcard)
      (2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p))
    have hR : (((residual X Z σ ∅).card/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        ((Fintype.card V*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) := by exact_mod_cast hn
    exact hR.trans_lt hPay
  obtain ⟨C,hC,hAvoid,hBas,hEmp,hCZ,hCd,hModes⟩ := paid_core_family hFam hCore hp hZ hX hB hAdm0 hPay'
  refine ⟨σ,C,hAvoid,hBas,hEmp,?_,?_⟩
  · intro v
    exact (edeg_union_le _ _ v).trans
      (Nat.add_le_add (hFam.fuelU_edeg_le hZ hX v) (hCd v))
  · intro L hL hphys
    obtain ⟨heq,hd,hP,hYZ,hYd,hYP⟩ := hModes L hL
      (fun v _ => SelectorEntry.rootAdm_of_physical X hL hphys v)
    exact ⟨heq,hd,hP,hYZ,hYd,hYP hphys⟩

end TypedTriangle.CorePaid
