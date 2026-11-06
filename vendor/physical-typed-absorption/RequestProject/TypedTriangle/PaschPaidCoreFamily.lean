module
public import RequestProject.TypedTriangle.PaschAmbientCorePayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open CorePayment PreparedSupply SelSimul SelBridge SelTyped CorePaid
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

theorem paid_core_family_with_ambient_pasch
    (ι : V ↪ Ambient) (Rfixed : Finset (Finset Ambient)) (L0 : ℕ)
    (hL0 : PairCodegreeBound Rfixed L0) {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj]
    {Z : Finset V} {Adm : V → Finset V → Prop} {A q : ℕ} {σ : V → LocalSel V}
    (h : SimulFamily G lab F X B0 Z Adm A q σ) {α : ℝ}
    (hfixed : mapConfiguration ι (selectorUniverse Z σ) ⊆ Rfixed)
    (hα : 0 < α)
    (hH3 : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F α)
    {r b p : ℕ} (hp : 0 < p)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    (hwin : ((SelSimul.residual X Z σ ∅).card : ℝ)/(p : ℝ) +
      2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) ≤
        (α/2)*Fintype.card (Survivors Z)) :
    ∃ (W : Finset (Sym2 V)) (DPaid : Finset (Finset V)),
      IsDecomposition (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ W) DPaid ∧
      (count (Rfixed∪mapConfiguration ι DPaid) : ℝ) ≤ count Rfixed+
        2*((pullEdges Z (SelSimul.residual X Z σ ∅)).card : ℝ)*
          ((Fintype.card Ambient : ℝ)/Fintype.card (Survivors Z))*
          ((L0+1 : ℕ) : ℝ)^3/α ∧
      Disjoint W (fuelU Z σ ∪ X.edgeFinset ∪ B0.edgeFinset) ∧
      Disjoint (fuelU Z σ ∪ W) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ W) ∧
      Basal (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ ∅ ∪ W) ∧
      (∀ f ∈ W, ∀ v ∈ f, v ∉ Z) ∧
      (∀ v, edeg W v ≤ 2*(61*r+60*q+p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset →
        (∀ v ∈ Z, Adm v (demand X L v)) →
        (fuelU Z σ ∪ W) ∪ L = packEdges (packing X Z σ L) ∪ (SelSimul.residual X Z σ L ∪ W) ∧
        Disjoint (packEdges (packing X Z σ L)) (SelSimul.residual X Z σ L ∪ W) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ SelSimul.residual X Z σ L ∪ W, ∀ v ∈ f, v ∉ Z) ∧
        (∀ v, edeg (SelSimul.residual X Z σ L ∪ W) v ≤ 3*(61*r+60*q)+2*p) ∧
        (IsPhysical (⟨G,lab⟩ : Host V I) F L →
          IsPhysical (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ L ∪ W)) := by
  let R := fuelU Z σ
  let K := SelSimul.residual X Z σ ∅
  have hadm0 : ∀ v ∈ Z, Adm v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  obtain ⟨_,hpart0,hd0,hpack0,ht0,hKZ,hKd⟩ := h.layer_partition hZ hX (empty_subset _) hadm0
  simp only [union_empty] at hpart0
  have hKsub : K ⊆ R := by
    change SelSimul.residual X Z σ ∅ ⊆ fuelU Z σ
    rw [hpart0]; exact subset_union_right
  let DR := (packing X Z σ ∅).image (fun p => selectorTriangle p.1 p.2)
  have hDR0 := rooted_packing_decomposition
    (H := (⟨G,lab⟩ : Host V I)) (F := F)
    (packing X Z σ ∅) hpack0 (fun z hz => by
      obtain ⟨_,x,y,he,hxy,hT⟩ := ht0 z hz
      exact ⟨x,y,he,hT⟩)
  have hDR : IsDecomposition (⟨G,lab⟩ : Host V I) F (R \ K) DR := by
    have hEq : packEdges (packing X Z σ ∅)=R\K := by
      change packEdges (packing X Z σ ∅)=fuelU Z σ\SelSimul.residual X Z σ ∅
      rw [hpart0]
      ext e
      have hd : e∈packEdges (packing X Z σ ∅) → e∉K := fun he => disjoint_left.mp hd0 he
      simp only [mem_sdiff,mem_union]
      tauto
    rw [←hEq]
    exact hDR0
  have hDRfixed : mapConfiguration ι DR ⊆ Rfixed := by
    apply Subset.trans _ hfixed
    intro T hT
    obtain ⟨S,hS,rfl⟩ := mem_mapConfiguration.mp hT
    exact mem_mapConfiguration.mpr ⟨S,selector_modes_subset_universe h ∅ hadm0 hS,rfl⟩
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
  have hLeft : (0 : ℝ) < (K.card : ℝ)/(p : ℝ)+
      2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) := by
    positivity
  have hpos : 0 < α*Fintype.card (Survivors Z) := by
    have hh := hwin
    change (K.card : ℝ)/(p : ℝ)+_ ≤ _ at hh
    nlinarith only [hh,hLeft]
  have hnCore : 0 < Fintype.card (Survivors Z) := by
    by_contra hn
    have he : Fintype.card (Survivors Z)=0 := by omega
    simp only [he,Nat.cast_zero,mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have htri : ∀ e ∈ pullEdges Z K, HasTri (restrictedHost (⟨G,lab⟩ : Host V I) Z) F e := by
    intro e he
    exact hasTri_pull_of_core_H3 Z hH3 hpos
      (Envelope.empty_residual_hasTri h (mem_preimage.mp he))
  have hEdeg : ∀ v, edeg (pullEdges Z K) v ≤ 61*r+60*q := by
    intro v
    simpa only [edeg_eq_classical] using (degree_pull_le Z K v).trans (hKd v.1)
  have hEcard : (pullEdges Z K).card ≤ K.card := by
    rw [pullEdges,card_preimage]; exact card_filter_le _ _
  have hwinE : ((pullEdges Z K).card : ℝ)/(p : ℝ)+
      2*((max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p : ℕ) : ℝ) ≤
        (α/2)*Fintype.card (Survivors Z) := by
    have hc : ((pullEdges Z K).card : ℝ) ≤ K.card := Nat.cast_le.mpr hEcard
    have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hdiv := div_le_div_of_nonneg_right hc hpR
    linarith only [hdiv,hwin]
  obtain ⟨W,DC,hW,hWZ,hKC,hRC,hWd,hStat⟩ :=
    basal_payment_inside_core_with_ambient_pasch ι hα Z hH3 (pullEdges Z K)
      R X.edgeFinset B0.edgeFinset DR
      (by simpa only [hback] using hDR) hp hnCore
      (by simpa only [hback] using hKsub) hEdeg hProt htri hwinE Rfixed L0 hL0
  have hRW : Basal (⟨G,lab⟩ : Host V I) F (R∪W) := ⟨DR∪DC,hRC⟩
  have hKW : Basal (⟨G,lab⟩ : Host V I) F (liftEdges Z (pullEdges Z K)∪W) := ⟨DC,hKC⟩
  have hFixedEq : Rfixed∪mapConfiguration ι (DR∪DC)=Rfixed∪mapConfiguration ι DC := by
    unfold mapConfiguration
    rw [map_union]
    ext T
    have hh : T∈mapConfiguration ι DR → T∈Rfixed := fun hT => hDRfixed hT
    simp only [mem_union]
    change (T∈Rfixed ∨ T∈mapConfiguration ι DR ∨ T∈mapConfiguration ι DC) ↔ _
    tauto
  have hPaidStat : (count (Rfixed∪mapConfiguration ι (DR∪DC)) : ℝ) ≤ count Rfixed+
      2*((pullEdges Z K).card : ℝ)*
        ((Fintype.card Ambient : ℝ)/Fintype.card (Survivors Z))*
        ((L0+1 : ℕ) : ℝ)^3/α := by
    rw [hFixedEq]
    exact hStat
  have hWX : Disjoint W (X.edgeFinset ∪ B0.edgeFinset) := hW.mono_right (by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_union_right _ he)
    · exact mem_union_right _ he)
  have hKW' : Basal (⟨G,lab⟩ : Host V I) F (K ∪ W) := by
    simpa only [hback] using hKW
  refine ⟨W,DR∪DC,hRC,hPaidStat,hW,disjoint_union_left.mpr ⟨h.fuelU_avoid,hWX⟩,hRW,hKW',hWZ,hWd,?_⟩
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
    have h1 := edeg_union_le (SelSimul.residual X Z σ L) W v
    have h2 := hYd v
    have h3 := hWd v
    omega
  · intro hphys
    have hRWL : Disjoint (R ∪ W) L := disjoint_union_left.mpr
      ⟨hRL,hWL.mono_right subset_union_right⟩
    exact Envelope.mode_residue_physical hRW hphys hRWL hPB heq hdisj

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.paid_core_family_with_ambient_pasch
