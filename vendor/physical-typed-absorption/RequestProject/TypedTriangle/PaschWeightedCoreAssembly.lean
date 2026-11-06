module
public import RequestProject.TypedTriangle.PaschWeightedCoreAvailability
public import RequestProject.TypedTriangle.PaschPartialRoutingCodegree
public import RequestProject.S07V27.CoreAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelBridge SelTyped SelSimul S07V27
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type*} [DecidableEq V] [DecidableEq Ambient]

theorem weightedPairCodegree_union {R S : Finset (Finset Ambient)} {L K : ℕ}
    (hR : PairCodegreeBound R L) (hS : PairCodegreeBound S K) :
    PairCodegreeBound (R ∪ S) (L+K) := by
  intro a b hab
  rw [filter_union]
  exact (card_union_le _ _).trans (Nat.add_le_add (hR a b hab) (hS a b hab))

theorem weightedCoreUniverse_biUnion {κ : Type*} (ι : V ↪ Ambient) (r : κ → V)
    (C : Finset κ) (τ : κ → LocalSel V) :
    C.biUnion (fun k => weightedCoreUniverse ι (r k) (τ k)) =
      mapConfiguration ι (C.biUnion (fun k => (τ k).P.image (selectorTriangle (r k)))) := by
  ext T
  simp only [mem_biUnion,weightedCoreUniverse,mem_mapConfiguration]
  constructor
  · rintro ⟨k,hk,S,hS,hEq⟩
    exact ⟨S,⟨k,hk,hS⟩,hEq⟩
  · rintro ⟨S,⟨k,hk,hS⟩,hEq⟩
    exact ⟨k,hk,S,hS,hEq⟩

theorem weightedCoreUniverse_same_root_biUnion {κ : Type*} (ι : V ↪ Ambient) (v : V)
    (C : Finset κ) (τ : κ → LocalSel V) :
    C.biUnion (fun k => weightedCoreUniverse ι v (τ k)) =
      mapConfiguration ι ((C.biUnion (fun k => (τ k).P)).image (selectorTriangle v)) := by
  rw [weightedCoreUniverse_biUnion ι (fun _ => v) C τ]
  apply congrArg (mapConfiguration ι)
  ext T
  simp only [mem_biUnion,mem_image]
  constructor
  · rintro ⟨k,hk,e,he,hEq⟩
    exact ⟨e,⟨k,hk,he⟩,hEq⟩
  · rintro ⟨e,⟨k,hk,he⟩,hEq⟩
    exact ⟨k,hk,e,he,hEq⟩

theorem weightedCoreUniverse_biUnion_update {κ : Type*} [DecidableEq κ]
    (ι : V ↪ Ambient) (r : κ → V) (C : Finset κ) (τ : κ → LocalSel V)
    (c : κ) (σc : LocalSel V) (hc : c ∉ C) :
    (insert c C).biUnion (fun k => weightedCoreUniverse ι (r k) (Function.update τ c σc k)) =
      weightedCoreUniverse ι (r c) σc ∪ C.biUnion (fun k => weightedCoreUniverse ι (r k) (τ k)) := by
  rw [biUnion_insert,Function.update_self]
  congr 1
  apply biUnion_congr rfl
  intro k hk
  rw [Function.update_of_ne (by rintro rfl; exact hc hk)]

/-- Component cells are genuinely disjoint, so their entire partial universe
has degree sixty, independently of the number of components. -/
theorem weightedCoreUniverse_components_pairCodegree {κ : Type*}
    (ι : V ↪ Ambient) (v : V) (C : Finset κ) (τ : κ → LocalSel V) (K : κ → Finset V)
    (hDeg : ∀ k ∈ C, ∀ y, edeg (τ k).P y ≤ 60)
    (hSupp : ∀ k ∈ C, ∀ e ∈ (τ k).P, ∀ y ∈ e, y ∈ K k)
    (hDis : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → Disjoint (K k) (K k')) :
    PairCodegreeBound (C.biUnion (fun k => weightedCoreUniverse ι v (τ k))) 60 := by
  rw [weightedCoreUniverse_same_root_biUnion]
  apply pairCodegreeBound_mapConfiguration
  apply rooted_edge_universe_pairCodegree v _ 60 (by decide)
  intro y
  have hh := edeg_biUnion_le C (fun k => (τ k).P) K hDeg hSupp y
  have hOne : (C.filter (fun k => y ∈ K k)).card ≤ 1 := by
    apply card_le_one.mpr
    intro k hk k' hk'
    by_contra hne
    exact disjoint_left.mp (hDis k (mem_filter.mp hk).1 k' (mem_filter.mp hk').1 hne)
      (mem_filter.mp hk).2 (mem_filter.mp hk').2
  omega

/-- **Assembly of the single-root contract over disjoint port parts.** -/
theorem weighted_coreAvail_biUnion {κ : Type*} [DecidableEq κ] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (v : V) (C : Finset κ) (U : κ → Finset V)
    (Adm : κ → Finset V → Prop) {A ζ ρ ζc ρc : ℕ}
    (hdisj : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → Disjoint (U k) (U k'))
    (Wc : Finset V) (ι : V ↪ Ambient) (pay : ℕ → ℝ) (hpay : ∀ L, 0 ≤ pay L)
    (hav : ∀ k ∈ C, WeightedCoreAvail G lab F v (U k) (Adm k) A ζc ρc Wc ι pay)
    (hζ : ζ + (A + 1) * (C.biUnion U).card ≤ ζc) (hρ : ρ + 60 ≤ ρc) :
    WeightedCoreAvail G lab F v (C.biUnion U) (fun S => ∀ k ∈ C, Adm k (S ∩ U k))
      A ζ ρ Wc ι (weightedCorePayShift pay 60) := by
  intro R0 L0 hCodeg Z0 Bf hZ0 hBf
  set CU := C.biUnion U with hCU
  have hUsub : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → U k' ⊆ CU \ U k := fun k hk k' hk' hne x hx =>
    mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨k', hk', hx⟩,
      fun h => Finset.disjoint_left.mp (hdisj k hk k' hk' hne) h hx⟩
  -- sequential placement over the parts
  have key : ∀ C' : Finset κ, C' ⊆ C → ∃ τ : κ → LocalSel V,
      (∀ k ∈ C', (τ k).Valid G lab F v (U k) (Adm k) (Z0 ∪ (CU \ U k)) Bf A) ∧
      (∀ k ∈ C', ∀ k' ∈ C', k ≠ k' → Disjoint (τ k).W (τ k').W) ∧
      (∀ k ∈ C', (τ k).W ⊆ Wc) ∧
      (count (R0 ∪ C'.biUnion (fun k => weightedCoreUniverse ι v (τ k))) : ℝ) ≤
        (count R0:ℝ) + ((∑ k ∈ C', (U k).card : ℕ):ℝ)*pay (L0+60) := by
    intro C'
    induction C' using Finset.induction_on with
    | empty => intro _; exact ⟨fun _ => ⟨∅, ∅, fun _ => ∅⟩, by simp, by simp, by simp, by simp⟩
    | insert c C' hc ih =>
      intro hsub
      have hcC : c ∈ C := hsub (mem_insert_self c C')
      have hC'C : C' ⊆ C := (subset_insert c C').trans hsub
      obtain ⟨τ, hval, hW, hWc, hCost⟩ := ih hC'C
      -- vertex sets of the placed parts are pairwise disjoint
      have hvd : ∀ k ∈ C', ∀ k' ∈ C', k ≠ k' →
          Disjoint (U k ∪ (τ k).W) (U k' ∪ (τ k').W) := by
        intro k hk k' hk' hne
        rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
        refine ⟨⟨hdisj k (hC'C hk) k' (hC'C hk') hne, ?_⟩, ?_, hW k hk k' hk' hne⟩
        · exact ((hval k' hk').avoidZ.mono_right
            ((hUsub k' (hC'C hk') k (hC'C hk) (Ne.symm hne)).trans subset_union_right)).symm
        · exact (hval k hk).avoidZ.mono_right
            ((hUsub k (hC'C hk) k' (hC'C hk') hne).trans subset_union_right)
      set Z0' := Z0 ∪ (CU \ U c) ∪ C'.biUnion (fun k => (τ k).W) with hZ0'
      set Bf' := Bf ∪ C'.biUnion (fun k => (τ k).P) with hBf'
      have hcardU : ∑ k ∈ C', (U k).card ≤ CU.card := by
        rw [← card_biUnion (fun k hk k' hk' hne => hdisj k (hC'C hk) k' (hC'C hk') hne)]
        exact card_le_card (biUnion_subset_biUnion_of_subset_left _ hC'C)
      have hZc : Z0'.card ≤ ζc := by
        rw [hZ0']
        have h1 := card_union_le (Z0 ∪ (CU \ U c)) (C'.biUnion (fun k => (τ k).W))
        have h2 := card_union_le Z0 (CU \ U c)
        have h3 : (CU \ U c).card ≤ CU.card := card_le_card sdiff_subset
        have h4 : (C'.biUnion (fun k => (τ k).W)).card ≤ A * CU.card := by
          refine card_biUnion_le.trans ?_
          calc ∑ k ∈ C', ((τ k).W).card ≤ ∑ k ∈ C', A * (U k).card :=
                sum_le_sum fun k hk => (hval k hk).card_le
            _ = A * ∑ k ∈ C', (U k).card := by rw [mul_sum]
            _ ≤ A * CU.card := Nat.mul_le_mul_left _ hcardU
        have h5 : (A + 1) * CU.card = A * CU.card + CU.card := by ring
        omega
      have hBc : ∀ y, edeg Bf' y ≤ ρc := by
        intro y
        rw [hBf']
        have h1 := edeg_union_le Bf (C'.biUnion (fun k => (τ k).P)) y
        have h2 := edeg_biUnion_le C' (fun k => (τ k).P) (fun k => U k ∪ (τ k).W)
          (fun k hk => (hval k hk).deg_le)
          (fun k hk f hf y hy => mem_union.mpr ((hval k hk).supp f hf y hy)) y
        have h3 : (C'.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 1 := by
          rw [card_le_one]
          intro k hk k' hk'
          by_contra hne
          rw [mem_filter] at hk hk'
          exact Finset.disjoint_left.mp (hvd k hk.1 k' hk'.1 hne) hk.2 hk'.2
        have := hBf y
        have : 60 * (C'.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 60 := by omega
        omega
      have hPartial : PairCodegreeBound (C'.biUnion (fun k => weightedCoreUniverse ι v (τ k))) 60 :=
        weightedCoreUniverse_components_pairCodegree ι v C' τ (fun k => U k ∪ (τ k).W)
          (fun k hk => (hval k hk).deg_le)
          (fun k hk f hf y hy => mem_union.mpr ((hval k hk).supp f hf y hy)) hvd
      have hPrevious := weightedPairCodegree_union hCodeg hPartial
      obtain ⟨σc, hσc, hσcW, hσcCost⟩ := hav c hcC
        (R0 ∪ C'.biUnion (fun k => weightedCoreUniverse ι v (τ k))) (L0+60) hPrevious
        Z0' Bf' hZc hBc
      have hupd : ∀ k ∈ C', Function.update τ c σc k = τ k := fun k hk =>
        Function.update_of_ne (by rintro rfl; exact hc hk) _ _
      refine ⟨Function.update τ c σc, ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · rw [Function.update_self]
          exact hσc.mono (fun x hx => by rw [hZ0']; exact mem_union_left _ hx)
            (fun f hf => by rw [hBf']; exact mem_union_left _ hf)
        · rw [hupd k hk]; exact hval k hk
      · have hWc : ∀ k ∈ C', Disjoint σc.W (τ k).W := fun k hk =>
          hσc.avoidZ.mono_right (fun x hx => by
            rw [hZ0']; exact mem_union_right _ (mem_biUnion.mpr ⟨k, hk, hx⟩))
        intro k hk k' hk' hne
        rcases mem_insert.mp hk with hkc | hk <;> rcases mem_insert.mp hk' with hkc' | hk'
        · exact absurd (hkc.trans hkc'.symm) hne
        · rw [hkc, Function.update_self, hupd k' hk']; exact hWc k' hk'
        · rw [hkc', Function.update_self, hupd k hk]; exact (hWc k hk).symm
        · rw [hupd k hk, hupd k' hk']; exact hW k hk k' hk' hne
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · rw [Function.update_self]; exact hσcW
        · rw [hupd k hk]; exact hWc k hk
      · rw [weightedCoreUniverse_biUnion_update ι (fun _ => v) C' τ c σc hc]
        have hSets : R0 ∪ (weightedCoreUniverse ι v σc ∪
            C'.biUnion (fun k => weightedCoreUniverse ι v (τ k))) =
            (R0 ∪ C'.biUnion (fun k => weightedCoreUniverse ι v (τ k))) ∪
              weightedCoreUniverse ι v σc := by ext T; simp only [mem_union]; tauto
        rw [hSets, sum_insert hc, Nat.cast_add]
        linarith only [hCost,hσcCost]
  obtain ⟨τ, hval, hW, hWc, hCost⟩ := key C (subset_refl _)
  -- the cells `U k ∪ W k` are pairwise disjoint
  have hvd : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → Disjoint (U k ∪ (τ k).W) (U k' ∪ (τ k').W) := by
    intro k hk k' hk' hne
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hdisj k hk k' hk' hne, ?_⟩, ?_, hW k hk k' hk' hne⟩
    · exact ((hval k' hk').avoidZ.mono_right
        ((hUsub k' hk' k hk (Ne.symm hne)).trans subset_union_right)).symm
    · exact (hval k hk).avoidZ.mono_right ((hUsub k hk k' hk' hne).trans subset_union_right)
  have hone : ∀ y, (C.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 1 := by
    intro y
    rw [card_le_one]
    intro k hk k' hk'
    by_contra hne
    rw [mem_filter] at hk hk'
    exact Finset.disjoint_left.mp (hvd k hk.1 k' hk'.1 hne) hk.2 hk'.2
  have hcell : ∀ k ∈ C, ∀ k' ∈ C, ∀ y, y ∈ U k ∪ (τ k).W → y ∈ U k' ∪ (τ k').W → k = k' := by
    intro k hk k' hk' y h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hvd k hk k' hk' hne) h1 h2
  refine ⟨⟨C.biUnion (fun k => (τ k).W), C.biUnion (fun k => (τ k).P),
    fun S => C.biUnion (fun k => (τ k).mode (S ∩ U k))⟩, ?_, ?_, ?_⟩
  refine
    { typed := ?_
      avoidB := ?_
      supp := ?_
      wing := ?_
      avoidZ := ?_
      portFree := ?_
      card_le := ?_
      deg_le := ?_
      modes := ?_ }
  · intro f hf
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    exact (hval k hk).typed f hf
  · rw [Finset.disjoint_left]
    intro f hf hfB
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hval k hk).avoidB hf hfB
  · intro f hf y hy
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    rcases (hval k hk).supp f hf y hy with h | h
    · exact Or.inl (mem_biUnion.mpr ⟨k, hk, h⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨k, hk, h⟩)
  · intro w hw
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact (hval k hk).wing w hw
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact Finset.disjoint_left.mp (hval k hk).avoidZ hw (mem_union_left _ hwZ)
  · rw [Finset.disjoint_left]
    intro w hw hwU
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    obtain ⟨k', hk', hwU⟩ := mem_biUnion.mp hwU
    exact absurd (hcell k hk k' hk' w (mem_union_right _ hw) (mem_union_left _ hwU) ▸ hwU)
      (Finset.disjoint_left.mp (hval k hk).portFree hw)
  · refine card_biUnion_le.trans ?_
    calc ∑ k ∈ C, ((τ k).W).card ≤ ∑ k ∈ C, A * (U k).card :=
          sum_le_sum fun k hk => (hval k hk).card_le
      _ = A * ∑ k ∈ C, (U k).card := by rw [mul_sum]
      _ = A * CU.card := by rw [hCU, card_biUnion hdisj]
  · intro y
    refine (edeg_biUnion_le C (fun k => (τ k).P) (fun k => U k ∪ (τ k).W)
      (fun k hk => (hval k hk).deg_le)
      (fun k hk f hf y hy => mem_union.mpr ((hval k hk).supp f hf y hy)) y).trans ?_
    have := hone y
    omega
  · intro S hS hadm
    have hM : ∀ k ∈ C, IsMode (τ k).P (τ k).W (S ∩ U k) ((τ k).mode (S ∩ U k)) :=
      fun k hk => (hval k hk).modes _ inter_subset_right (hadm k hk)
    -- every covered vertex of the mode of `k` lies in the cell of `k`
    have hvert : ∀ k ∈ C, ∀ f ∈ (τ k).mode (S ∩ U k), ∀ y ∈ f, y ∈ U k ∪ (τ k).W := by
      intro k hk f hf y hy
      rcases mem_union.mp (mode_vert' (hM k hk) hf hy) with h | h
      · exact mem_union_right _ h
      · exact mem_union_left _ (mem_inter.mp h).2
    refine ⟨?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
      exact mem_biUnion.mpr ⟨k, hk, (hM k hk).1 hf⟩
    · intro x hx
      -- the cell of `x`
      obtain ⟨k, hk, hxk⟩ : ∃ k ∈ C, x ∈ (τ k).W ∪ (S ∩ U k) := by
        rcases mem_union.mp hx with hx | hx
        · obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
          exact ⟨k, hk, mem_union_left _ hx⟩
        · obtain ⟨k, hk, hxU⟩ := mem_biUnion.mp (hS hx)
          exact ⟨k, hk, mem_union_right _ (mem_inter.mpr ⟨hx, hxU⟩)⟩
      have hxcell : x ∈ U k ∪ (τ k).W := by
        rcases mem_union.mp hxk with h | h
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_inter.mp h).2
      have heq : (C.biUnion (fun k => (τ k).mode (S ∩ U k))).filter (fun e => x ∈ e) =
          ((τ k).mode (S ∩ U k)).filter (fun e => x ∈ e) := by
        ext f
        simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨⟨k', hk', hf⟩, hxf⟩
          have := hcell k hk k' hk' x hxcell (hvert k' hk' f hf x hxf)
          subst this
          exact ⟨hf, hxf⟩
        · rintro ⟨hf, hxf⟩
          exact ⟨⟨k, hk, hf⟩, hxf⟩
      rw [heq]
      exact (hM k hk).2.1 x hxk
    · intro x hx f hf hxf
      obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
      have := mode_vert' (hM k hk) hf hxf
      apply hx
      rcases mem_union.mp this with h | h
      · exact mem_union_left _ (mem_biUnion.mpr ⟨k, hk, h⟩)
      · exact mem_union_right _ (mem_inter.mp h).1
  · intro w hw
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact hWc k hk hw

  · change (count (R0 ∪ mapConfiguration ι ((C.biUnion (fun k => (τ k).P)).image
        (selectorTriangle v))) : ℝ) ≤ (count R0:ℝ) + (CU.card:ℝ)*pay (L0+60)
    rw [←weightedCoreUniverse_same_root_biUnion ι v C τ]
    have hCard : (∑ k ∈ C, (U k).card) = CU.card := by rw [hCU,card_biUnion hdisj]
    simpa only [hCard] using hCost

#print axioms weighted_coreAvail_biUnion
end TypedTriangle.Pasch
