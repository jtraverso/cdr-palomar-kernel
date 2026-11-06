module
public import RequestProject.TypedTriangle.PaschWeightedCoreAssembly
public import RequestProject.S07V27.CoreSchedule
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
variable {V I Ambient : Type*} [DecidableEq V] [DecidableEq Ambient] [Fintype V]

/-- One actual scheduled selector universe pays against the intact ambient
family. The partial root universe has codegree sixty regardless of root
count, so the payment argument is shifted once, never once per root. -/
theorem weighted_schedule_core (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z Wc : Finset V)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') (hZW : Disjoint Z Wc)
    (Adm : V → Finset V → Prop) (ι : V ↪ Ambient) (pay : ℕ → ℝ)
    (hpay : ∀ L, 0 ≤ pay L) {A q r b ζw ρw : ℕ}
    (hAvail : ∀ v ∈ Z, WeightedCoreAvail G lab F v (X.neighborFinset v) (Adm v)
      A ζw ρw Wc ι pay)
    (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r) (hB : ∀ x, B0.degree x ≤ b)
    (hζ : r + b + A * r * Fintype.card V / q ≤ ζw) (hρ : b + 61 * r + 60 * q ≤ ρw) :
    ∀ (R0 : Finset (Finset Ambient)) (L0 : ℕ), PairCodegreeBound R0 L0 →
    ∃ σ : V → LocalSel V, SimulFamily G lab F X B0 Z Adm A q σ ∧
      (∀ v ∈ Z, (σ v).W ⊆ Wc) ∧
      (count (R0 ∪ mapConfiguration ι (selectorUniverse Z σ)) : ℝ) ≤
        (count R0:ℝ) + ((r*Z.card:ℕ):ℝ)*pay (L0+60) := by
  intro R0 L0 hCodeg
  have key : ∀ Z' : Finset V, Z' ⊆ Z → ∃ σ : V → LocalSel V,
      (∀ v ∈ Z', (σ v).Valid G lab F v (X.neighborFinset v) (Adm v)
        (Z ∪ X.neighborFinset v ∪ B0.neighborFinset v) (X.edgeFinset ∪ B0.edgeFinset) A) ∧
      (∀ v ∈ Z', ∀ v' ∈ Z', v ≠ v' → Disjoint (σ v).P (σ v').P) ∧
      (∀ x, auxCount Z' (fun v => (σ v).W) x ≤ q) ∧ (∀ v ∈ Z', (σ v).W ⊆ Wc) ∧
      (count (R0 ∪ Z'.biUnion (fun v => weightedCoreUniverse ι v (σ v))) : ℝ) ≤
        (count R0:ℝ) + ((∑ v ∈ Z', (X.neighborFinset v).card : ℕ):ℝ)*pay (L0+60) := by
    intro Z'
    induction Z' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ⟨∅, ∅, fun _ => ∅⟩, by simp, by simp, fun x => by simp [auxCount],
        by simp, by simp⟩
    | insert a Z' ha ih =>
      intro hsub
      have haZ : a ∈ Z := hsub (mem_insert_self a Z')
      have hZsub : Z' ⊆ Z := (subset_insert a Z').trans hsub
      obtain ⟨σ, hval, hdisj, hcnt, hsubW, hCost⟩ := ih ((subset_insert a Z').trans hsub)
      set Wf : V → Finset V := fun v => (σ v).W with hWf
      -- per-root auxiliary bound `A·r`
      have hWcard : ∀ v ∈ Z', (Wf v).card ≤ A * r := by
        intro v hv
        refine ((hval v hv).card_le).trans (Nat.mul_le_mul_left _ ?_)
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX v
      -- the saturated set
      set Sat := satSet Z' Wf q with hSat
      have hSatc : Sat.card ≤ A * r * Fintype.card V / q := by
        refine (satSet_card_le Z' Wf hq hWcard).trans (Nat.div_le_div_right ?_)
        exact Nat.mul_le_mul_left _ (card_le_univ _)
      -- the deleted vertex window
      set Z0 := X.neighborFinset a ∪ B0.neighborFinset a ∪ Sat with hZ0
      have hZ0c : Z0.card ≤ ζw := by
        rw [hZ0]
        have h1 := card_union_le (X.neighborFinset a ∪ B0.neighborFinset a) Sat
        have h2 := card_union_le (X.neighborFinset a) (B0.neighborFinset a)
        have h4 : (X.neighborFinset a).card ≤ r := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX a
        have h5 : (B0.neighborFinset a).card ≤ b := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hB a
        omega
      -- the forbidden edge window
      set Bf := X.edgeFinset ∪ B0.edgeFinset ∪ Z'.biUnion (fun v => (σ v).P) with hBf
      have hBfd : ∀ y, edeg Bf y ≤ ρw := by
        intro y
        rw [hBf]
        have h1 := edeg_union_le (X.edgeFinset ∪ B0.edgeFinset) (Z'.biUnion (fun v => (σ v).P)) y
        have h2 := edeg_union_le X.edgeFinset B0.edgeFinset y
        rw [edeg_edgeFinset] at h2
        rw [edeg_edgeFinset] at h2
        have h3 := edeg_biUnion_le Z' (fun v => (σ v).P) (fun v => X.neighborFinset v ∪ (σ v).W)
          (fun v hv => (hval v hv).deg_le)
          (fun v hv f hf y hy => mem_union.mpr ((hval v hv).supp f hf y hy)) y
        have h4 := filter_or_card_le Z' (fun v => y ∈ X.neighborFinset v) (fun v => y ∈ (σ v).W)
        have h5 := portCount_le X Z' y
        have h6 : (Z'.filter (fun v => y ∈ (σ v).W)).card ≤ q := hcnt y
        have h7 := hX y
        have h8 := hB y
        simp only [mem_union] at h3
        have h9 : 60 * (Z'.filter (fun v => y ∈ X.neighborFinset v ∨ y ∈ (σ v).W)).card ≤
            60 * (r + q) := Nat.mul_le_mul_left _ (by omega)
        omega
      -- the local selector of the current root
      have hPartialFamily : SimulFamily G lab F X B0 Z' Adm A q σ := by
        refine ⟨?_,hdisj,hcnt⟩
        intro v hv
        apply (hval v hv).mono
        · intro x hx
          simp only [mem_union] at hx ⊢
          rcases hx with (hx | hx) | hx
          · exact Or.inl (Or.inl (hZsub hx))
          · exact Or.inl (Or.inr hx)
          · exact Or.inr hx
        · exact subset_refl _
      have hPartialLocal : PairCodegreeBound (selectorUniverse Z' σ) 60 := by
        intro u v huv
        exact selectorUniverse_pair_degree_le hPartialFamily
          (fun v hv v' hv' => hZ v (hZsub hv) v' (hZsub hv')) u v huv
      have hPartial : PairCodegreeBound
          (Z'.biUnion (fun v => weightedCoreUniverse ι v (σ v))) 60 := by
        rw [weightedCoreUniverse_biUnion ι (fun v : V => v) Z' σ]
        exact pairCodegreeBound_mapConfiguration ι (selectorUniverse Z' σ) 60 hPartialLocal
      have hPrevious := weightedPairCodegree_union hCodeg hPartial
      obtain ⟨σa, hσa, hσaW, hσaCost⟩ := hAvail a haZ
        (R0 ∪ Z'.biUnion (fun v => weightedCoreUniverse ι v (σ v))) (L0+60) hPrevious
        Z0 Bf hZ0c hBfd
      have hσaZ : Disjoint σa.W Z := (hZW.symm.mono_left hσaW)
      refine ⟨Function.update σ a σa, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · rw [Function.update_self]
          have hval' := (hσa.extendZ hσaZ).mono (Z0' := Z ∪ X.neighborFinset v ∪
              B0.neighborFinset v) (Bf' := X.edgeFinset ∪ B0.edgeFinset)
            (fun x hx => by
              rw [hZ0]
              simp only [mem_union] at hx ⊢
              tauto)
            (fun f hf => by rw [hBf]; exact mem_union_left _ hf)
          exact hval'
        · have hva : v ≠ a := fun h => ha (h ▸ hv)
          rw [Function.update_of_ne hva]
          exact hval v hv
      · intro v hv v' hv' hne
        have hPa : ∀ w ∈ Z', Disjoint σa.P (σ w).P := fun w hw =>
          hσa.avoidB.mono_right (fun f hf => by
            rw [hBf]; exact mem_union_right _ (mem_biUnion.mpr ⟨w, hw, hf⟩))
        have hupd : ∀ w ∈ Z', Function.update σ a σa w = σ w := fun w hw =>
          Function.update_of_ne (by rintro rfl; exact ha hw) _ _
        rcases mem_insert.mp hv with hva | hvZ <;> rcases mem_insert.mp hv' with hva' | hvZ'
        · exact absurd (hva.trans hva'.symm) hne
        · rw [hva, Function.update_self, hupd v' hvZ']; exact hPa v' hvZ'
        · rw [hva', Function.update_self, hupd v hvZ]; exact (hPa v hvZ).symm
        · rw [hupd v hvZ, hupd v' hvZ']; exact hdisj v hvZ v' hvZ' hne
      · have hcong : ∀ v ∈ Z', (fun v => (Function.update σ a σa v).W) v = Wf v := by
          intro v hv
          simp only [hWf]
          rw [Function.update_of_ne (by rintro rfl; exact ha hv)]
        intro x
        refine auxCount_insert_le ha _ hq (fun y => ?_) ?_ x
        · rw [auxCount_congr hcong]; exact hcnt y
        · rw [satSet_congr hcong, Function.update_self]
          exact hσa.avoidZ.mono_right (fun y hy => by rw [hZ0]; exact mem_union_right _ hy)
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv'
        · rw [Function.update_self]; exact hσaW
        · have hva : v ≠ a := fun h => ha (h ▸ hv')
          rw [Function.update_of_ne hva]; exact hsubW v hv'
      · rw [weightedCoreUniverse_biUnion_update ι (fun v : V => v) Z' σ a σa ha]
        have hSets : R0 ∪ (weightedCoreUniverse ι a σa ∪
            Z'.biUnion (fun v => weightedCoreUniverse ι v (σ v))) =
            (R0 ∪ Z'.biUnion (fun v => weightedCoreUniverse ι v (σ v))) ∪
              weightedCoreUniverse ι a σa := by ext T; simp only [mem_union]; tauto
        rw [hSets,sum_insert ha,Nat.cast_add]
        linarith only [hCost,hσaCost]
  obtain ⟨σ, h1, h2, h3, h4, hCost⟩ := key Z (subset_refl _)
  refine ⟨σ,⟨h1,h2,h3⟩,h4,?_⟩
  have hUniverse : mapConfiguration ι (selectorUniverse Z σ) =
      Z.biUnion (fun v => weightedCoreUniverse ι v (σ v)) :=
    (weightedCoreUniverse_biUnion ι (fun v : V => v) Z σ).symm
  rw [hUniverse]
  have hPorts : (∑ v ∈ Z, (X.neighborFinset v).card) ≤ r*Z.card := by
    calc
      _ ≤ ∑ _v ∈ Z, r := sum_le_sum (fun v _ => by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX v)
      _ = r*Z.card := by simp [Nat.mul_comm]
  have hScale : (((∑ v ∈ Z, (X.neighborFinset v).card : ℕ):ℝ))*pay (L0+60) ≤
      ((r*Z.card:ℕ):ℝ)*pay (L0+60) := mul_le_mul_of_nonneg_right
        (show (((∑ v ∈ Z, (X.neighborFinset v).card : ℕ):ℝ)) ≤ ((r*Z.card:ℕ):ℝ) by
          exact_mod_cast hPorts) (hpay (L0+60))
  exact hCost.trans (add_le_add (le_refl _) hScale)

#print axioms weighted_schedule_core
end TypedTriangle.Pasch
