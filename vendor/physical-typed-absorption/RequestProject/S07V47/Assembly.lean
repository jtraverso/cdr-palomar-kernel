/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Shape
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V47 §3 — exact cover/payload assembly for ANY setting of child shape

`shape_assembly` : let `S` have `ChildShape C0 R S` (so possibly the PROTECTED setting) and let
`MacroBank S L N` hold.  Given an occurrence-indexed word `z i p v` that is
* active where selected (`z i p v ≠ 0 → i ≤ J ∧ gCat v ∈ K_{Zstrat i}`),
* within the per-(stratum, entry, sign, colour) capacity (`|z i p v| ≤ m_i`), and
* cancels the charge (`[x] + ∑_{i ≤ J} ∑_p [z i p] = 0`),

the stratum banks of `run S N` supply it and all conclusions of V46 hold for `S`
(`ShapeOutcome`): physical activation stratum by stratum, payloads avoiding `Zstrat i` and inside
the child, disjoint strata, exact intrinsic cancellation `[x] + [1_Y] = 0` (torsion included),
`x + 1_Y ∈ Λ(H[W])`, the exact partition `⋃ total = ⋃ cover ⊔ Y`, and `|Y| ≤ E · ∑|z|`.
In addition the union of the banks AND the union of the covers satisfy the basal predicate OF `S`
(for the protected setting: decomposable in `H` and disjoint from `F0`).
-/

open Finset Classical Submodule

noncomputable section

namespace S07V47

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- **the properties of a selected occurrence word `z` (supplied by `hs`) in a child-shaped
setting** -/
def ShapeProps (C0 : CoreCompression H lab F W d c E) (R : ℕ)
    (S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)) (N J : ℕ) (x : MCore H lab F W)
    (z : ℕ → Fin S.P → Cat d R → ℤ) (hs : ∀ i, (stratBank S N i).Supplies (z i)) : Prop :=
    (∀ i p v, z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Zstrat S N i)) ∧
    (∀ i p v, (z i p v).natAbs ≤ mStrat S N i) ∧
    (∀ i, PhysicalActivation H lab F W (stratBank S N i) (gCat C0 R) (z i) (hs i) S.E) ∧
    (∀ i, Avoids (Zstrat S N i) (Bank.payload (hs i))) ∧
    (∀ i j, i ≠ j → Disjoint (stratBank S N i).total (stratBank S N j).total) ∧
    clsQ H lab F W (x : Sym2 V → ℤ) +
      chargeQ H lab F W ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) = 0 ∧
    (x : Sym2 V → ℤ) + ind ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∈
      LamCore H lab F W ∧
    ((range (J + 1)).biUnion fun i => (stratBank S N i).total) =
      ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∪
        ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
    Disjoint ((range (J + 1)).biUnion fun i => Bank.cover (hs i))
      ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
    S.basal ((range (J + 1)).biUnion fun i => (stratBank S N i).total) ∧
    S.basal ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∧
    physBasal H lab F ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∧
    ((range (J + 1)).biUnion fun i => Bank.payload (hs i)).card ≤
      S.E * ∑ i ∈ range (J + 1), ∑ p, ∑ v, (z i p v).natAbs

/-- **the allocation outcome for a setting of child shape** -/
def ShapeOutcome (C0 : CoreCompression H lab F W d c E) (R : ℕ)
    (S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)) (N J : ℕ) (x : MCore H lab F W) : Prop :=
  ∃ (z : ℕ → Fin S.P → Cat d R → ℤ) (hs : ∀ i, (stratBank S N i).Supplies (z i)),
    ShapeProps C0 R S N J x z hs

section

variable {C0 : CoreCompression H lab F W d c E} {R : ℕ}
  {S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)} {L N : ℕ}

/-- every stratum bank of a child-shaped setting is valid for the PHYSICAL data, payloads in the
child (V43 `child_stratBank_valid`, for any child shape) -/
theorem shape_stratBank_valid (hS : ChildShape C0 R S) (hM : MacroBank S L N) (j : ℕ) :
    (stratBank S N j).Valid (physBasal H lab F) (wQ H lab F W) (gCat C0 R) ∧
      ∀ k, (stratBank S N j).Y k ⊆ childEdges H W := by
  have hv := stratBank_valid (j := j) hM
  have hch : ∀ k, chargeQ H lab F W ((stratBank S N j).Y k) =
      sgnQ ((stratBank S N j).sgn k) (gCat C0 R ((stratBank S N j).cat k)) ∧
      (stratBank S N j).Y k ⊆ childEdges H W := by
    intro k
    have hc := hv.charge k
    rw [hS.w_eq, hS.g_eq] at hc
    exact (charge_tagW_eq_sgnQ_iff _ _ _).1 hc
  exact ⟨⟨hv.disj, hv.pw, fun k => hS.basal_phys _ (hv.basalA k),
    fun k => hS.basal_phys _ (hv.basalT k), fun k => (hch k).1⟩, fun k => (hch k).2⟩

/-- per-entry supply: the stratum bank has `m_i` occurrences of every active (sign, entry, colour) -/
lemma shape_supplies (hS : ChildShape C0 R S) {i : ℕ} (z : Fin S.P → Cat d R → ℤ)
    (hact : ∀ p v, z p v ≠ 0 → gCat C0 R v ∈ KZ H lab F W (Zstrat S N i))
    (hz : ∀ p v, (z p v).natAbs ≤ mStrat S N i) : (stratBank S N i).Supplies z := by
  intro p v
  by_cases h0 : z p v = 0
  · rw [h0]; simp
  · rw [stratBank_fiber_card]
    unfold Kstrat
    rw [if_pos ((hS.g_mem_K_iff v _).2 (hact p v h0))]
    exact hz p v

/-- **exact assembly for a child-shaped (e.g. protected) setting** -/
theorem shape_assembly (hS : ChildShape C0 R S) (hM : MacroBank S L N) (J : ℕ)
    (x : MCore H lab F W) (z : ℕ → Fin S.P → Cat d R → ℤ)
    (hzs : ∀ i p v, z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Zstrat S N i))
    (hzm : ∀ i p v, (z i p v).natAbs ≤ mStrat S N i)
    (hzx : clsQ H lab F W (x : Sym2 V → ℤ) +
      ∑ i ∈ range (J + 1), ∑ p, wcls (gCat C0 R) (z i p) = 0) :
    ShapeOutcome C0 R S N J x := by
  have hs : ∀ i, (stratBank S N i).Supplies (z i) := fun i =>
    shape_supplies hS (z i) (fun p v h => (hzs i p v h).2) (hzm i)
  have hPA : ∀ i, PhysicalActivation H lab F W (stratBank S N i) (gCat C0 R) (z i) (hs i) S.E :=
    fun i => physical_activation (shape_stratBank_valid hS hM i).1
      (shape_stratBank_valid hS hM i).2
      (fun k => (hM.cells _ (get_mem_run k)).1.2.2.2.1) (hs i)
  have htd : ∀ i j, i ≠ j → Disjoint (stratBank S N i).total (stratBank S N j).total :=
    fun i j hij => stratBank_total_disjoint hM hij
  have hpd : ∀ i j, i ≠ j → Disjoint (Bank.payload (hs i)) (Bank.payload (hs j)) :=
    fun i j hij => ((htd i j hij).mono_left (Bank.payload_subset_total (hs i))).mono_right
      (Bank.payload_subset_total (hs j))
  have hcd : ∀ i j, i ≠ j → Disjoint (Bank.cover (hs i)) (Bank.cover (hs j)) :=
    fun i j hij => ((htd i j hij).mono_left (Bank.cover_subset_total (hs i))).mono_right
      (Bank.cover_subset_total (hs j))
  set Y := (range (J + 1)).biUnion fun i => Bank.payload (hs i) with hY
  have hchY : chargeQ H lab F W Y = ∑ i ∈ range (J + 1), ∑ p, wcls (gCat C0 R) (z i p) := by
    unfold chargeQ
    rw [hY, sum_biUnion (fun i _ j _ hij => hpd i j hij)]
    refine sum_congr rfl fun i _ => ?_
    obtain ⟨-, -, -, -, -, -, hch, -⟩ := hPA i
    unfold chargeQ at hch
    rw [hch]; rfl
  have hzero : clsQ H lab F W (x : Sym2 V → ℤ) + chargeQ H lab F W Y = 0 := by
    rw [hchY]; exact hzx
  have hvS : ∀ i, (stratBank S N i).Valid S.basal S.w S.g := fun i => stratBank_valid hM
  refine ⟨z, hs, ?_⟩
  unfold ShapeProps
  refine ⟨hzs, hzm, hPA, fun i => Bank.payload_avoids_of (hs i) (stratBank_avoids hM),
    htd, hzero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← clsQ_eq_zero_iff]
    unfold clsQ
    rw [Submodule.Quotient.mk_add]
    have := chargeQ_eq H lab F W Y
    unfold clsQ at this hzero
    rw [← this]; exact hzero
  · ext e
    simp only [mem_biUnion, mem_range, mem_union]
    constructor
    · rintro ⟨i, hi, he⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hcu, -⟩ := hPA i
      rw [← hcu, mem_union] at he
      rcases he with he | he
      · exact Or.inl ⟨i, hi, he⟩
      · exact Or.inr ⟨i, hi, he⟩
    · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
      · exact ⟨i, hi, Bank.cover_subset_total (hs i) he⟩
      · exact ⟨i, hi, Bank.payload_subset_total (hs i) he⟩
  · rw [disjoint_biUnion_left]
    intro i _
    rw [disjoint_biUnion_right]
    intro j _
    by_cases hij : i = j
    · subst hij
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdj, -⟩ := hPA i
      exact hdj
    · exact ((htd i j hij).mono_left (Bank.cover_subset_total (hs i))).mono_right
        (Bank.payload_subset_total (hs j))
  · exact inherit_biUnion hS.basal_inherit (f := fun i => (stratBank S N i).total)
      (fun i => Bank.basal_total hS.basal_inherit (hvS i)) htd _
  · exact inherit_biUnion hS.basal_inherit (f := fun i => Bank.cover (hs i))
      (fun i => Bank.basal_cover (hs i) hS.basal_inherit (hvS i)) hcd _
  · exact inherit_biUnion (physBasal_inherit H lab F)
      (f := fun i => Bank.cover (hs i)) (fun i => (hPA i).2.2.2.2.2.2.2.2.1) hcd _
  · refine card_biUnion_le.trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ := hPA i
    exact hcard

/-- **zero subgroup at the start (`K_∅ = 0`, in particular zero executed rounds)**: the empty word
already gives the outcome, for every `J` -/
theorem shape_outcome_of_K_empty_bot (hS : ChildShape C0 R S) (hM : MacroBank S L N) (J : ℕ)
    (x : MCore H lab F W) (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (h0 : (KZ H lab F W ∅).toAddSubgroup = ⊥) : ShapeOutcome C0 R S N J x := by
  have hx0 : clsQ H lab F W (x : Sym2 V → ℤ) = 0 := by
    have : clsQ H lab F W (x : Sym2 V → ℤ) ∈ (KZ H lab F W ∅).toAddSubgroup := hx
    rw [h0] at this; exact this
  refine shape_assembly hS hM J x (fun _ _ _ => 0) (fun _ _ _ h => absurd rfl h)
    (fun _ _ _ => by simp) ?_
  rw [hx0]
  simp [wcls]

end

end S07V47
