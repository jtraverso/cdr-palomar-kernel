/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V43.Activation
public import RequestProject.S07V42.V40Adapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V43 §2 — physical activation in the ACTUAL intrinsic quotient, and the child residue

Ambient finite host `H` on `V` (labels `lab`, types `F`), fixed child core `W`.

* `physBasal H lab F X` : `X` has an allowed decomposition in the ORIGINAL host `H`
  (this is the basal predicate of V42 `nativeSetting`); `physBasal_inherit`.
* `childEdges H W = edges (indG H W)` : the edges of the child core `H[W]`.
* `Q = ClassQ H lab F W = (Sym2 V → ℤ) ⧸ Λ(H[W])` (V42), edge weights `wQ e = [1_e]`.

For a `Bank` valid for `physBasal` and `wQ` (any catalog charges `g : C → Q`):

* `physical_activation` : the selection `selJ hs` realises the word exactly; the payload is a
  disjoint union of the selected `Y i`, lies in the child, avoids whatever the bank avoids, has
  intrinsic class EXACTLY `∑ p, ∑ c, z p c • g c` (an equality in `Q`, torsion included); the bank
  and the cover `bank \ payload` are basal (decomposable in `H`); size and degrees are bounded.
* `residue_mem_lattice` : if `R` is in the child, disjoint from the bank, and
  `[1_R] + ∑ z • g = 0` in `Q`, then `1_{R ∪ Y_J} ∈ Λ(H[W])` (intrinsic integer physical lattice of
  the child). Nothing is assumed about decomposability of `R` or of the child.
* `residue_partition` : exact partition `bank ∪ R = cover ⊔ (R ∪ Y_J)` with `cover` basal and
  `1_{bank ∪ R} = 1_cover + 1_{R ∪ Y_J}`.
-/

open Finset Classical

noncomputable section

namespace S07V43

open TypedTriangle.SparseEdge S07V42 S07V40

variable {V I : Type*} [Fintype V] (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
  (W : Finset V)

/-- basal = has an allowed decomposition in the original host `H` -/
def physBasal (X : Finset (Sym2 V)) : Prop := ∃ D, IsDecomposition H lab F X D

/-- the edges of the child core `H[W]` -/
def childEdges : Finset (Sym2 V) := edges (indG H W)

omit [Fintype V] in
lemma physBasal_inherit : Inherit (physBasal H lab F) := by
  refine ⟨⟨∅, S07V28.isDecomposition_empty H lab F⟩, ?_⟩
  rintro X Y hXY ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
  exact ⟨D₁ ∪ D₂, S07V31.isDecomposition_union h₁ h₂ hXY⟩

omit [Fintype V] in
lemma ind_union_of_disjoint {X Y : Finset (Sym2 V)} (h : Disjoint X Y) :
    ind (X ∪ Y) = ind X + ind Y := by
  funext e
  simp only [ind, Pi.add_apply, mem_union]
  by_cases hx : e ∈ X
  · have hy : e ∉ Y := disjoint_left.1 h hx
    simp [hx, hy]
  · by_cases hy : e ∈ Y <;> simp [hx, hy]

omit [Fintype V] in
lemma chargeQ_union {X Y : Finset (Sym2 V)} (h : Disjoint X Y) :
    chargeQ H lab F W (X ∪ Y) = chargeQ H lab F W X + chargeQ H lab F W Y := by
  unfold chargeQ; exact sum_union h

omit [Fintype V] in
lemma charge_eq_chargeQ (Y : Finset (Sym2 V)) :
    S07V40.charge (wQ H lab F W) Y = chargeQ H lab F W Y := rfl

omit [Fintype V] in
/-- a class vanishes in `Q` iff the vector lies in `Λ(H[W])` -/
lemma clsQ_eq_zero_iff (x : Sym2 V → ℤ) : clsQ H lab F W x = 0 ↔ x ∈ LamCore H lab F W :=
  Submodule.Quotient.mk_eq_zero _

variable {H lab F W} {ι C : Type*} [Fintype ι] [Fintype C] {P : ℕ}
  {b : Bank V ι C P} {g : C → ClassQ H lab F W} {z : Fin P → C → ℤ}

/-- **intrinsic class of the payload** (`[1_{Y_J}] = ∑ z • g` in `Q`) -/
theorem chargeQ_payload (hv : b.Valid (physBasal H lab F) (wQ H lab F W) g)
    (hs : b.Supplies z) :
    chargeQ H lab F W (Bank.payload hs) = ∑ p, ∑ c, z p c • g c :=
  Bank.charge_payload hs hv

theorem clsQ_payload (hv : b.Valid (physBasal H lab F) (wQ H lab F W) g)
    (hs : b.Supplies z) :
    clsQ H lab F W (ind (Bank.payload hs)) = ∑ p, ∑ c, z p c • g c := by
  rw [← chargeQ_eq]; exact chargeQ_payload hv hs

/-- **the child residue lies in the intrinsic integer physical lattice of the child** -/
theorem residue_mem_lattice (hv : b.Valid (physBasal H lab F) (wQ H lab F W) g)
    (hs : b.Supplies z) {R : Finset (Sym2 V)} (hRB : Disjoint R b.total)
    (hres : chargeQ H lab F W R + ∑ p, ∑ c, z p c • g c = 0) :
    ind (R ∪ Bank.payload hs) ∈ LamCore H lab F W := by
  rw [← clsQ_eq_zero_iff, ← chargeQ_eq,
    chargeQ_union H lab F W (hRB.mono_right (Bank.payload_subset_total hs)),
    chargeQ_payload hv hs, hres]

/-- the child residue stays in the child -/
theorem residue_subset_child (hY : ∀ i, b.Y i ⊆ childEdges H W) (hs : b.Supplies z)
    {R : Finset (Sym2 V)} (hR : R ⊆ childEdges H W) :
    R ∪ Bank.payload hs ⊆ childEdges H W :=
  union_subset hR (Bank.payload_subset_of hs hY)

omit [Fintype V] in
/-- **exact partition** separating the basal covered complement from the child residue -/
theorem residue_partition (hv : b.Valid (physBasal H lab F) (wQ H lab F W) g)
    (hs : b.Supplies z) {R : Finset (Sym2 V)} (hRB : Disjoint R b.total) :
    b.total ∪ R = Bank.cover hs ∪ (R ∪ Bank.payload hs) ∧
      Disjoint (Bank.cover hs) (R ∪ Bank.payload hs) ∧
      physBasal H lab F (Bank.cover hs) ∧
      ind (b.total ∪ R) = ind (Bank.cover hs) + ind (R ∪ Bank.payload hs) := by
  have hdisj : Disjoint (Bank.cover hs) (R ∪ Bank.payload hs) :=
    disjoint_union_right.2 ⟨(hRB.symm.mono_left (Bank.cover_subset_total hs)),
      Bank.disjoint_cover_payload hs hv⟩
  have heq : b.total ∪ R = Bank.cover hs ∪ (R ∪ Bank.payload hs) := by
    rw [← Bank.cover_union_payload hs hv]
    ext e; simp only [mem_union]; tauto
  exact ⟨heq, hdisj, Bank.basal_cover hs (physBasal_inherit H lab F) hv,
    by rw [heq, ind_union_of_disjoint hdisj]⟩

variable (H lab F W) in
/-- **The physical activation specification** for the selection `J = selJ hs` of a bank `b`
(word `z`, catalog charges `g`, cell bound `Ecell`), items 1–5:
1. exact signed counts and no wrong sign; payload `Y_J` is the disjoint union of the selected
   `Y i`, lies in the child and inside the bank (hence avoids whatever the bank avoids);
2. `[1_{Y_J}] = ∑ p, ∑ c, z p c • g c` in `Q = (Sym2 V → ℤ) ⧸ Λ(H[W])` (torsion included);
3. the bank `B` and the cover `B \ Y_J` are basal (decomposable in `H`); `cover ⊔ Y_J = B`;
   unselected cells keep their whole total in the cover;
4. size and every local degree of `Y_J` bounded by the bank and by `Ecell` × word cost;
   stage-wise charge and size;
5. any child residue `R` disjoint from `B` with `[1_R] + ∑ z • g = 0` gives
   `1_{R ∪ Y_J} ∈ Λ(H[W])`, with the exact partition `B ∪ R = cover ⊔ (R ∪ Y_J)` and
   `1_{B ∪ R} = 1_cover + 1_{R ∪ Y_J}`. -/
def PhysicalActivation (b : Bank V ι C P) (g : C → ClassQ H lab F W) (z : Fin P → C → ℤ)
    (hs : b.Supplies z) (Ecell : ℕ) : Prop :=
    -- 1. selection and payload
    (∀ p c s, ((Bank.selJ hs).filter (fun i => b.col i = p ∧ b.cat i = c ∧ b.sgn i = s)).card =
        if s = decide (0 < z p c) then (z p c).natAbs else 0) ∧
    (∀ i ∈ Bank.selJ hs, z (b.col i) (b.cat i) ≠ 0 ∧
        b.sgn i = decide (0 < z (b.col i) (b.cat i))) ∧
    Bank.payload hs = (Bank.selJ hs).biUnion b.Y ∧
    ((Bank.selJ hs : Set ι).PairwiseDisjoint b.Y) ∧
    Bank.payload hs ⊆ childEdges H W ∧ Bank.payload hs ⊆ b.total ∧
    -- 2. exact intrinsic charge
    chargeQ H lab F W (Bank.payload hs) = ∑ p, ∑ c, z p c • g c ∧
    -- 3. basal bank and basal covered complement
    physBasal H lab F b.total ∧ physBasal H lab F (Bank.cover hs) ∧
    Bank.cover hs = b.total \ Bank.payload hs ∧
    Bank.cover hs ∪ Bank.payload hs = b.total ∧ Disjoint (Bank.cover hs) (Bank.payload hs) ∧
    (∀ i, i ∉ Bank.selJ hs → b.tot i ⊆ Bank.cover hs) ∧
    -- 4. size and degrees
    (Bank.payload hs).card ≤ Ecell * ∑ p, ∑ c, (z p c).natAbs ∧
    (∀ v, deg (Bank.payload hs) v ≤ deg b.total v ∧
      deg (Bank.payload hs) v ≤ Ecell * ∑ p, ∑ c, (z p c).natAbs) ∧
    (∀ p, chargeQ H lab F W (Bank.payloadStage hs p) = ∑ c, z p c • g c ∧
      (Bank.payloadStage hs p).card ≤ Ecell * ∑ c, (z p c).natAbs) ∧
    -- 5. child residue
    (∀ R : Finset (Sym2 V), R ⊆ childEdges H W → Disjoint R b.total →
      chargeQ H lab F W R + ∑ p, ∑ c, z p c • g c = 0 →
      R ∪ Bank.payload hs ⊆ childEdges H W ∧
      ind (R ∪ Bank.payload hs) ∈ LamCore H lab F W ∧
      b.total ∪ R = Bank.cover hs ∪ (R ∪ Bank.payload hs) ∧
      Disjoint (Bank.cover hs) (R ∪ Bank.payload hs) ∧
      ind (b.total ∪ R) = ind (Bank.cover hs) + ind (R ∪ Bank.payload hs))

/-- **Physical integer activation** (finite occurrence interface).  For a bank valid in the
ambient host (`physBasal`, intrinsic weights `wQ`), with payloads in the child and cells of
size `≤ Ecell`, every supplied word is physically activated by `selJ hs`
(`PhysicalActivation`, items 1–5). -/
theorem physical_activation (hv : b.Valid (physBasal H lab F) (wQ H lab F W) g)
    (hY : ∀ i, b.Y i ⊆ childEdges H W) {Ecell : ℕ} (hE : ∀ i, (b.tot i).card ≤ Ecell)
    (hs : b.Supplies z) : PhysicalActivation H lab F W b g z hs Ecell :=
  ⟨Bank.selJ_count_sign hs, fun _ hi => Bank.selJ_sign hs hi, rfl,
    Bank.Y_pairwiseDisjoint hv _, Bank.payload_subset_of hs hY, Bank.payload_subset_total hs,
    chargeQ_payload hv hs, Bank.basal_total (physBasal_inherit H lab F) hv,
    Bank.basal_cover hs (physBasal_inherit H lab F) hv, Bank.cover_eq_sdiff hs hv,
    Bank.cover_union_payload hs hv, Bank.disjoint_cover_payload hs hv,
    fun _ hi => Bank.tot_subset_cover_of_not_mem hs hi, Bank.card_payload_le hs hv hE,
    fun v => Bank.deg_payload_le hs hv hE v,
    fun p => ⟨Bank.charge_payloadStage hs hv p, Bank.card_payloadStage_le hs hv hE p⟩,
    fun _ hR hRB hres => ⟨residue_subset_child hY hs hR, residue_mem_lattice hv hs hRB hres,
      (residue_partition hv hs hRB).1, (residue_partition hv hs hRB).2.1,
      (residue_partition hv hs hRB).2.2.2⟩⟩

end S07V43
