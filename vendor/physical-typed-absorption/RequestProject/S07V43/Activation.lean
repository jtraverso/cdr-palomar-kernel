/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V40.Basic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V43 §1 — integer activation of a finite bank of OCCURRENCES

A finite bank is indexed by a finite type `ι` of **occurrences** (not by edge sets: two
occurrences may carry equal, even empty, edge sets).  Occurrence `i` carries a tag
`(sgn i, cat i, col i)` and two finite edge sets `A i`, `Y i` (off part, charged part); its total
is `tot i = A i ∪ Y i`.

* `Bank.Valid basal w g` : `A i`, `Y i` disjoint; totals of DISTINCT occurrences disjoint;
  `A i` and `tot i` basal; `charge (Y i) = ± g (cat i)`.
* Given an integer word `z : Fin P → C → ℤ` and enough occurrences of the requested sign in every
  `(p, c)` fibre (`Supplies b z`), `sel b z hs p c` is a set of EXACTLY `|z p c|` occurrences of
  sign `decide (0 < z p c)`, catalog `c`, colour `p`; `selJ` is their union.
* `payload = ⋃_{i ∈ J} Y i` (an actual disjoint union), `cover = ⋃_{i∈J} A i ∪ ⋃_{i∉J} tot i`.

Main facts: `selJ_count`, `selJ_sign`, `charge_payload` (exact equality in `Q`, torsion
included), `cover_eq_sdiff` / `cover_union_payload` / `disjoint_cover_payload` (exact
partition of the bank), `basal_total`, `basal_cover`, `card_payload_le`, `deg_payload_le`,
and stage-wise versions.
-/

@[expose] public section

namespace S07V43

open Finset Classical S07V40

noncomputable section

variable {V ι C Q : Type*} [Fintype ι] [Fintype C] [AddCommGroup Q] {P : ℕ}

/-- A finite bank of occurrences. -/
structure Bank (V ι C : Type*) (P : ℕ) where
  /-- sign of the occurrence -/
  sgn : ι → Bool
  /-- catalog entry -/
  cat : ι → C
  /-- colour (activation stage) -/
  col : ι → Fin P
  /-- off part -/
  A : ι → Finset (Sym2 V)
  /-- charged part -/
  Y : ι → Finset (Sym2 V)

namespace Bank

variable (b : Bank V ι C P)

/-- total edge set of occurrence `i` -/
def tot (i : ι) : Finset (Sym2 V) := b.A i ∪ b.Y i

/-- the union of all totals -/
def total : Finset (Sym2 V) := univ.biUnion b.tot

/-- occurrences with tag `(s, c, p)` -/
def fiber (s : Bool) (c : C) (p : Fin P) : Finset ι :=
  univ.filter (fun i => b.sgn i = s ∧ b.cat i = c ∧ b.col i = p)

/-- validity of a bank -/
structure Valid (basal : Finset (Sym2 V) → Prop) (w : Sym2 V → Q) (g : C → Q) : Prop where
  disj : ∀ i, Disjoint (b.A i) (b.Y i)
  pw : ∀ i j, i ≠ j → Disjoint (b.tot i) (b.tot j)
  basalA : ∀ i, basal (b.A i)
  basalT : ∀ i, basal (b.tot i)
  charge : ∀ i, charge w (b.Y i) = sgnQ (b.sgn i) (g (b.cat i))

/-- enough occurrences of the requested sign in every fibre -/
def Supplies (z : Fin P → C → ℤ) : Prop :=
  ∀ p c, (z p c).natAbs ≤ (b.fiber (decide (0 < z p c)) c p).card

end Bank

/-- the basal predicate holds for `∅` and is inherited by disjoint unions -/
def Inherit (basal : Finset (Sym2 V) → Prop) : Prop :=
  basal ∅ ∧ ∀ X Y : Finset (Sym2 V), Disjoint X Y → basal X → basal Y → basal (X ∪ Y)

omit [Fintype ι] in
lemma inherit_biUnion {basal : Finset (Sym2 V) → Prop} (hB : Inherit basal)
    {f : ι → Finset (Sym2 V)} (hf : ∀ i, basal (f i))
    (hpw : ∀ i j, i ≠ j → Disjoint (f i) (f j)) : ∀ s : Finset ι, basal (s.biUnion f) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using hB.1
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine hB.2 _ _ ?_ (hf a) ih
    rw [disjoint_biUnion_right]
    intro i hi
    exact hpw a i (fun h => ha (h ▸ hi))

namespace Bank

variable {b : Bank V ι C P}

omit [Fintype ι] [Fintype C] in
lemma Y_subset_tot (i : ι) : b.Y i ⊆ b.tot i := subset_union_right

omit [Fintype ι] [Fintype C] in
lemma A_subset_tot (i : ι) : b.A i ⊆ b.tot i := subset_union_left

omit [Fintype C] in
lemma tot_subset_total (i : ι) : b.tot i ⊆ b.total := subset_biUnion_of_mem _ (mem_univ i)

/-! ### Selection -/

omit [Fintype C] in
lemma exists_sel {z : Fin P → C → ℤ} (hs : b.Supplies z) (p : Fin P) (c : C) :
    ∃ t ⊆ b.fiber (decide (0 < z p c)) c p, t.card = (z p c).natAbs :=
  exists_subset_card_eq (hs p c)

/-- the selected occurrences of colour `p` and catalog entry `c` -/
def sel {z : Fin P → C → ℤ} (hs : b.Supplies z) (p : Fin P) (c : C) : Finset ι :=
  (exists_sel hs p c).choose

/-- the selected occurrences `J` -/
def selJ {z : Fin P → C → ℤ} (hs : b.Supplies z) : Finset ι :=
  univ.biUnion (fun pc : Fin P × C => sel hs pc.1 pc.2)

variable {z : Fin P → C → ℤ} (hs : b.Supplies z)

omit [Fintype C] in
lemma sel_subset (p : Fin P) (c : C) : sel hs p c ⊆ b.fiber (decide (0 < z p c)) c p :=
  (exists_sel hs p c).choose_spec.1

omit [Fintype C] in
lemma card_sel (p : Fin P) (c : C) : (sel hs p c).card = (z p c).natAbs :=
  (exists_sel hs p c).choose_spec.2

omit [Fintype C] in
lemma mem_sel {p : Fin P} {c : C} {i : ι} (h : i ∈ sel hs p c) :
    b.sgn i = decide (0 < z p c) ∧ b.cat i = c ∧ b.col i = p := by
  have := sel_subset hs p c h
  simp only [fiber, mem_filter, mem_univ, true_and] at this
  exact this

lemma mem_selJ {i : ι} : i ∈ selJ hs ↔ i ∈ sel hs (b.col i) (b.cat i) := by
  constructor
  · intro h
    simp only [selJ, mem_biUnion, mem_univ, true_and] at h
    obtain ⟨⟨p, c⟩, hpc⟩ := h
    obtain ⟨-, h2, h3⟩ := mem_sel hs hpc
    simp only at h2 h3
    rw [h2, h3]; exact hpc
  · intro h
    simp only [selJ, mem_biUnion, mem_univ, true_and]
    exact ⟨⟨b.col i, b.cat i⟩, h⟩

lemma sel_pairwiseDisjoint :
    ((univ : Finset (Fin P × C)) : Set (Fin P × C)).PairwiseDisjoint (fun pc => sel hs pc.1 pc.2) := by
  intro x _ y _ hxy
  rw [Function.onFun, disjoint_left]
  intro i hx hy
  obtain ⟨-, hx2, hx3⟩ := mem_sel hs hx
  obtain ⟨-, hy2, hy3⟩ := mem_sel hs hy
  exact hxy (Prod.ext (hx3.symm.trans hy3) (hx2.symm.trans hy2))

/-- **no wrong sign**: every selected occurrence has the sign of its coefficient, which is
nonzero -/
theorem selJ_sign {i : ι} (h : i ∈ selJ hs) :
    z (b.col i) (b.cat i) ≠ 0 ∧ b.sgn i = decide (0 < z (b.col i) (b.cat i)) := by
  rw [mem_selJ] at h
  refine ⟨fun h0 => ?_, (mem_sel hs h).1⟩
  have := card_sel hs (b.col i) (b.cat i)
  rw [h0, Int.natAbs_zero, card_eq_zero] at this
  rw [this] at h; simp at h

/-- **exact counts**: `J` has exactly `|z p c|` occurrences of colour `p` and entry `c` -/
theorem selJ_count (p : Fin P) (c : C) :
    ((selJ hs).filter (fun i => b.col i = p ∧ b.cat i = c)).card = (z p c).natAbs := by
  rw [← card_sel hs p c]
  congr 1
  ext i
  simp only [mem_filter, mem_selJ]
  constructor
  · rintro ⟨h, h1, h2⟩; rw [h1, h2] at h; exact h
  · intro h
    obtain ⟨-, h2, h3⟩ := mem_sel hs h
    exact ⟨by rw [h2, h3]; exact h, h3, h2⟩

/-- **exact signed counts**: occurrences of the requested sign: `|z p c|`; of the other sign:
none -/
theorem selJ_count_sign (p : Fin P) (c : C) (s : Bool) :
    ((selJ hs).filter (fun i => b.col i = p ∧ b.cat i = c ∧ b.sgn i = s)).card =
      if s = decide (0 < z p c) then (z p c).natAbs else 0 := by
  split_ifs with hsz
  · rw [← selJ_count hs p c]
    congr 1
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨h, h1, h2, -⟩; exact ⟨h, h1, h2⟩
    · rintro ⟨h, h1, h2⟩
      refine ⟨h, h1, h2, ?_⟩
      rw [(selJ_sign hs h).2, h1, h2, hsz]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i h ⟨h1, h2, h3⟩
    apply hsz
    rw [← h3, (selJ_sign hs h).2, h1, h2]

lemma card_selJ : (selJ hs).card = ∑ p, ∑ c, (z p c).natAbs := by
  rw [selJ, card_biUnion (sel_pairwiseDisjoint hs), Fintype.sum_prod_type]
  simp only [card_sel]

/-! ### The payload and the cover -/

/-- the selected payload `Y_J = ⋃_{i ∈ J} Y i` -/
def payload : Finset (Sym2 V) := (selJ hs).biUnion b.Y

/-- mode of an occurrence: `A i` if selected (OFF), `tot i` otherwise -/
def mode (i : ι) : Finset (Sym2 V) := if i ∈ selJ hs then b.A i else b.tot i

/-- the basal cover `⋃_{i ∈ J} A i ∪ ⋃_{i ∉ J} tot i` -/
def cover : Finset (Sym2 V) := univ.biUnion (mode hs)

lemma mode_subset (i : ι) : mode hs i ⊆ b.tot i := by
  unfold mode; split_ifs
  · exact A_subset_tot i
  · exact subset_rfl

lemma payload_subset_total : payload hs ⊆ b.total :=
  biUnion_subset.2 fun i _ => (Y_subset_tot i).trans (tot_subset_total i)

lemma cover_subset_total : cover hs ⊆ b.total := biUnion_mono fun i _ => mode_subset hs i

variable {basal : Finset (Sym2 V) → Prop} {w : Sym2 V → Q} {g : C → Q}

omit [Fintype ι] [Fintype C] in
lemma Y_pairwiseDisjoint (hv : b.Valid basal w g) (s : Finset ι) :
    (s : Set ι).PairwiseDisjoint b.Y := by
  intro i _ j _ hij
  exact (hv.pw i j hij).mono (Y_subset_tot i) (Y_subset_tot j)

/-- **exact partition**: the cover is the bank minus the payload -/
theorem cover_eq_sdiff (hv : b.Valid basal w g) : cover hs = b.total \ payload hs := by
  ext e
  simp only [cover, payload, total, mem_sdiff, mem_biUnion, mem_univ, true_and, not_exists,
    not_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i, mode_subset hs i hi⟩, fun j hj hej => ?_⟩
    by_cases hij : i = j
    · subst hij
      have : e ∈ b.A i := by simpa [mode, hj] using hi
      exact disjoint_left.1 (hv.disj i) this hej
    · exact disjoint_left.1 (hv.pw i j hij) (mode_subset hs i hi) (Y_subset_tot j hej)
  · rintro ⟨⟨i, hi⟩, hn⟩
    refine ⟨i, ?_⟩
    unfold mode
    split_ifs with hJ
    · rcases mem_union.1 hi with h | h
      · exact h
      · exact absurd h (hn i hJ)
    · exact hi

theorem disjoint_cover_payload (hv : b.Valid basal w g) : Disjoint (cover hs) (payload hs) := by
  rw [cover_eq_sdiff hs hv]; exact sdiff_disjoint

theorem cover_union_payload (hv : b.Valid basal w g) :
    cover hs ∪ payload hs = b.total := by
  rw [cover_eq_sdiff hs hv, sdiff_union_of_subset (payload_subset_total hs)]

omit [Fintype C] in
/-- **the bank is basal** -/
theorem basal_total (hB : Inherit basal) (hv : b.Valid basal w g) : basal b.total :=
  inherit_biUnion hB hv.basalT hv.pw univ

/-- **the bank minus the payload is basal** (selected cells OFF, others ON) -/
theorem basal_cover (hB : Inherit basal) (hv : b.Valid basal w g) : basal (cover hs) := by
  refine inherit_biUnion hB (fun i => ?_) (fun i j hij =>
    (hv.pw i j hij).mono (mode_subset hs i) (mode_subset hs j)) univ
  unfold mode; split_ifs
  · exact hv.basalA i
  · exact hv.basalT i

theorem basal_total_sdiff_payload (hB : Inherit basal) (hv : b.Valid basal w g) :
    basal (b.total \ payload hs) := by
  rw [← cover_eq_sdiff hs hv]; exact basal_cover hs hB hv

/-- unselected occurrences (in particular all occurrences of any colour with a zero word)
retain their whole cell inside the cover -/
theorem tot_subset_cover_of_not_mem {i : ι} (hi : i ∉ selJ hs) : b.tot i ⊆ cover hs := by
  intro e he
  simp only [cover, mem_biUnion, mem_univ, true_and]
  exact ⟨i, by simp [mode, hi, he]⟩

theorem not_mem_selJ_of_zero {p : Fin P} (hz : ∀ c, z p c = 0) {i : ι} (hi : b.col i = p) :
    i ∉ selJ hs := fun h => (selJ_sign hs h).1 (by rw [hi]; exact hz _)

/-! ### Charge -/

omit [Fintype ι] [Fintype C] in
lemma natAbs_smul_sgnQ (x : Q) (n : ℤ) :
    (n.natAbs) • sgnQ (decide (0 < n)) x = n • x := by
  unfold sgnQ
  rcases lt_or_ge 0 n with h | h
  · rw [if_pos (by simpa using h), ← natCast_zsmul, Int.natCast_natAbs, abs_of_pos h]
  · rw [if_neg (by simpa using h), ← natCast_zsmul, Int.natCast_natAbs, abs_of_nonpos h,
      smul_neg, neg_smul, neg_neg]

omit [Fintype C] in
lemma sum_sel_sgnQ (p : Fin P) (c : C) :
    ∑ i ∈ sel hs p c, sgnQ (b.sgn i) (g (b.cat i)) = z p c • g c := by
  rw [sum_congr rfl (g := fun _ => sgnQ (decide (0 < z p c)) (g c)) (fun i hi => by
      rw [(mem_sel hs hi).1, (mem_sel hs hi).2.1]), sum_const, card_sel, natAbs_smul_sgnQ]

/-- **exact intrinsic charge of the payload** (an equality in `Q`; torsion included) -/
theorem charge_payload (hv : b.Valid basal w g) :
    charge w (payload hs) = ∑ p, ∑ c, z p c • g c := by
  unfold charge payload
  rw [sum_biUnion (Y_pairwiseDisjoint hv _)]
  rw [sum_congr rfl (fun i _ => (show ∑ e ∈ b.Y i, w e = _ from hv.charge i))]
  unfold selJ
  rw [sum_biUnion (sel_pairwiseDisjoint hs), Fintype.sum_prod_type]
  simp only [sum_sel_sgnQ]

/-! ### Size and degrees -/

theorem card_payload (hv : b.Valid basal w g) :
    (payload hs).card = ∑ i ∈ selJ hs, (b.Y i).card :=
  card_biUnion (Y_pairwiseDisjoint hv _)

/-- size of the payload: at most `Ecell` times the word cost -/
theorem card_payload_le (hv : b.Valid basal w g) {Ecell : ℕ}
    (hE : ∀ i, (b.tot i).card ≤ Ecell) :
    (payload hs).card ≤ Ecell * ∑ p, ∑ c, (z p c).natAbs := by
  rw [card_payload hs hv, ← card_selJ hs, mul_comm]
  calc ∑ i ∈ selJ hs, (b.Y i).card ≤ ∑ _i ∈ selJ hs, Ecell :=
        sum_le_sum fun i _ => (card_le_card (Y_subset_tot i)).trans (hE i)
    _ = _ := by simp

/-- every local degree of the payload is bounded by that of the bank and by `Ecell` times the
word cost -/
theorem deg_payload_le (hv : b.Valid basal w g) {Ecell : ℕ}
    (hE : ∀ i, (b.tot i).card ≤ Ecell) (v : V) :
    deg (payload hs) v ≤ deg b.total v ∧
      deg (payload hs) v ≤ Ecell * ∑ p, ∑ c, (z p c).natAbs :=
  ⟨deg_mono (payload_subset_total hs) v,
    (card_filter_le _ _).trans (card_payload_le hs hv hE)⟩

/-! ### Stages (colours) -/

/-- the selected occurrences of colour `p` -/
def selStage (p : Fin P) : Finset ι := univ.biUnion (fun c => sel hs p c)

/-- the payload of colour `p` -/
def payloadStage (p : Fin P) : Finset (Sym2 V) := (selStage hs p).biUnion b.Y

lemma selStage_eq (p : Fin P) : selStage hs p = (selJ hs).filter (fun i => b.col i = p) := by
  ext i
  simp only [selStage, mem_biUnion, mem_univ, true_and, mem_filter, mem_selJ]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨-, h2, h3⟩ := mem_sel hs hc
    exact ⟨by rw [h2, h3]; exact hc, h3⟩
  · rintro ⟨h, h3⟩; exact ⟨b.cat i, h3 ▸ h⟩

theorem payload_eq_biUnion_stage : payload hs = univ.biUnion (payloadStage hs) := by
  ext e
  simp only [payload, payloadStage, mem_biUnion, mem_univ, true_and, selStage_eq, mem_filter]
  constructor
  · rintro ⟨i, hi, he⟩; exact ⟨b.col i, i, ⟨hi, rfl⟩, he⟩
  · rintro ⟨-, i, ⟨hi, -⟩, he⟩; exact ⟨i, hi, he⟩

lemma sel_stage_pairwiseDisjoint (p : Fin P) :
    ((univ : Finset C) : Set C).PairwiseDisjoint (fun c => sel hs p c) := by
  intro x _ y _ hxy
  rw [Function.onFun, disjoint_left]
  intro i hx hy
  exact hxy ((mem_sel hs hx).2.1.symm.trans (mem_sel hs hy).2.1)

theorem charge_payloadStage (hv : b.Valid basal w g) (p : Fin P) :
    charge w (payloadStage hs p) = ∑ c, z p c • g c := by
  unfold charge payloadStage
  rw [sum_biUnion (Y_pairwiseDisjoint hv _), sum_congr rfl (fun i _ => (show ∑ e ∈ b.Y i, w e = _ from hv.charge i)), selStage,
    sum_biUnion (sel_stage_pairwiseDisjoint hs p)]
  simp only [sum_sel_sgnQ]

theorem card_payloadStage_le (hv : b.Valid basal w g) {Ecell : ℕ}
    (hE : ∀ i, (b.tot i).card ≤ Ecell) (p : Fin P) :
    (payloadStage hs p).card ≤ Ecell * ∑ c, (z p c).natAbs := by
  unfold payloadStage
  rw [card_biUnion (Y_pairwiseDisjoint hv _)]
  have hc : (selStage hs p).card = ∑ c, (z p c).natAbs := by
    rw [selStage, card_biUnion (sel_stage_pairwiseDisjoint hs p)]
    simp only [card_sel]
  rw [← hc, mul_comm]
  calc ∑ i ∈ selStage hs p, (b.Y i).card ≤ ∑ _i ∈ selStage hs p, Ecell :=
        sum_le_sum fun i _ => (card_le_card (Y_subset_tot i)).trans (hE i)
    _ = _ := by simp

theorem payloadStage_disjoint (hv : b.Valid basal w g) {p p' : Fin P} (hpp : p ≠ p') :
    Disjoint (payloadStage hs p) (payloadStage hs p') := by
  unfold payloadStage
  rw [disjoint_biUnion_left]
  intro i hi
  rw [disjoint_biUnion_right]
  intro j hj
  have hij : i ≠ j := by
    rintro rfl
    rw [selStage_eq, mem_filter] at hi hj
    exact hpp (hi.2.symm.trans hj.2)
  exact (hv.pw i j hij).mono (Y_subset_tot i) (Y_subset_tot j)

/-! ### Avoidance -/

theorem payload_disjoint_of (X : Finset (Sym2 V)) (h : Disjoint b.total X) :
    Disjoint (payload hs) X := h.mono_left (payload_subset_total hs)

theorem payload_avoids_of {Z : Finset V} (h : Avoids Z b.total) : Avoids Z (payload hs) :=
  fun e he => h e (payload_subset_total hs he)

theorem payload_subset_of {X : Finset (Sym2 V)} (h : ∀ i, b.Y i ⊆ X) : payload hs ⊆ X :=
  biUnion_subset.2 fun i _ => h i

/-- uniform supply: every fibre has at least `m` occurrences and every colour costs `≤ m` -/
theorem supplies_of_uniform {m : ℕ} (hm : ∀ s c p, m ≤ (b.fiber s c p).card)
    (hz : ∀ p, ∑ c, (z p c).natAbs ≤ m) : b.Supplies z :=
  fun p c => (single_le_sum (f := fun c => (z p c).natAbs) (fun _ _ => Nat.zero_le _)
    (mem_univ c)).trans ((hz p).trans (hm _ c p))

end Bank

end

end S07V43
