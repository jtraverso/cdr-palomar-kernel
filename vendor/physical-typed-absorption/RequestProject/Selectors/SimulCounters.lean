/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Finite counters for the simultaneous layer (S07 §7) — V21

Pure finite combinatorics, no graph-theoretic input:

* `edeg E y` : number of edges of the finite edge set `E` containing `y` (degree in `E`).
* `auxCount Z W x` : number of roots `v ∈ Z` at which `x` is an AUXILIARY (`x ∈ W v`).
* `sum_auxCount` : double counting, `∑_x auxCount = ∑_v |W v|`.
* `satSet` / `satSet_card_le` : the vertices whose counter has reached the ceiling `q`;
  if every root has at most `a` auxiliaries, `|sat| ≤ a·|Z| / q` (`q > 0`).
* `auxCount_insert_le` : the counter step: a vertex chosen only while unsaturated stays `≤ q`.
* `portCount_le` : PORTS are counted separately, by degree: a vertex is a port
  (`x ∈ N_X(v)`) of at most `deg_X(x)` roots.  Ports are not subject to saturation.
* `edeg_biUnion_le` : the union of per-root edge sets, each of degree `≤ c` and supported on
  a per-root vertex set, has degree `≤ c · #{v : y supported at v}`.
-/

namespace SelSimul

open Finset

variable {ι β : Type*} [DecidableEq β]

/-- Degree of `y` in a finite edge set: number of edges containing `y`. -/
def edeg (E : Finset (Sym2 β)) (y : β) : ℕ := (E.filter (fun f => y ∈ f)).card

lemma edeg_mono {E E' : Finset (Sym2 β)} (h : E ⊆ E') (y : β) : edeg E y ≤ edeg E' y :=
  card_le_card (filter_subset_filter _ h)

lemma edeg_union_le (E E' : Finset (Sym2 β)) (y : β) :
    edeg (E ∪ E') y ≤ edeg E y + edeg E' y := by
  unfold edeg; rw [filter_union]; exact card_union_le _ _

/-- For a simple graph, `edeg` of its edge set is the usual degree. -/
lemma edeg_edgeFinset [Fintype β] (X : SimpleGraph β) [DecidableRel X.Adj] (y : β) :
    edeg X.edgeFinset y = X.degree y := by
  unfold edeg
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

/-- Number of roots at which `x` is an auxiliary. -/
def auxCount (Z : Finset ι) (W : ι → Finset β) (x : β) : ℕ := (Z.filter (fun v => x ∈ W v)).card

/-- **Double counting**: total auxiliary occurrences. -/
theorem sum_auxCount (Z : Finset ι) (W : ι → Finset β) (T : Finset β)
    (hT : ∀ v ∈ Z, W v ⊆ T) : ∑ x ∈ T, auxCount Z W x = ∑ v ∈ Z, (W v).card := by
  unfold auxCount
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v hv => ?_
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (hT v hv)]

/-- Total occurrences are bounded by `a · |Z|` when each root has at most `a` auxiliaries. -/
theorem sum_auxCount_le (Z : Finset ι) (W : ι → Finset β) (T : Finset β)
    (hT : ∀ v ∈ Z, W v ⊆ T) {a : ℕ} (ha : ∀ v ∈ Z, (W v).card ≤ a) :
    ∑ x ∈ T, auxCount Z W x ≤ a * Z.card := by
  rw [sum_auxCount Z W T hT, mul_comm]
  exact sum_le_card_nsmul _ _ _ ha |>.trans (by simp)

/-- The saturated vertices: counter at least `q`. -/
def satSet (Z : Finset ι) (W : ι → Finset β) (q : ℕ) : Finset β :=
  (Z.biUnion W).filter (fun x => q ≤ auxCount Z W x)

lemma auxCount_eq_zero_of_not_mem {Z : Finset ι} {W : ι → Finset β} {x : β}
    (hx : x ∉ Z.biUnion W) : auxCount Z W x = 0 := by
  unfold auxCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v hv hxv
  exact hx (mem_biUnion.mpr ⟨v, hv, hxv⟩)

lemma lt_of_not_mem_satSet {Z : Finset ι} {W : ι → Finset β} {q : ℕ} (hq : 0 < q) {x : β}
    (hx : x ∉ satSet Z W q) : auxCount Z W x < q := by
  by_cases h : x ∈ Z.biUnion W
  · by_contra h'
    exact hx (mem_filter.mpr ⟨h, by omega⟩)
  · rw [auxCount_eq_zero_of_not_mem h]; exact hq

/-- `q · |sat| ≤` total occurrences. -/
theorem satSet_card_mul_le (Z : Finset ι) (W : ι → Finset β) (q : ℕ) :
    q * (satSet Z W q).card ≤ ∑ v ∈ Z, (W v).card := by
  rw [← sum_auxCount Z W (Z.biUnion W) (fun v hv => subset_biUnion_of_mem W hv)]
  calc q * (satSet Z W q).card = ∑ _x ∈ satSet Z W q, q := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ satSet Z W q, auxCount Z W x := sum_le_sum fun x hx => (mem_filter.mp hx).2
    _ ≤ ∑ x ∈ Z.biUnion W, auxCount Z W x := sum_le_sum_of_subset (filter_subset _ _)

/-- **Saturated set bound**: `|sat| ≤ a·|Z| / q` for `q > 0` and at most `a` auxiliaries
per root. -/
theorem satSet_card_le (Z : Finset ι) (W : ι → Finset β) {q a : ℕ} (hq : 0 < q)
    (ha : ∀ v ∈ Z, (W v).card ≤ a) : (satSet Z W q).card ≤ a * Z.card / q := by
  rw [Nat.le_div_iff_mul_le hq, mul_comm]
  refine (satSet_card_mul_le Z W q).trans ?_
  rw [mul_comm]
  exact sum_le_card_nsmul _ _ _ ha |>.trans (by simp [mul_comm])

/-- Counter after adding a new root `a ∉ Z`. -/
lemma auxCount_insert [DecidableEq ι] {Z : Finset ι} {a : ι} (ha : a ∉ Z) (W : ι → Finset β) (x : β) :
    auxCount (insert a Z) W x = auxCount Z W x + if x ∈ W a then 1 else 0 := by
  unfold auxCount
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => ha (mem_filter.mp h').1)]
  · rfl

/-- Counters only see the roots of `Z`. -/
lemma auxCount_congr {Z : Finset ι} {W W' : ι → Finset β} (h : ∀ v ∈ Z, W v = W' v) (x : β) :
    auxCount Z W x = auxCount Z W' x := by
  unfold auxCount
  congr 1
  exact filter_congr fun v hv => by rw [h v hv]

/-- The saturated set only sees the roots of `Z`. -/
lemma satSet_congr {Z : Finset ι} {W W' : ι → Finset β} (h : ∀ v ∈ Z, W v = W' v) (q : ℕ) :
    satSet Z W q = satSet Z W' q := by
  unfold satSet
  rw [biUnion_congr rfl h]
  exact filter_congr fun x _ => by rw [auxCount_congr h]

/-- **Counter step**: if the new root only uses unsaturated vertices as auxiliaries, all
counters stay `≤ q`. -/
theorem auxCount_insert_le [DecidableEq ι] {Z : Finset ι} {a : ι} (ha : a ∉ Z) (W : ι → Finset β) {q : ℕ}
    (hq : 0 < q) (hcnt : ∀ x, auxCount Z W x ≤ q) (havoid : Disjoint (W a) (satSet Z W q))
    (x : β) : auxCount (insert a Z) W x ≤ q := by
  rw [auxCount_insert ha]
  split_ifs with h
  · have := lt_of_not_mem_satSet hq (disjoint_left.mp havoid h); omega
  · simpa using hcnt x

/-- **Ports by degree**: `x` is a port (`x ∈ N_X(v)`) of at most `deg_X(x)` roots. -/
theorem portCount_le [Fintype β] (X : SimpleGraph β) [DecidableRel X.Adj] (Z : Finset β)
    (x : β) : (Z.filter (fun v => x ∈ X.neighborFinset v)).card ≤ X.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_le_card fun v hv => ?_
  rw [mem_filter, SimpleGraph.mem_neighborFinset] at hv
  rw [SimpleGraph.mem_neighborFinset]
  exact hv.2.symm

/-- **Union degree**: per-root edge sets of degree `≤ c`, each supported on `T v`. -/
theorem edeg_biUnion_le (Z : Finset ι) (P : ι → Finset (Sym2 β)) (T : ι → Finset β) {c : ℕ}
    (hdeg : ∀ v ∈ Z, ∀ y, edeg (P v) y ≤ c) (hsupp : ∀ v ∈ Z, ∀ f ∈ P v, ∀ y ∈ f, y ∈ T v)
    (y : β) : edeg (Z.biUnion P) y ≤ c * (Z.filter (fun v => y ∈ T v)).card := by
  unfold edeg
  rw [filter_biUnion]
  refine (card_biUnion_le).trans ?_
  calc ∑ v ∈ Z, ((P v).filter (fun f => y ∈ f)).card
      = ∑ v ∈ Z.filter (fun v => y ∈ T v), ((P v).filter (fun f => y ∈ f)).card := by
        rw [sum_filter_of_ne]
        intro v hv hne
        by_contra hT
        obtain ⟨f, hf⟩ := card_ne_zero.mp hne
        rw [mem_filter] at hf
        exact hT (hsupp v hv f hf.1 y hf.2)
    _ ≤ ∑ _v ∈ Z.filter (fun v => y ∈ T v), c :=
        sum_le_sum fun v hv => hdeg v (mem_filter.mp hv).1 y
    _ = c * (Z.filter (fun v => y ∈ T v)).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Roots at which `y` is a port or an auxiliary: at most (ports) + (auxiliaries). -/
lemma filter_or_card_le [DecidableEq ι] (Z : Finset ι) (p p' : ι → Prop) [DecidablePred p] [DecidablePred p'] :
    (Z.filter (fun v => p v ∨ p' v)).card ≤ (Z.filter p).card + (Z.filter p').card := by
  rw [filter_or]; exact card_union_le _ _

/-- **Ceiling arithmetic of (7.1)**: if `4·A·z·r ≤ q·m` (e.g. `q = ⌈4Azr/m⌉`), then the
saturated-set bound `A·r·z / q` is at most `m / 4`. -/
theorem sat_budget_of_ceiling {A z r q m : ℕ} (hq : 0 < q) (h : 4 * A * z * r ≤ q * m) :
    A * r * z / q ≤ m / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  refine Nat.le_of_mul_le_mul_right ?_ hq
  have h1 : A * r * z / q * q ≤ A * r * z := Nat.div_mul_le_self _ _
  calc A * r * z / q * 4 * q = 4 * (A * r * z / q * q) := by ring
    _ ≤ 4 * (A * r * z) := Nat.mul_le_mul_left _ h1
    _ = 4 * A * z * r := by ring
    _ ≤ q * m := h
    _ = m * q := mul_comm _ _

end SelSimul
