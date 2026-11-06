/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Supply
public import RequestProject.S07V40.Basic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §9 — connection to the V40 macro-round interface

* `nativeSetting`: the V40 `MacroSetting` with class group `Q = ClassQ H lab F W`, edge
  charges `wQ e = [1_e]`, the FIXED catalog `gCat C0 R` on `Cat d R`, `K Z = K_Z`
  (`KZ`), and basal predicate "has an allowed decomposition in the original `H`". The numbers
  `P, q, zmax` are free parameters (chosen by the local work); `E = Ecell`.
* `nativeSetting_basal`: `BasalInherit`.
* `nativeSetting_K_antitone`: `K` is antitone.
* `nativeSetting_catalog_small`: the catalog generates `K Z` for every `Z` with `|Z| ≤ zmax`
  (V40's `CatalogGenerates` quantifies over ALL `Z`; only small `Z` carry compression data).
* `nativeSetting_supply`: **`CellSupply` of V40 is discharged** for this setting from the
  native construction (`native_cell_supply`), under the named inputs (core compression, deleted
  compressions and terminal supplies for every small `Z`) and the numerical premises
  `zmax ≤ coreDelta β h |W|` and `q + Bstar · Ecell ≤ ε |W|`.
* `nativeSetting_chainBound`: from antitonicity and small-set catalog generation,
  `ChainBound S (card (Cat d R))` (each strict drop of `K` removes an active catalog entry).
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.Dispersal

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

/-- the V40 macro setting attached to the native catalog -/
def nativeSetting {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax : ℕ) :
    S07V40.MacroSetting V (ClassQ H lab F W) (Cat d R) where
  w := wQ H lab F W
  g := gCat C0 R
  K := fun Z => (KZ H lab F W Z).toAddSubgroup
  basal := fun X => ∃ D, IsDecomposition H lab F X D
  P := P
  q := q
  E := Ecell
  zmax := zmax

lemma nativeSetting_basal {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) : S07V40.BasalInherit (nativeSetting C0 R P q Ecell zmax) := by
  refine ⟨⟨∅, S07V28.isDecomposition_empty H lab F⟩, ?_⟩
  rintro X Y hXY ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
  exact ⟨D₁ ∪ D₂, S07V31.isDecomposition_union h₁ h₂ hXY⟩

lemma nativeSetting_K_antitone {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) {Z Z' : Finset V} (h : Z ⊆ Z') :
    (nativeSetting C0 R P q Ecell zmax).K Z' ≤ (nativeSetting C0 R P q Ecell zmax).K Z :=
  fun _ hk => KZ_antitone H lab F W h hk

lemma nativeSetting_charge {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) (Y : Finset (Sym2 V)) :
    S07V40.charge (nativeSetting C0 R P q Ecell zmax).w Y = chargeQ H lab F W Y := rfl

/-- **catalog generation for all small `Z`** -/
theorem nativeSetting_catalog_small {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E')
    (Z : Finset V) (hZ : Z.card ≤ zmax) :
    AddSubgroup.closure {x | ∃ v, (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).g v = x ∧
      (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).g v ∈
        (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).K Z} =
      (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).K Z :=
  catalog_generates hβ hH3 hH4 hW C0 ((Nat.cast_le.2 hZ).trans hzmax) (CZ Z hZ)

universe u v

/-- **V40 `CellSupply` discharged from the native construction.** The constants
`t, Ecell, ε, n0` are fixed before the host; `P, q, zmax` are free. -/
theorem nativeSetting_supply {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' s : ℕ) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) :
    ∃ (t Ecell : ℕ) (ε : ℝ), 0 < ε ∧ ∃ n0 : ℕ,
      ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
        {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → n0 ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ P q zmax : ℕ, (zmax : ℝ) ≤ coreDelta β h * W.card →
      ((q + (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * Ecell : ℕ) : ℝ) ≤
        ε * W.card →
      (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') →
      (∀ Z : Finset V, Z.card ≤ zmax → ∀ U : Finset V, U ⊆ W \ Z → U.card ≤ t →
        S07V31.TerminalSupply (S07V39.delG H Z) lab F U s ⌊β₁ * Fintype.card V⌋₊
          ⌊β₁ * Fintype.card V⌋₊) →
      S07V40.CellSupply (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax) := by
  obtain ⟨t, Ecell, ε, hε, n0, hsup⟩ := native_cell_supply.{u, v} h hβ d c E d' c' E' s hβ₁
  refine ⟨t, Ecell, ε, hε, n0, ?_⟩
  intro V _ I H lab F W hH3 hH4 hWc hWn C0 P q zmax hzmax hqB CZ hterm B Z hBdeg hZ l hl
  obtain ⟨A, Y, hAY, hB', hZav, -, ⟨DA, hDA⟩, ⟨DAY, hDAY⟩, hcard, hch⟩ :=
    hsup hH3 hH4 hWc hWn C0 ((Nat.cast_le.2 hZ).trans hzmax) (CZ Z hZ) (hterm Z hZ) B
      (q + (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * Ecell)
      (fun x => hBdeg x) hqB l.2.1 hl l.1
  refine ⟨⟨A, Y⟩, hAY, ⟨DA, isDecomposition_of_delG hDA⟩, ⟨DAY, isDecomposition_of_delG hDAY⟩,
    hB', ?_, hcard, ?_⟩
  · intro e he z hz; exact hZav e he z hz
  · show chargeQ H lab F W Y = S07V40.sgnQ l.1 (gCat C0 (catR β d c E d' c' E') l.2.1)
    rw [hch]; rfl

/-- **Chain bound from the native catalog**: along any monotone chain of small sets, the number
of strict changes of `K` is at most the catalog size. -/
theorem nativeSetting_chainBound {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') :
    S07V40.ChainBound (nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax)
      (Fintype.card (Cat d (catR β d c E d' c' E'))) := by
  set S := nativeSetting C0 (catR β d c E d' c' E') P q Ecell zmax with hS
  intro n Z hmono hsmall
  let act : ℕ → Finset (Cat d (catR β d c E d' c' E')) := fun i => univ.filter (fun v => S.g v ∈ S.K (Z i))
  have hgen : ∀ i ≤ n, AddSubgroup.closure {x | ∃ v, S.g v = x ∧ v ∈ act i} = S.K (Z i) := by
    intro i hi
    have := nativeSetting_catalog_small hβ hH3 hH4 hW C0 P q Ecell zmax hzmax CZ (Z i)
      (hsmall i hi)
    rw [← this]
    congr 1
    ext x
    simp only [act, hS, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : ∀ i, act (i + 1) ⊆ act i := by
    intro i v hv
    simp only [act, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact nativeSetting_K_antitone C0 _ P q Ecell zmax (hmono (Nat.le_succ i)) hv
  have key : ∀ m ≤ n, ((range m).filter (fun i => S.K (Z (i + 1)) ≠ S.K (Z i))).card +
      (act m).card ≤ (act 0).card := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih' := ih (Nat.le_of_succ_le hm)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hch : S.K (Z (m + 1)) ≠ S.K (Z m)
      · rw [if_pos hch, Finset.card_insert_of_notMem (by simp)]
        have hlt : (act (m + 1)).card < (act m).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.2 ⟨hsub m, fun heq => hch ?_⟩
          rw [← hgen (m + 1) hm, ← hgen m (Nat.le_of_succ_le hm), heq]
        omega
      · rw [if_neg hch]
        have := Finset.card_le_card (hsub m)
        omega
  have := key n le_rfl
  have h0 : (act 0).card ≤ Fintype.card (Cat d (catR β d c E d' c' E')) := Finset.card_le_univ _
  omega

end S07V42
