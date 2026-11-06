/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V43.Residue
public import RequestProject.S07V43.Bridge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V43 §4 — the child-tagged native setting: V40's bank with payloads INSIDE the child

V42 `nativeSetting` uses the V40 `GoodCell`, which does not record that the charged part `Y` of
a cell lies in the child core (V42 `native_cell_supply` proves it but V40 cannot store it).
`childSetting` is the same native setting with the edge weight TAGGED by a non-child counter:

* `tagW e = ([1_e], if e ∈ childEdges H W then 0 else 1) ∈ Q × ℤ`, catalog `(gCat v, 0)`,
  `K Z = K_Z × 0`, basal = decomposable in `H`.
* `charge_tagW_eq_sgnQ_iff` : `charge tagW Y = ± (x, 0)` iff `[1_Y] = ± x` in `Q` AND
  `Y ⊆ childEdges H W`.  So every cell of the V40 bank of this setting has its payload in the
  child, and its first coordinate is the ACTUAL intrinsic class.
* `childSetting_supply` : V40 `CellSupply` from V42 `native_cell_supply` under exactly the inputs
  of V42 `nativeSetting_supply` (core compression, deleted compressions, terminal supplies for
  every small `Z`, and the two numeric premises).
* `childSetting_chainBound` : V40 `ChainBound` with bound `card Cat` (from V42
  `nativeSetting_chainBound`, `K` of the two settings changes at the same steps).
* `childSetting_macroBank` : the V40 global bank `MacroBank (childSetting …) (card Cat) N` from
  the same inputs plus `0 < q` and the cap `2 Ecell Bstar N ≤ q zmax`.
* `child_stratBank_valid` : the bank of any stratum is a valid occurrence bank for the PHYSICAL
  data (`physBasal`, `wQ`, `gCat`) and all its payloads lie in the child.
-/

open Finset Classical

noncomputable section

namespace S07V43

open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V42 S07V40

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

variable (H lab F W) in
/-- the tagged edge weight -/
def tagW (e : Sym2 V) : ClassQ H lab F W × ℤ :=
  (wQ H lab F W e, if e ∈ childEdges H W then 0 else 1)

/-- the child-tagged native V40 setting -/
def childSetting {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax : ℕ) :
    MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R) where
  w := tagW H lab F W
  g := fun v => (gCat C0 R v, 0)
  K := fun Z => (KZ H lab F W Z).toAddSubgroup.map (AddMonoidHom.inl _ _)
  basal := physBasal H lab F
  P := P
  q := q
  E := Ecell
  zmax := zmax

lemma charge_tagW (Y : Finset (Sym2 V)) :
    S07V40.charge (tagW H lab F W) Y =
      (chargeQ H lab F W Y, ∑ e ∈ Y, if e ∈ childEdges H W then (0 : ℤ) else 1) := by
  unfold S07V40.charge tagW chargeQ
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

omit [Fintype V] in
lemma sgnQ_pair (s : Bool) (x : ClassQ H lab F W) :
    sgnQ s ((x, 0) : ClassQ H lab F W × ℤ) = (sgnQ s x, 0) := by
  unfold sgnQ; split_ifs <;> simp

/-- **the tag forces the payload into the child** -/
theorem charge_tagW_eq_sgnQ_iff (Y : Finset (Sym2 V)) (s : Bool) (x : ClassQ H lab F W) :
    S07V40.charge (tagW H lab F W) Y = sgnQ s ((x, 0) : ClassQ H lab F W × ℤ) ↔
      chargeQ H lab F W Y = sgnQ s x ∧ Y ⊆ childEdges H W := by
  rw [charge_tagW, sgnQ_pair, Prod.mk.injEq]
  apply and_congr_right
  intro _
  rw [sum_eq_zero_iff_of_nonneg (fun e _ => by split_ifs <;> norm_num)]
  constructor
  · intro h e he
    by_contra hn
    have := h e he
    rw [if_neg hn] at this
    exact one_ne_zero this
  · intro h e he
    rw [if_pos (h he)]

lemma mem_inl_map_iff (K : AddSubgroup (ClassQ H lab F W)) (x : ClassQ H lab F W) :
    ((x, 0) : ClassQ H lab F W × ℤ) ∈ K.map (AddMonoidHom.inl _ _) ↔ x ∈ K := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := congrArg Prod.fst hyx
    exact this ▸ hy
  · intro h; exact ⟨x, h, rfl⟩

lemma childSetting_g_mem_K_iff {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) (v : Cat d R) (Z : Finset V) :
    (childSetting C0 R P q Ecell zmax).g v ∈ (childSetting C0 R P q Ecell zmax).K Z ↔
      gCat C0 R v ∈ KZ H lab F W Z :=
  mem_inl_map_iff _ _

lemma inl_map_injective :
    Function.Injective (fun K : AddSubgroup (ClassQ H lab F W) =>
      K.map (AddMonoidHom.inl (ClassQ H lab F W) ℤ)) := by
  intro K K' h
  ext x
  have := congrArg (fun L : AddSubgroup (ClassQ H lab F W × ℤ) => ((x, 0) : _ × ℤ) ∈ L) h
  simp only [mem_inl_map_iff] at this
  exact Iff.of_eq this

lemma childSetting_basal {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) : BasalInherit (childSetting C0 R P q Ecell zmax) :=
  physBasal_inherit H lab F

lemma edge_child_of_deleted {Z : Finset V} {e : Sym2 V} (he : e ∈ edges (indG H (W \ Z))) :
    e ∈ childEdges H W := by
  unfold childEdges edges at *
  simp only [mem_filter, mem_univ, true_and] at *
  exact SimpleGraph.edgeSet_mono (indG_mono H sdiff_subset) he

universe u v

/-- **V40 `CellSupply` for the child-tagged setting**, from V42 `native_cell_supply`, under the
same named inputs as V42 `nativeSetting_supply`.  Constants `t, Ecell, ε, n0` are fixed before
the host. -/
theorem childSetting_supply {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' s : ℕ) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) :
    ∃ (t Ecell : ℕ) (ε : ℝ), 0 < ε ∧ ∃ n0 : ℕ,
      ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
        {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → n0 ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ P q zmax : ℕ, (zmax : ℝ) ≤ coreDelta β h * W.card →
      ((q + (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * Ecell : ℕ) : ℝ) ≤
        ε * W.card →
      (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') →
      (∀ Z : Finset V, Z.card ≤ zmax → ∀ U : Finset V, U ⊆ W \ Z → U.card ≤ t →
        S07V31.TerminalSupply (S07V39.delG H Z) lab F U s ⌊β₁ * Fintype.card V⌋₊
          ⌊β₁ * Fintype.card V⌋₊) →
      CellSupply (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) := by
  obtain ⟨t, Ecell, ε, hε, n0, hsup⟩ := native_cell_supply.{u, v} h hβ d c E d' c' E' s hβ₁
  refine ⟨t, Ecell, ε, hε, n0, ?_⟩
  intro V _ I H lab F W hH3 hH4 hWc hWn C0 P q zmax hzmax hqB CZ hterm B Z hBdeg hZ l hl
  rw [childSetting_g_mem_K_iff] at hl
  obtain ⟨A, Y, hAY, hB', hZav, hYc, ⟨DA, hDA⟩, ⟨DAY, hDAY⟩, hcard, hch⟩ :=
    hsup hH3 hH4 hWc hWn C0 ((Nat.cast_le.2 hZ).trans hzmax) (CZ Z hZ) (hterm Z hZ) B
      (q + (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * Ecell)
      (fun x => hBdeg x) hqB l.2.1 hl l.1
  refine ⟨⟨A, Y⟩, hAY, ⟨DA, isDecomposition_of_delG hDA⟩, ⟨DAY, isDecomposition_of_delG hDAY⟩,
    hB', ?_, hcard, ?_⟩
  · intro e he z hz; exact hZav e he z hz
  · show S07V40.charge (tagW H lab F W) Y =
      sgnQ l.1 ((gCat C0 (catR β d c E d' c' E') l.2.1, 0) : ClassQ H lab F W × ℤ)
    rw [charge_tagW_eq_sgnQ_iff]
    refine ⟨?_, fun e he => edge_child_of_deleted (hYc e he)⟩
    rw [hch]; rfl

/-- **chain bound for the child-tagged setting** (same `K`-changes as V42 `nativeSetting`) -/
theorem childSetting_chainBound {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') :
    ChainBound (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax)
      (Fintype.card (Cat d (catR β d c E d' c' E'))) := by
  intro n Z hmono hsmall
  have := nativeSetting_chainBound hβ hH3 hH4 hW C0 P q Ecell zmax hzmax CZ n Z hmono hsmall
  refine le_of_eq_of_le ?_ this
  congr 1
  apply filter_congr
  intro i _
  exact not_congr ⟨fun h' => inl_map_injective h', fun h' => by
    show (KZ H lab F W (Z (i + 1))).toAddSubgroup.map _ =
      (KZ H lab F W (Z i)).toAddSubgroup.map _
    exact congrArg _ h'⟩

/-- **the V40 global bank exists for the child-tagged setting**, from the V42 inputs (core
compression, deleted compressions, terminal supplies), `0 < q`, the numeric premises and the cap.
All constants (`t, Ecell, ε, n0`) are fixed before the host; the chain bound is `card Cat`. -/
theorem childSetting_macroBank {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' s : ℕ) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) :
    ∃ (t Ecell : ℕ) (ε : ℝ), 0 < ε ∧ ∃ n0 : ℕ,
      ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
        {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → n0 ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ P q zmax N : ℕ, 0 < q → (zmax : ℝ) ≤ coreDelta β h * W.card →
      ((q + (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * Ecell : ℕ) : ℝ) ≤
        ε * W.card →
      2 * Ecell * (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar * N ≤
        q * zmax →
      (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') →
      (∀ Z : Finset V, Z.card ≤ zmax → ∀ U : Finset V, U ⊆ W \ Z → U.card ≤ t →
        S07V31.TerminalSupply (S07V39.delG H Z) lab F U s ⌊β₁ * Fintype.card V⌋₊
          ⌊β₁ * Fintype.card V⌋₊) →
      MacroBank (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax)
        (Fintype.card (Cat d (catR β d c E d' c' E'))) N := by
  obtain ⟨t, Ecell, ε, hε, n0, hsup⟩ := childSetting_supply.{u, v} h hβ d c E d' c' E' s hβ₁
  refine ⟨t, Ecell, ε, hε, n0, ?_⟩
  intro V _ I H lab F W hH3 hH4 hWc hWn C0 P q zmax N hq hzmax hqB hcap CZ hterm
  exact macro_bank hq (hsup hH3 hH4 hWc hWn C0 P q zmax hzmax hqB CZ hterm)
    (childSetting_basal C0 _ P q Ecell zmax)
    (childSetting_chainBound hβ hH3 hH4 hWc C0 P q Ecell zmax hzmax CZ) hcap

/-- **each stratum of the child-tagged V40 bank is a valid PHYSICAL occurrence bank** with all
payloads in the child -/
theorem child_stratBank_valid {d c E R P q Ecell zmax L N : ℕ}
    {C0 : CoreCompression H lab F W d c E}
    (hM : MacroBank (childSetting C0 R P q Ecell zmax) L N) (j : ℕ) :
    (stratBank (childSetting C0 R P q Ecell zmax) N j).Valid (physBasal H lab F)
        (wQ H lab F W) (gCat C0 R) ∧
      ∀ k, (stratBank (childSetting C0 R P q Ecell zmax) N j).Y k ⊆ childEdges H W := by
  have hv := stratBank_valid (j := j) hM
  have hch : ∀ k, chargeQ H lab F W ((stratBank (childSetting C0 R P q Ecell zmax) N j).Y k) =
      sgnQ ((stratBank (childSetting C0 R P q Ecell zmax) N j).sgn k)
        (gCat C0 R ((stratBank (childSetting C0 R P q Ecell zmax) N j).cat k)) ∧
      (stratBank (childSetting C0 R P q Ecell zmax) N j).Y k ⊆ childEdges H W :=
    fun k => (charge_tagW_eq_sgnQ_iff _ _ _).1 (hv.charge k)
  exact ⟨⟨hv.disj, hv.pw, hv.basalA, hv.basalT, fun k => (hch k).1⟩, fun k => (hch k).2⟩

end S07V43
