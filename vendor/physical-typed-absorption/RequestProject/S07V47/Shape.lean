/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V46.Uniform
public import RequestProject.S07V47.Criteria
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V47 §2 — the transparent child shape, the PROTECTED setting, and the step interfaces

V46 hard-codes `childSetting C0 R P q Ecell zmax`.  The protected bank of the local constructor has
the SAME edge weight `tagW`, catalog `(gCat, 0)`, subgroup map `Z ↦ K_Z × 0`, colours, threshold,
cell bound and smallness threshold, but a STRONGER basal predicate
`X ↦ (X decomposable in the original H) ∧ Disjoint X F0`.  Its run need not equal the unprotected
run, so nothing below assumes the two banks coincide.

* `ChildShape C0 R S` : transparent structure of explicit equalities `S.w = tagW`,
  `S.g = (gCat ·, 0)`, `S.K = (K_· × 0)`, plus `S.basal ⊆ physBasal` and inheritance of `S.basal`.
  No word/allocation provider is assumed.
* `protSetting C0 R P q Ecell zmax F0` : `childSetting` with the basal predicate replaced by
  `protBasal F0`; every other field is definitionally the `childSetting` field
  (`protSetting_w`, …, `protSetting_zmax` are `rfl`).  `protSetting_shape`, `childSetting_shape`.
* `protSetting_chainBound` : the V43 chain bound `card Cat` transfers verbatim (it only reads `K`
  and `zmax`).
* `catalogGen_of_bot` : at a zero subgroup `K_Z = 0`, catalog generation is automatic.
* `pChain`, `pMonF`, `pMonL` : the stratum chain and the step monitors for an ARBITRARY setting
  `S` (full monitor at the last step / localized monitors at every step).
* `stepPay_full`, `stepPay_local` : V46 `StepPay` for the actual strata of `S`; the localized
  version needs only that the final subgroup `K_{Zstrat (J+1)}` is zero (early stop).
-/

open Finset Classical Submodule

noncomputable section

namespace S07V47

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- **transparent child shape**: explicit equalities with the V43 child data, and a basal predicate
that may be STRONGER than decomposability (e.g. protection) but is still inherited -/
structure ChildShape (C0 : CoreCompression H lab F W d c E) (R : ℕ)
    (S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)) : Prop where
  w_eq : S.w = tagW H lab F W
  g_eq : S.g = fun v => (gCat C0 R v, 0)
  K_eq : S.K = fun Z => (KZ H lab F W Z).toAddSubgroup.map (AddMonoidHom.inl _ _)
  basal_phys : ∀ X, S.basal X → physBasal H lab F X
  basal_inherit : Inherit S.basal

variable (H lab F) in
/-- the protected basal predicate: decomposable in the ORIGINAL host and disjoint from `F0` -/
def protBasal (F0 : Finset (Sym2 V)) (X : Finset (Sym2 V)) : Prop :=
  physBasal H lab F X ∧ Disjoint X F0

omit [Fintype V] in
lemma protBasal_inherit (F0 : Finset (Sym2 V)) : Inherit (protBasal H lab F F0) := by
  refine ⟨⟨(physBasal_inherit H lab F).1, disjoint_empty_left _⟩, ?_⟩
  rintro X Y hXY ⟨hX, hX0⟩ ⟨hY, hY0⟩
  exact ⟨(physBasal_inherit H lab F).2 X Y hXY hX hY, disjoint_union_left.2 ⟨hX0, hY0⟩⟩

/-- **the protected child setting**: `childSetting` with basal `protBasal F0`, all other fields
unchanged -/
def protSetting (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax : ℕ)
    (F0 : Finset (Sym2 V)) : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R) :=
  { childSetting C0 R P q Ecell zmax with basal := protBasal H lab F F0 }

section fields

variable (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax : ℕ) (F0 : Finset (Sym2 V))

lemma protSetting_w : (protSetting C0 R P q Ecell zmax F0).w = (childSetting C0 R P q Ecell zmax).w := rfl
lemma protSetting_g : (protSetting C0 R P q Ecell zmax F0).g = (childSetting C0 R P q Ecell zmax).g := rfl
lemma protSetting_K : (protSetting C0 R P q Ecell zmax F0).K = (childSetting C0 R P q Ecell zmax).K := rfl
lemma protSetting_P : (protSetting C0 R P q Ecell zmax F0).P = (childSetting C0 R P q Ecell zmax).P := rfl
lemma protSetting_q : (protSetting C0 R P q Ecell zmax F0).q = (childSetting C0 R P q Ecell zmax).q := rfl
lemma protSetting_E : (protSetting C0 R P q Ecell zmax F0).E = (childSetting C0 R P q Ecell zmax).E := rfl
lemma protSetting_zmax :
    (protSetting C0 R P q Ecell zmax F0).zmax = (childSetting C0 R P q Ecell zmax).zmax := rfl
lemma protSetting_Bstar :
    (protSetting C0 R P q Ecell zmax F0).Bstar = (childSetting C0 R P q Ecell zmax).Bstar := rfl
lemma protSetting_basal (X : Finset (Sym2 V)) :
    (protSetting C0 R P q Ecell zmax F0).basal X ↔ physBasal H lab F X ∧ Disjoint X F0 := Iff.rfl

theorem childSetting_shape : ChildShape C0 R (childSetting C0 R P q Ecell zmax) :=
  ⟨rfl, rfl, rfl, fun _ h => h, physBasal_inherit H lab F⟩

theorem protSetting_shape : ChildShape C0 R (protSetting C0 R P q Ecell zmax F0) :=
  ⟨rfl, rfl, rfl, fun _ h => h.1, protBasal_inherit F0⟩

end fields

/-- **the chain bound of the protected setting** is the V43 one (`card Cat`): it reads only `K` and
`zmax`, which are the `childSetting` fields -/
theorem protSetting_chainBound {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E')
    (F0 : Finset (Sym2 V)) :
    ChainBound (protSetting C0 (catR β d c E d' c' E') P q Ecell zmax F0)
      (Fintype.card (Cat d (catR β d c E d' c' E'))) :=
  childSetting_chainBound hβ hH3 hH4 hW C0 P q Ecell zmax hzmax CZ

section shape

variable {C0 : CoreCompression H lab F W d c E} {R : ℕ}
  {S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)}

lemma ChildShape.g_mem_K_iff (hS : ChildShape C0 R S) (v : Cat d R) (Z : Finset V) :
    S.g v ∈ S.K Z ↔ gCat C0 R v ∈ KZ H lab F W Z := by
  rw [hS.g_eq, hS.K_eq]; exact mem_inl_map_iff _ _

lemma ChildShape.K_eq_bot_iff (hS : ChildShape C0 R S) (Z : Finset V) :
    S.K Z = ⊥ ↔ (KZ H lab F W Z).toAddSubgroup = ⊥ := by
  rw [hS.K_eq]
  constructor
  · intro h
    apply inl_map_injective
    simp only at h ⊢
    rw [h, AddSubgroup.map_bot]
  · intro h; simp only; rw [h, AddSubgroup.map_bot]

end shape

/-- at a zero subgroup, catalog generation is automatic -/
lemma catalogGen_of_bot (C0 : CoreCompression H lab F W d c E) (R : ℕ) {Z : Finset V}
    (h : (KZ H lab F W Z).toAddSubgroup = ⊥) : CatalogGen C0 R Z := by
  unfold CatalogGen
  rw [h, eq_bot_iff, AddSubgroup.closure_le]
  rintro k ⟨v, rfl, hv⟩
  have : gCat C0 R v ∈ (KZ H lab F W Z).toAddSubgroup := hv
  rw [h] at this; exact this

section chain

variable {Q' C' : Type*} [AddCommGroup Q'] [Fintype C']

variable (H lab F W) in
/-- the stratum chain of an arbitrary setting: `K_{Zstrat ℓ}` for `ℓ ≤ J`, then `⊥` -/
def pChain (S : MacroSetting V Q' C') (N J ℓ : ℕ) : AddSubgroup (ClassQ H lab F W) :=
  if ℓ ≤ J then (KZ H lab F W (Zstrat S N ℓ)).toAddSubgroup else ⊥

/-- step monitors with the FULL monitor at the last step -/
def pMonF (C0 : CoreCompression H lab F W d c E) {R A M K : ℕ} (S : MacroSetting V Q' C')
    (N J : ℕ) (Pk : ∀ ℓ, ℓ < J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (ℓ : ℕ) (y : ClassQ H lab F W) : ℝ :=
  if h : ℓ < J then monQ (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi) y
  else monQ (physMon C0 ∅ Fm.psi) y

/-- step monitors LOCALIZED at every step (early stop) -/
def pMonL (C0 : CoreCompression H lab F W d c E) {R A M K : ℕ} (S : MacroSetting V Q' C')
    (N J : ℕ) (Pk : ∀ ℓ, ℓ ≤ J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (ℓ : ℕ) (y : ClassQ H lab F W) : ℝ :=
  if h : ℓ ≤ J then monQ (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi) y else 0

variable (C0 : CoreCompression H lab F W d c E)

lemma pChain_le {S : MacroSetting V Q' C'} {N J ℓ : ℕ} (hℓ : ℓ ≤ J) :
    pChain H lab F W S N J ℓ = (KZ H lab F W (Zstrat S N ℓ)).toAddSubgroup := by
  unfold pChain; rw [if_pos hℓ]

lemma pChain_succ {S : MacroSetting V Q' C'} {N J : ℕ} : pChain H lab F W S N J (J + 1) = ⊥ := by
  unfold pChain; rw [if_neg (by omega)]

/-- the catalog support condition shared by both step interfaces -/
lemma active_support {R : ℕ} {S : MacroSetting V Q' C'} {N J ℓ : ℕ} (hℓ : ℓ ≤ J)
    (z : Cat d R → ℤ)
    (hz0 : ∀ v, v ∉ (univ.filter fun v => gCat C0 R v ∈ KZ H lab F W (Zstrat S N ℓ)) → z v = 0) :
    ∀ v, z v ≠ 0 → gCat C0 R v ∈ pChain H lab F W S N J ℓ := by
  intro v hv
  have hvC : v ∈ (univ.filter fun v => gCat C0 R v ∈ KZ H lab F W (Zstrat S N ℓ)) := by
    by_contra h; exact hv (hz0 v h)
  rw [pChain_le hℓ]
  exact (mem_filter.1 hvC).2

/-- **step interface, full monitor at the last step** (V46 `stepPay_strata`, any setting) -/
theorem stepPay_full {R A M K : ℕ} (S : MacroSetting V Q' C') (N J : ℕ)
    (Pk : ∀ ℓ, ℓ < J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat S N j)) :
    StepPay (gCat C0 R) (clsCore H lab F W).range (pChain H lab F W S N J)
      (pMonF C0 S N J Pk Fm) A M J := by
  refine ⟨gCat_mem_range C0, ?_, ?_⟩
  · intro ℓ hℓ y hy hyK
    obtain ⟨x, rfl⟩ := hy
    rw [clsCore_apply] at hyK ⊢
    rw [pChain_le hℓ] at hyK
    have hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R ''
        ((univ.filter fun v => gCat C0 R v ∈ KZ H lab F W (Zstrat S N ℓ) : Finset _) : Set _)) := by
      rw [closure_active_eq C0 (hgen ℓ hℓ)]; exact hyK
    by_cases hlt : ℓ < J
    · obtain ⟨z, hz0, -, hzK, hzc⟩ := (Pk ℓ hlt).pay _ x hx
      refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
      · rw [pChain_le (by omega)]; exact hzK
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 _ (Pk ℓ hlt).psi a = physMon C0 _ (Pk ℓ hlt).psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold pMonF
        rw [dif_pos hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ) ≤
            (((A : ℤ) * (1 + l1 (physMon C0 _ (Pk ℓ hlt).psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
    · obtain ⟨z, hz0, -, hz0', hzc⟩ := Fm.pay _ x hx
      refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
      · unfold pChain; rw [if_neg (by omega)]
        exact (AddSubgroup.mem_bot).2 hz0'
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 ∅ Fm.psi a = physMon C0 ∅ Fm.psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold pMonF
        rw [dif_neg hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ) ≤
            (((A : ℤ) * (1 + l1 (physMon C0 ∅ Fm.psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
  · intro ℓ _ y hy u
    unfold pMonF
    by_cases hlt : ℓ < J
    · simp only [dif_pos hlt]
      exact monQ_word_le C0 _ _ (Pk ℓ hlt).box_le y hy u
    · simp only [dif_neg hlt]
      exact monQ_word_le C0 _ _ Fm.box_le y hy u

/-- **step interface, localized monitors at EVERY step** (early stop: the final subgroup
`K_{Zstrat (J+1)}` is zero, so the localized payment at step `J` is already exact) -/
theorem stepPay_local {R A M K : ℕ} (S : MacroSetting V Q' C') (N J : ℕ)
    (Pk : ∀ ℓ, ℓ ≤ J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat S N j))
    (hfin : (KZ H lab F W (Zstrat S N (J + 1))).toAddSubgroup = ⊥) :
    StepPay (gCat C0 R) (clsCore H lab F W).range (pChain H lab F W S N J)
      (pMonL C0 S N J Pk) A M J := by
  refine ⟨gCat_mem_range C0, ?_, ?_⟩
  · intro ℓ hℓ y hy hyK
    obtain ⟨x, rfl⟩ := hy
    rw [clsCore_apply] at hyK ⊢
    rw [pChain_le hℓ] at hyK
    have hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R ''
        ((univ.filter fun v => gCat C0 R v ∈ KZ H lab F W (Zstrat S N ℓ) : Finset _) : Set _)) := by
      rw [closure_active_eq C0 (hgen ℓ hℓ)]; exact hyK
    obtain ⟨z, hz0, -, hzK, hzc⟩ := (Pk ℓ hℓ).pay _ x hx
    refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
    · by_cases hlt : ℓ < J
      · rw [pChain_le (by omega)]; exact hzK
      · have hJ : ℓ = J := by omega
        subst hJ
        rw [pChain_succ]
        have h' : clsQ H lab F W (x : Sym2 V → ℤ) + ∑ v, z v • gCat C0 R v ∈
            (KZ H lab F W (Zstrat S N (ℓ + 1))).toAddSubgroup := hzK
        rw [hfin] at h'
        exact h'
    · have hcg : ∀ a b : MCore H lab F W,
          clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
          physMon C0 _ (Pk ℓ hℓ).psi a = physMon C0 _ (Pk ℓ hℓ).psi b :=
        fun a b h => physMon_congr C0 _ _ h
      unfold pMonL
      rw [dif_pos hℓ, monQ_clsQ _ hcg]
      have : ((wcost z : ℤ) : ℝ) ≤
          (((A : ℤ) * (1 + l1 (physMon C0 _ (Pk ℓ hℓ).psi x)) : ℤ) : ℝ) := by
        rw [wcost_cast]; exact_mod_cast hzc
      push_cast at this ⊢
      exact this
  · intro ℓ hℓ y hy u
    unfold pMonL
    simp only [dif_pos hℓ]
    exact monQ_word_le C0 _ _ (Pk ℓ hℓ).box_le y hy u

end chain

end S07V47
