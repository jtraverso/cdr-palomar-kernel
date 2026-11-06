/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V46.FullMonitor
public import RequestProject.S07V46.Alloc
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V46 §6 — the one-step payment interface on the ACTUAL strata of the V40/V43 child bank

Instantiation of the abstract `StepPay` (§2) with:
* `Q = ClassQ H lab F W`, `g = gCat C0 R` (the fixed catalog), `G = range clsCore` (classes of
  actual core profiles: every class met in the chain is represented by an actual `MCore` vector);
* the chain `stratChain S N J ℓ = K_{Zstrat ℓ}` for `ℓ ≤ J` and `⊥` at `J+1` (EXACT cancellation);
* the step monitors `stratMon`: step `ℓ < J` uses the V44 `PhysicalMonitors` of the ACTUAL set
  `Zstrat (ℓ+1)` (localized), the last step `J` uses the `FullMonitor` (§5).

`monQ f y` is the `ℓ¹` monitor of the class `y` through any actual preimage (`monQ_clsQ`: it equals
`‖f x‖₁` for `y = [x]` because `f` depends only on the class).

* `closure_active_eq` : `CatalogGen` ⇒ the active catalog of `Z` generates exactly `K_Z`.
* `monQ_word_le` : Lipschitz growth `monQ (y + [u]) ≤ monQ y + M · |u|` on `G`.
* `stepPay_strata` : `StepPay (gCat C0 R) (range clsCore) (stratChain …) (stratMon …) A M J`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V46

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- the monitor of a class through an actual core preimage (`0` if none) -/
def monQ {K : ℕ} (f : MCore H lab F W →+ (Fin K → ℤ)) (y : ClassQ H lab F W) : ℝ :=
  if h : ∃ x : MCore H lab F W, clsQ H lab F W (x : Sym2 V → ℤ) = y then (l1 (f h.choose) : ℝ)
  else 0

lemma monQ_clsQ {K : ℕ} (f : MCore H lab F W →+ (Fin K → ℤ))
    (hf : ∀ x y : MCore H lab F W,
      clsQ H lab F W (x : Sym2 V → ℤ) = clsQ H lab F W (y : Sym2 V → ℤ) → f x = f y)
    (x : MCore H lab F W) : monQ f (clsQ H lab F W (x : Sym2 V → ℤ)) = (l1 (f x) : ℝ) := by
  have h : ∃ x' : MCore H lab F W, clsQ H lab F W (x' : Sym2 V → ℤ) =
      clsQ H lab F W (x : Sym2 V → ℤ) := ⟨x, rfl⟩
  unfold monQ
  rw [dif_pos h, hf _ _ h.choose_spec]

lemma wcost_cast {C : Type*} [Fintype C] (u : C → ℤ) : ((wcost u : ℕ) : ℤ) = ∑ v, |u v| := by
  simp [wcost]

variable (C0 : CoreCompression H lab F W d c E)

/-- the class of a catalog word is the class of an actual core vector -/
lemma wcls_gCat {R : ℕ} (x : MCore H lab F W) (u : Cat d R → ℤ) :
    clsQ H lab F W (x : Sym2 V → ℤ) + wcls (gCat C0 R) u =
      clsQ H lab F W ((x + ∑ v, u v • realRep C0 v.1 : MCore H lab F W) : Sym2 V → ℤ) := by
  change _ = clsCore H lab F W (x + ∑ v, u v • realRep C0 v.1)
  rw [map_add, map_sum, clsCore_apply]
  congr 1
  unfold wcls
  refine sum_congr rfl fun v _ => ?_
  rw [map_zsmul, clsCore_apply, gCat_eq_clsQ_realRep C0 v]

lemma realRep_q_le {R : ℕ} (v : Cat d R) (j : Fin d) :
    |C0.q (realRep C0 v.1) j| ≤ monR R E := by
  by_cases h : Realizable C0 v.1
  · rw [q_realRep C0 h]
    exact ((mem_box.1 v.2) j).trans (by exact_mod_cast R_le_monR R E)
  · unfold realRep; rw [dif_neg h]; simp

/-- every catalog charge is the class of an actual core vector -/
lemma gCat_mem_range {R : ℕ} (v : Cat d R) : gCat C0 R v ∈ (clsCore H lab F W).range :=
  ⟨realRep C0 v.1, by rw [clsCore_apply, gCat_eq_clsQ_realRep C0 v]⟩

/-- **Lipschitz growth of a physical monitor under catalog words** -/
theorem monQ_word_le {R K M : ℕ} (D : Finset (Fin d → ℤ))
    (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K → ℤ))
    (hM : ∀ b ∈ box d (monR R E), l1 (psi ((qmk C0.S b : Qt C0.S) : Qt C0.S ⧸ Hgrp C0.S D)) ≤ M)
    (y : ClassQ H lab F W) (hy : y ∈ (clsCore H lab F W).range) (u : Cat d R → ℤ) :
    monQ (physMon C0 D psi) (y + wcls (gCat C0 R) u) ≤
      monQ (physMon C0 D psi) y + M * wcost u := by
  obtain ⟨x, rfl⟩ := hy
  have hcg : ∀ a b : MCore H lab F W,
      clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
      physMon C0 D psi a = physMon C0 D psi b := fun a b h => physMon_congr C0 D psi h
  rw [clsCore_apply, wcls_gCat, monQ_clsQ _ hcg, monQ_clsQ _ hcg]
  have hl0 : 0 ≤ l1 (physMon C0 D psi x) := sum_nonneg fun _ _ => abs_nonneg _
  have hw := physMon_word_le C0 D psi hM univ x (fun v => realRep C0 v.1) u
    (fun v _ j => realRep_q_le C0 v j) (Eb := (l1 (physMon C0 D psi x)).toNat)
    (S' := wcost u) (by rw [Int.toNat_of_nonneg hl0]) (by rw [wcost_cast])
  rw [Int.toNat_of_nonneg hl0] at hw
  exact_mod_cast hw

/-- the stratum chain: `K_{Zstrat ℓ}` for `ℓ ≤ J`, then `⊥` -/
def stratChain {R P q Ecell zmax : ℕ} (N J : ℕ) (ℓ : ℕ) : AddSubgroup (ClassQ H lab F W) :=
  if ℓ ≤ J then (KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N ℓ)).toAddSubgroup
  else ⊥

/-- the step monitors: localized at `Zstrat (ℓ+1)` for `ℓ < J`, full at `ℓ = J` -/
def stratMon {R P q Ecell zmax A M K : ℕ} (N J : ℕ)
    (Pk : ∀ ℓ, ℓ < J →
      PhysicalMonitors C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (ℓ : ℕ) (y : ClassQ H lab F W) : ℝ :=
  if h : ℓ < J then
    monQ (physMon C0 (Dset C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)))
      (Pk ℓ h).psi) y
  else monQ (physMon C0 ∅ Fm.psi) y

/-- under `CatalogGen`, the active catalog of `Z` generates exactly `K_Z` -/
lemma closure_active_eq {R : ℕ} {Z : Finset V} (hgen : CatalogGen C0 R Z) :
    AddSubgroup.closure (gCat C0 R '' ((univ.filter fun v => gCat C0 R v ∈ KZ H lab F W Z :
      Finset (Cat d R)) : Set (Cat d R))) = (KZ H lab F W Z).toAddSubgroup := by
  rw [← hgen]
  congr 1
  ext k
  simp only [coe_filter, mem_univ, true_and, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩; exact ⟨v, hv, rfl⟩

/-- **the one-step payment interface on the actual strata** -/
theorem stepPay_strata {R P q Ecell zmax A M K : ℕ} (N J : ℕ)
    (Pk : ∀ ℓ, ℓ < J →
      PhysicalMonitors C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K)
    (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N j)) :
    StepPay (gCat C0 R) (clsCore H lab F W).range
      (stratChain C0 (R := R) (P := P) (q := q) (Ecell := Ecell) (zmax := zmax) N J)
      (stratMon C0 N J Pk Fm) A M J := by
  refine ⟨gCat_mem_range C0, ?_, ?_⟩
  · intro ℓ hℓ y hy hyK
    obtain ⟨x, rfl⟩ := hy
    rw [clsCore_apply] at hyK ⊢
    have hyK' : clsQ H lab F W (x : Sym2 V → ℤ) ∈
        KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N ℓ) := by
      unfold stratChain at hyK; rw [if_pos hℓ] at hyK; exact hyK
    set Cset : Finset (Cat d R) := univ.filter fun v =>
      gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N ℓ) with hC
    have hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R '' (Cset : Set _)) := by
      rw [hC, closure_active_eq C0 (hgen ℓ hℓ)]; exact hyK'
    have hsupp : ∀ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) →
        ∀ v, z v ≠ 0 → gCat C0 R v ∈ stratChain C0 (R := R) (P := P) (q := q) (Ecell := Ecell)
          (zmax := zmax) N J ℓ := by
      intro z hz0 v hv
      have hvC : v ∈ Cset := by by_contra h; exact hv (hz0 v h)
      unfold stratChain; rw [if_pos hℓ]
      exact (mem_filter.1 hvC).2
    by_cases hlt : ℓ < J
    · obtain ⟨z, hz0, -, hzK, hzc⟩ := (Pk ℓ hlt).pay Cset x hx
      refine ⟨z, hsupp z hz0, ?_, ?_⟩
      · unfold stratChain; rw [if_pos (by omega)]; exact hzK
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 _ (Pk ℓ hlt).psi a = physMon C0 _ (Pk ℓ hlt).psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold stratMon
        rw [dif_pos hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ) ≤
            (((A : ℤ) * (1 + l1 (physMon C0 _ (Pk ℓ hlt).psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
    · have hJ : ℓ = J := by omega
      obtain ⟨z, hz0, -, hz0', hzc⟩ := Fm.pay Cset x hx
      refine ⟨z, hsupp z hz0, ?_, ?_⟩
      · unfold stratChain; rw [if_neg (by omega)]
        exact (AddSubgroup.mem_bot).2 hz0'
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 ∅ Fm.psi a = physMon C0 ∅ Fm.psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold stratMon
        rw [dif_neg hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ) ≤
            (((A : ℤ) * (1 + l1 (physMon C0 ∅ Fm.psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
  · intro ℓ _ y hy u
    unfold stratMon
    by_cases hlt : ℓ < J
    · simp only [dif_pos hlt]
      exact monQ_word_le C0 _ _ (Pk ℓ hlt).box_le y hy u
    · simp only [dif_neg hlt]
      exact monQ_word_le C0 _ _ Fm.box_le y hy u

end S07V46
