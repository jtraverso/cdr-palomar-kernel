/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Assembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V47 §4 — the allocation in a child-shaped (protected) bank, with EARLY STOPPING

For any setting `S` with `ChildShape C0 R S` (in particular `protSetting … F0`) and its bank
`MacroBank S L N`:

* `shape_allocation_full` : the V46 branch (full monitor at the last step `J`), with the RELAXED
  final premise `1 + τ n² ≤ 2 ∑_{i ≤ J} m_i` and the same colour count `2Γ ≤ P`.
* `shape_allocation_local` : the EARLY-STOP branch: if the subgroup after the last step is zero,
  `K_{Zstrat (J+1)} = 0`, the localized monitors pay EVERY step, the last one exactly into `0`;
  only the localized bounds `‖ψ_{Zstrat(ℓ+1)} x‖₁ ≤ η n |Zstrat(ℓ+1)|` (`ℓ ≤ J`) are used, no
  `τ n²` term and no quadratic number of executed rounds.
* `shape_outcome_of_K_empty_bot` (§3) : `K_∅ = 0` (e.g. zero executed rounds).
* `shape_allocation_dichotomy` : **the proper dichotomy**, read off the bank itself.
  - If the final `K(Z_N) ≠ 0`: all `N` rounds are executed, `J = L`, and the quadratic full-monitor
    budget is paid (`hfull`, `hN : 1 + τ n² ≤ 2N` are only required in this case).
  - If the final `K(Z_N) = 0`: with `J + 1 = numStrata` the run is finished through the localized
    chain (the final zero subgroup is `K_{Zstrat (numStrata)}`, proved from the bank: the strata
    exhaust the executed rounds and the process stopped at `K = 0`), or `numStrata = 0`, in which
    case `K_∅ = 0` and the empty word works.
* `prot_avoids` : in the protected setting, the union of the stratum banks, the payload `Y` and the
  basal cover are all disjoint from `F0` (from the basal predicate of `S`).
-/

open Finset Classical Submodule

noncomputable section

namespace S07V47

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

variable {C0 : CoreCompression H lab F W d c E} {R : ℕ}
  {S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)} {L N : ℕ}

lemma Ks_anti : ∀ i j, i ≤ j → (KZ H lab F W (Zstrat S N j)).toAddSubgroup ≤
    (KZ H lab F W (Zstrat S N i)).toAddSubgroup :=
  fun _ _ hij _ hk => KZ_antitone H lab F W (Zstrat_mono hij) hk

lemma localized_to_prefix (hM : MacroBank S L N) {eta gamma : ℝ} (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (n : ℕ) (hqn : gamma * n ≤ S.q) (ℓ : ℕ) {b : ℝ}
    (hb : b ≤ eta * n * (Zstrat S N (ℓ + 1)).card) :
    b ≤ eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma *
      ∑ i ∈ range (ℓ + 1), (mStrat S N i : ℝ) := by
  refine hb.trans ?_
  have := local_scale (eta := eta) hγ hη (n := n) (q := S.q) (z := (Zstrat S N (ℓ + 1)).card)
    (c := 2 * S.E * S.Bstar) (S := ∑ i ∈ range (ℓ + 1), mStrat S N i) hqn
    (hM.prefix_bound (ℓ + 1))
  push_cast at this ⊢
  exact this

lemma hx0_of (hM : MacroBank S L N) {x : MCore H lab F W}
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅) :
    clsQ H lab F W (x : Sym2 V → ℤ) ∈ (KZ H lab F W (Zstrat S N 0)).toAddSubgroup := by
  rw [Zstrat_zero hM]; exact hx

/-- **branch with the full monitor at the last step, relaxed final premise** -/
theorem shape_allocation_full (hS : ChildShape C0 R S) (hM : MacroBank S L N) {J A M K : ℕ}
    (hJL : J ≤ L)
    (Pk : ∀ ℓ, ℓ < J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat S N j))
    {eta gamma tau : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma * n ≤ S.q) (hθ : eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (hP : 2 * gammaL A M L ≤ S.P)
    (hSJ : 1 + tau * n ^ 2 ≤ 2 * ∑ i ∈ range (J + 1), (mStrat S N i : ℝ))
    (x : MCore H lab F W) (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (hloc : ∀ ℓ (h : ℓ < J),
      (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi x) : ℝ) ≤
        eta * n * (Zstrat S N (ℓ + 1)).card)
    (hfull : (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2) :
    ShapeOutcome C0 R S N J x := by
  have hm0 : 1 ≤ mStrat S N 0 := by
    refine one_le_m0 hM (J := J) ?_
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ i ∈ range (J + 1), mStrat S N i = 0 := by omega
    have : (∑ i ∈ range (J + 1), (mStrat S N i : ℝ)) = 0 := by exact_mod_cast h0
    have hl0 : (0 : ℝ) ≤ (l1 (physMon C0 ∅ Fm.psi x) : ℝ) := by
      exact_mod_cast (sum_nonneg fun _ _ => abs_nonneg _ : (0 : ℤ) ≤ l1 (physMon C0 ∅ Fm.psi x))
    rw [this] at hSJ
    linarith
  have hθ0 : 0 ≤ eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma := by positivity
  set μ := pMonF C0 S N J Pk Fm
  have hcg0 : ∀ (D : Finset (Fin d → ℤ)) {K' : ℕ} (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K' → ℤ))
      (a b : MCore H lab F W), clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
      physMon C0 D psi a = physMon C0 D psi b := fun D _ psi a b hab => physMon_congr C0 D psi hab
  have hloc' : ∀ ℓ < J, μ ℓ (clsQ H lab F W (x : Sym2 V → ℤ)) ≤
      eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma * ∑ i ∈ range (ℓ + 1), (mStrat S N i : ℝ) := by
    intro ℓ h
    have : μ ℓ (clsQ H lab F W (x : Sym2 V → ℤ)) =
        (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi x) : ℝ) := by
      simp only [μ, pMonF, dif_pos h]; exact monQ_clsQ _ (hcg0 _ _) x
    rw [this]
    exact localized_to_prefix hM hγ hη n hqn ℓ (hloc ℓ h)
  have hfull' : μ J (clsQ H lab F W (x : Sym2 V → ℤ)) ≤ tau * n ^ 2 := by
    have : μ J (clsQ H lab F W (x : Sym2 V → ℤ)) = (l1 (physMon C0 ∅ Fm.psi x) : ℝ) := by
      simp only [μ, pMonF, dif_neg (lt_irrefl J)]; exact monQ_clsQ _ (hcg0 _ _) x
    rw [this]; exact hfull
  obtain ⟨z, hzs, hzm, hzx⟩ := strata_allocation_of_cap (P := S.P) Ks_anti
    (fun ℓ hℓ => pChain_le hℓ) pChain_succ (stepPay_full C0 S N J Pk Fm hgen)
    (mStrat S N) (clsQ H lab F W (x : Sym2 V → ℤ)) ⟨x, rfl⟩ (hx0_of hM hx)
    (fun a hrec => prefix_capacity_relaxed A M S.P L J hJL (mStrat S N) a _ hθ0 hθ hrec hloc'
      hfull' hP hm0 hSJ)
  exact shape_assembly hS hM J x z hzs hzm hzx

/-- **early-stop branch: localized monitors at every step, final subgroup zero** -/
theorem shape_allocation_local (hS : ChildShape C0 R S) (hM : MacroBank S L N) {J A M K : ℕ}
    (hJL : J ≤ L)
    (Pk : ∀ ℓ, ℓ ≤ J → PhysicalMonitors C0 R (Zstrat S N (ℓ + 1)) A M K)
    (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat S N j))
    (hfin : (KZ H lab F W (Zstrat S N (J + 1))).toAddSubgroup = ⊥)
    (hm0 : 1 ≤ mStrat S N 0)
    {eta gamma : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma * n ≤ S.q) (hθ : eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (hP : 2 * gammaL A M L ≤ S.P)
    (x : MCore H lab F W) (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (hloc : ∀ ℓ (h : ℓ ≤ J),
      (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi x) : ℝ) ≤
        eta * n * (Zstrat S N (ℓ + 1)).card) :
    ShapeOutcome C0 R S N J x := by
  have hθ0 : 0 ≤ eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma := by positivity
  set μ := pMonL C0 S N J Pk
  have hloc' : ∀ ℓ ≤ J, μ ℓ (clsQ H lab F W (x : Sym2 V → ℤ)) ≤
      eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma * ∑ i ∈ range (ℓ + 1), (mStrat S N i : ℝ) := by
    intro ℓ h
    have : μ ℓ (clsQ H lab F W (x : Sym2 V → ℤ)) =
        (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Pk ℓ h).psi x) : ℝ) := by
      simp only [μ, pMonL, dif_pos h]
      exact monQ_clsQ _ (fun a b hab => physMon_congr C0 _ _ hab) x
    rw [this]
    exact localized_to_prefix hM hγ hη n hqn ℓ (hloc ℓ h)
  obtain ⟨z, hzs, hzm, hzx⟩ := strata_allocation_of_cap (P := S.P) Ks_anti
    (fun ℓ hℓ => pChain_le hℓ) pChain_succ (stepPay_local C0 S N J Pk hgen hfin)
    (mStrat S N) (clsQ H lab F W (x : Sym2 V → ℤ)) ⟨x, rfl⟩ (hx0_of hM hx)
    (fun a hrec => prefix_capacity_local A M S.P L J hJL (mStrat S N) a _ hθ0 hθ hrec hloc' hP
      hm0)
  exact shape_assembly hS hM J x z hzs hzm hzx

/-! ### Bank facts for the dichotomy -/

/-- the strata exhaust the executed rounds: `preStrat (numStrata) = numRounds` -/
lemma preStrat_numStrata (hM : MacroBank S L N) : preStrat S N (numStrata S N) = numRounds S N := by
  rw [← hM.m_sum]
  unfold preStrat
  have hle := hM.numStrata_le
  refine sum_subset (range_subset_range.2 hle) fun j hj hjn => ?_
  simp only [mem_range, not_lt] at hjn
  by_contra h
  have := (hM.m_pos_iff j).1 (Nat.pos_of_ne_zero h)
  omega

/-- after an early stop, the subgroup of the final stratum set is zero -/
lemma K_Zstrat_numStrata_bot (hM : MacroBank S L N) (hK : S.K (Zr S N) = ⊥) :
    S.K (Zstrat S N (numStrata S N)) = ⊥ := by
  unfold Zstrat
  rw [preStrat_numStrata hM]
  rcases lt_or_eq_of_le (numRounds_le (S := S) N) with h | h
  · exact K_numRounds_eq_bot h
  · rw [h]; exact hK

/-- **THE DICHOTOMY (proved, not assumed).** -/
theorem shape_allocation_dichotomy (hS : ChildShape C0 R S) (hM : MacroBank S L N) {A M K : ℕ}
    (Mon : ∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
    (Fm : FullMonitor C0 R A M K) (hgen : ∀ j ≤ L, CatalogGen C0 R (Zstrat S N j))
    {eta gamma tau : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma * n ≤ S.q) (hθ : eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (hP : 2 * gammaL A M L ≤ S.P)
    (x : MCore H lab F W) (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (hloc : ∀ ℓ ≤ L, (ℓ < L ∨ S.K (Zr S N) = ⊥) →
      ∀ hg : CatalogGen C0 R (Zstrat S N (ℓ + 1)),
      (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Mon _ hg).psi x) : ℝ) ≤
        eta * n * (Zstrat S N (ℓ + 1)).card)
    (hfull : S.K (Zr S N) ≠ ⊥ → (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2)
    (hN : S.K (Zr S N) ≠ ⊥ → 1 + tau * n ^ 2 ≤ 2 * N) :
    ∃ J ≤ L, ShapeOutcome C0 R S N J x ∧ (S.K (Zr S N) ≠ ⊥ → J = L) ∧
      (S.K (Zr S N) = ⊥ → J + 1 = numStrata S N ∨ (numStrata S N = 0 ∧ J = 0)) := by
  by_cases hK : S.K (Zr S N) = ⊥
  · -- early stop: finish through the localized chain
    have hfinS := K_Zstrat_numStrata_bot hM hK
    have hfin := (hS.K_eq_bot_iff _).1 hfinS
    rcases Nat.eq_zero_or_pos (numStrata S N) with h0 | hpos
    · -- zero strata: `K_∅ = 0`
      rw [h0, Zstrat_zero hM] at hfin
      exact ⟨0, Nat.zero_le _, shape_outcome_of_K_empty_bot hS hM 0 x hx hfin,
        fun h => absurd hK h, fun _ => Or.inr ⟨h0, rfl⟩⟩
    · obtain ⟨J, hJ⟩ : ∃ J, numStrata S N = J + 1 := ⟨numStrata S N - 1, by omega⟩
      have hJL : J ≤ L := by have := hM.numStrata_le; omega
      have hm0 : 1 ≤ mStrat S N 0 := (hM.m_pos_iff 0).2 hpos
      rw [hJ] at hfin
      have hgenL : ∀ ℓ, ℓ ≤ J → CatalogGen C0 R (Zstrat S N (ℓ + 1)) := by
        intro ℓ hℓ
        rcases lt_or_eq_of_le hℓ with h | h
        · exact hgen (ℓ + 1) (by omega)
        · subst h; exact catalogGen_of_bot C0 R hfin
      refine ⟨J, hJL, shape_allocation_local hS hM hJL (fun ℓ h => Mon _ (hgenL ℓ h))
        (fun j hj => hgen j (by omega)) hfin hm0 n hγ hη hqn hθ hP x hx
        (fun ℓ h => hloc ℓ (by omega) (Or.inr hK) _), fun h => absurd hK h,
        fun _ => Or.inl hJ.symm⟩
  · -- the final subgroup is nonzero: all `N` rounds executed, full budget paid
    have hsum : ∑ j ∈ range (L + 1), mStrat S N j = N := hM.dichotomy.resolve_left hK
    have hSJ : 1 + tau * n ^ 2 ≤ 2 * ∑ i ∈ range (L + 1), (mStrat S N i : ℝ) := by
      have : (∑ i ∈ range (L + 1), (mStrat S N i : ℝ)) = N := by exact_mod_cast hsum
      rw [this]; exact hN hK
    refine ⟨L, le_rfl, shape_allocation_full hS hM le_rfl
      (fun ℓ h => Mon _ (hgen (ℓ + 1) (by omega))) Fm hgen n hγ hη hqn hθ hP hSJ x hx
      (fun ℓ h => hloc ℓ (by omega) (Or.inl h) _) (hfull hK), fun _ => rfl,
      fun h => absurd h hK⟩

/-- **avoidance of the protected edge set**: if the basal predicate of `S` forces disjointness from
`F0` (e.g. `S = protSetting … F0`), the union of the stratum banks, the payload and the cover are
disjoint from `F0` -/
theorem prot_avoids {J : ℕ} {x : MCore H lab F W} {F0 : Finset (Sym2 V)}
    (hF0 : ∀ X, S.basal X → Disjoint X F0)
    {z : ℕ → Fin S.P → Cat d R → ℤ} {hs : ∀ i, (stratBank S N i).Supplies (z i)}
    (h : ShapeProps C0 R S N J x z hs) :
    Disjoint ((range (J + 1)).biUnion fun i => (stratBank S N i).total) F0 ∧
      Disjoint ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) F0 ∧
      Disjoint ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) F0 := by
  obtain ⟨-, -, -, -, -, -, -, hpart, -, hbt, hbc, -, -⟩ := h
  have ht := hF0 _ hbt
  refine ⟨ht, ?_, hF0 _ hbc⟩
  rw [hpart] at ht
  exact disjoint_of_subset_left subset_union_right ht

end S07V47
