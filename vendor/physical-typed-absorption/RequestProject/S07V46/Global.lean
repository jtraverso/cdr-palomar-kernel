/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V46.StepPhys
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V46 §7 — GLOBAL CAPACITATED INTEGER ALLOCATION in the actual V40/V43 child bank

`global_capacitated_allocation` : for the actual bank `run (childSetting C0 R P q Ecell zmax) N`
(given its V40 invariants `MacroBank … L N`), a charge `x ∈ M(H[W])` with `[x] ∈ K_∅`, stratum
monitors `Pk ℓ` at the ACTUAL sets `Zstrat (ℓ+1)` (`ℓ < J`), a full monitor `Fm`, catalog generation
at `Zstrat j` (`j ≤ J`), and the numeric criterion

* `γ n ≤ q`, `θ := η (2 Ecell B*) / γ ≤ 1`, `2 Γ ≤ P` with `Γ = gammaL A M L`,
* `1 + τ n² ≤ ∑_{i ≤ J} m_i`,
* localized bounds `‖ψ_{Zstrat(ℓ+1)} x‖₁ ≤ η n |Zstrat(ℓ+1)|` (`ℓ < J`), full bound
  `‖ψ_full x‖₁ ≤ τ n²`,

there is an occurrence-indexed word `z i p v` (stratum `i`, colour `p`, catalog entry `v`) with
1. `z i p v ≠ 0 → i ≤ J ∧ gCat v ∈ K_{Zstrat i}` (selected only where active);
2. `|z i p v| ≤ m_i` (the exact per-(entry, sign, colour) count of stratum `i`);
3. the stratum banks supply `z i` and every `z i` is PHYSICALLY activated (V43
   `PhysicalActivation`), payloads avoiding `Zstrat i`; distinct strata use DISJOINT cells (no cell
   is reused);
4. `[x] + [1_Y] = 0` EXACTLY in `ClassQ` (torsion included), where `Y = ⋃_{i ≤ J} payload_i`, i.e.
   `x + 1_Y ∈ Λ(H[W])`;
5. the exact cover/payload partition `⋃ total_i = ⋃ cover_i ⊔ Y` with basal (decomposable) cover;
6. `|Y| ≤ Ecell · ∑ |z|`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V46

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

section bank

variable {Q C : Type*} [AddCommGroup Q] [Fintype C] {S : MacroSetting V Q C} {L N : ℕ}

/-- **distinct strata use disjoint cells** -/
theorem stratBank_total_disjoint (hM : MacroBank S L N) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (stratBank S N i).total (stratBank S N j).total := by
  unfold Bank.total
  rw [disjoint_biUnion_left]
  intro k _
  rw [disjoint_biUnion_right]
  intro k' _
  have hne : k.1 ≠ k'.1 := by
    intro h
    apply hij
    rw [← k.2, ← k'.2, h]
  have hpw := List.pairwise_iff_get.1 hM.disjoint
  rw [stratBank_tot, stratBank_tot]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hpw _ _ h
  · exact (hpw _ _ h).symm

lemma Zstrat_zero (hM : MacroBank S L N) : Zstrat S N 0 = ∅ := by
  unfold Zstrat preStrat; simpa using hM.zero

lemma Zstrat_mono {i j : ℕ} (hij : i ≤ j) : Zstrat S N i ⊆ Zstrat S N j := by
  unfold Zstrat
  refine Zr_mono ?_
  unfold preStrat
  exact sum_le_sum_of_subset (range_subset_range.2 hij)

/-- a positive prefix forces a nonempty first stratum -/
lemma one_le_m0 (hM : MacroBank S L N) {J : ℕ}
    (h : 1 ≤ ∑ i ∈ range (J + 1), mStrat S N i) : 1 ≤ mStrat S N 0 := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ range (J + 1), 0 < mStrat S N i := by
    by_contra hcon
    push_neg at hcon
    have : ∑ i ∈ range (J + 1), mStrat S N i = 0 :=
      sum_eq_zero fun i hi => Nat.le_zero.1 (hcon i hi)
    omega
  have h1 := (hM.m_pos_iff i).1 hi
  exact (hM.m_pos_iff 0).2 (by omega)

end bank

variable (C0 : CoreCompression H lab F W d c E)

/-- per-entry supply: the stratum bank has `m_i` occurrences of every active (sign, entry, colour) -/
lemma stratBank_supplies_entry {R P q Ecell zmax N i : ℕ} (z : Fin P → Cat d R → ℤ)
    (hact : ∀ p v, z p v ≠ 0 → gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N i))
    (hz : ∀ p v, (z p v).natAbs ≤ mStrat (childSetting C0 R P q Ecell zmax) N i) :
    (stratBank (childSetting C0 R P q Ecell zmax) N i).Supplies z := by
  intro p v
  by_cases h0 : z p v = 0
  · rw [h0]; simp
  · rw [stratBank_fiber_card]
    unfold Kstrat
    rw [if_pos ((childSetting_g_mem_K_iff C0 R P q Ecell zmax v _).2
      (hact p v h0))]
    exact hz p v

/-- **GLOBAL CAPACITATED INTEGER ALLOCATION in the actual child bank.** -/
theorem global_capacitated_allocation {R P q Ecell zmax L N A M K J : ℕ}
    (hM : MacroBank (childSetting C0 R P q Ecell zmax) L N) (hJL : J ≤ L)
    (Pk : ∀ ℓ, ℓ < J → PhysicalMonitors C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K)
    (hgen : ∀ j ≤ J, CatalogGen C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N j))
    {eta gamma tau : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta) (hτ : 0 ≤ tau)
    (hqn : gamma * n ≤ q)
    (hθ : eta * ((2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (hP : 2 * gammaL A M L ≤ P)
    (hSJ : 1 + tau * n ^ 2 ≤ ∑ i ∈ range (J + 1), (mStrat (childSetting C0 R P q Ecell zmax) N i : ℝ))
    (x : MCore H lab F W) (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (hloc : ∀ ℓ (h : ℓ < J),
      (l1 (physMon C0 (Dset C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1))) (Pk ℓ h).psi x) : ℝ) ≤
        eta * n * (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)).card)
    (hfull : (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2) :
    ∃ (z : ℕ → Fin P → Cat d R → ℤ) (hs : ∀ i, (stratBank (childSetting C0 R P q Ecell zmax) N i).Supplies (z i)),
      (∀ i p v, z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N i)) ∧
      (∀ i p v, (z i p v).natAbs ≤ mStrat (childSetting C0 R P q Ecell zmax) N i) ∧
      (∀ i, PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N i) (gCat C0 R) (z i) (hs i) Ecell) ∧
      (∀ i, Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N i) (Bank.payload (hs i))) ∧
      (∀ i j, i ≠ j → Disjoint (stratBank (childSetting C0 R P q Ecell zmax) N i).total (stratBank (childSetting C0 R P q Ecell zmax) N j).total) ∧
      clsQ H lab F W (x : Sym2 V → ℤ) +
        chargeQ H lab F W ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) = 0 ∧
      (x : Sym2 V → ℤ) + ind ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∈
        LamCore H lab F W ∧
      ((range (J + 1)).biUnion fun i => (stratBank (childSetting C0 R P q Ecell zmax) N i).total) =
        ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∪
          ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
      Disjoint ((range (J + 1)).biUnion fun i => Bank.cover (hs i))
        ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
      physBasal H lab F ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∧
      ((range (J + 1)).biUnion fun i => Bank.payload (hs i)).card ≤
        Ecell * ∑ i ∈ range (J + 1), ∑ p, ∑ v, (z i p v).natAbs := by
  -- the abstract allocation on the actual strata
  have hanti : ∀ i j, i ≤ j → (KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N j)).toAddSubgroup ≤
      (KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N i)).toAddSubgroup :=
    fun i j hij k hk => KZ_antitone H lab F W (Zstrat_mono hij) hk
  have hKc : ∀ ℓ ≤ J, stratChain C0 (R := R) (P := P) (q := q) (Ecell := Ecell) (zmax := zmax)
      N J ℓ = (KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N ℓ)).toAddSubgroup := fun ℓ hℓ => by
    unfold stratChain; rw [if_pos hℓ]
  have hbot : stratChain C0 (R := R) (P := P) (q := q) (Ecell := Ecell) (zmax := zmax)
      N J (J + 1) = ⊥ := by
    unfold stratChain; rw [if_neg (by omega)]
  have hn2 : (0 : ℝ) ≤ tau * n ^ 2 := by positivity
  have hm0 : 1 ≤ mStrat (childSetting C0 R P q Ecell zmax) N 0 := by
    refine one_le_m0 hM (J := J) ?_
    have : (1 : ℝ) ≤ ((∑ i ∈ range (J + 1), mStrat (childSetting C0 R P q Ecell zmax) N i : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hθ0 : 0 ≤ eta * ((2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma := by positivity
  have hx0 : clsQ H lab F W (x : Sym2 V → ℤ) ∈
      (KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N 0)).toAddSubgroup := by
    rw [Zstrat_zero hM]; exact hx
  have hloc' : ∀ ℓ < J, stratMon C0 N J Pk Fm ℓ (clsQ H lab F W (x : Sym2 V → ℤ)) ≤
      eta * ((2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma *
        ∑ i ∈ range (ℓ + 1), (mStrat (childSetting C0 R P q Ecell zmax) N i : ℝ) := by
    intro ℓ h
    have hcg : ∀ a b : MCore H lab F W,
        clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
        physMon C0 _ (Pk ℓ h).psi a = physMon C0 _ (Pk ℓ h).psi b :=
      fun a b hab => physMon_congr C0 _ _ hab
    unfold stratMon
    rw [dif_pos h, monQ_clsQ _ hcg]
    refine (hloc ℓ h).trans ?_
    have := local_scale (eta := eta) hγ hη (n := n) (q := q) (z := (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)).card)
      (c := 2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar) (S := ∑ i ∈ range (ℓ + 1), mStrat (childSetting C0 R P q Ecell zmax) N i) hqn
      (hM.prefix_bound (ℓ + 1))
    push_cast at this ⊢
    exact this
  have hfull' : stratMon C0 N J Pk Fm J (clsQ H lab F W (x : Sym2 V → ℤ)) ≤ tau * n ^ 2 := by
    have hcg : ∀ a b : MCore H lab F W,
        clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
        physMon C0 ∅ Fm.psi a = physMon C0 ∅ Fm.psi b :=
      fun a b hab => physMon_congr C0 _ _ hab
    unfold stratMon
    rw [dif_neg (lt_irrefl J), monQ_clsQ _ hcg]
    exact hfull
  obtain ⟨z, hzs, hzm, hzx⟩ := strata_allocation hJL hanti hKc hbot
    (stepPay_strata C0 N J Pk Fm hgen) (mStrat (childSetting C0 R P q Ecell zmax) N) hθ0 hθ hn2 hP hm0 hSJ
    (clsQ H lab F W (x : Sym2 V → ℤ)) ⟨x, rfl⟩ hx0 hloc' hfull'
  -- physical activation stratum by stratum
  have hs : ∀ i, (stratBank (childSetting C0 R P q Ecell zmax) N i).Supplies (z i) := fun i =>
    stratBank_supplies_entry C0 (z i) (fun p v h => (hzs i p v h).2) (hzm i)
  have hPA : ∀ i, PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N i) (gCat C0 R) (z i) (hs i)
      Ecell := fun i =>
    physical_activation (child_stratBank_valid hM i).1 (child_stratBank_valid hM i).2
      (fun k => (hM.cells _ (get_mem_run k)).1.2.2.2.1) (hs i)
  have htd : ∀ i j, i ≠ j → Disjoint (stratBank (childSetting C0 R P q Ecell zmax) N i).total (stratBank (childSetting C0 R P q Ecell zmax) N j).total :=
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
  refine ⟨z, hs, hzs, hzm, hPA, fun i => Bank.payload_avoids_of (hs i) (stratBank_avoids hM),
    htd, hzero, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact inherit_biUnion (physBasal_inherit H lab F)
      (f := fun i => Bank.cover (hs i)) (fun i => (hPA i).2.2.2.2.2.2.2.2.1) hcd _
  · refine card_biUnion_le.trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ := hPA i
    exact hcard

/-- **the last prefix of a still-active bank is the whole round count**: if the final `K` is
nonzero, `∑_{i ≤ L} m_i = N`, so `1 + τ n² ≤ N` gives the numeric premise `hSJ` with `J = L`. -/
lemma prefix_full_of_active {Q C : Type*} [AddCommGroup Q] [Fintype C] {S : MacroSetting V Q C}
    {L N : ℕ} (hM : MacroBank S L N) (hK : S.K (Zr S N) ≠ ⊥) {τ' : ℝ} (hN : 1 + τ' ≤ N) :
    1 + τ' ≤ ∑ i ∈ range (L + 1), (mStrat S N i : ℝ) := by
  have h := hM.dichotomy.resolve_left hK
  have : (∑ i ∈ range (L + 1), (mStrat S N i : ℝ)) = N := by exact_mod_cast h
  rw [this]; exact hN

end S07V46
