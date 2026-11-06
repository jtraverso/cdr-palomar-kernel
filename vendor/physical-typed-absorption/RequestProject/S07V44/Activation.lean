/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V44.Uniform
public import RequestProject.S07V43.NativeActivation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V44 §6 — coupling-free physical activation of the V44 payment word (V43 bank)

V43 `native_payment_activation` concluded `φ(y) + [1_{Y_J}] ∈ φ(H)` only for an ASSUMED coupling
`φ : Qt S →+ ClassQ`.  Here no coupling is used: the V44 word `z : Cat d R → ℤ` (from
`PhysicalMonitors.pay`) is placed in one colour `p0` (`wordIn p0 z`) and activated in a stratum
`j` of the actual V40 child bank (V43 `native_stratum_activation`).  The conclusion is the ACTUAL
class identity `[x] + [1_{Y_J}] ∈ K_Z` in `ClassQ`.

* `activate_payment_word` : any word `z` with `[x] + ∑ z v • gCat v ∈ K_Z`, supported on entries
  active in stratum `j`, of cost `≤ m_j`, is physically activated with
  `[1_{Y_J}] = ∑ z v • gCat v` and `[x] + [1_{Y_J}] ∈ K_Z`.
* `PhysicalMonitors.pay_activate` : the combination with the V44 payment, under the numeric
  premise `A (1 + ‖physMon x‖₁) ≤ m_j` (an explicit premise, not derived here).
-/

open Finset Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V44

open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V42 S07V40 S07V43 S07V34 S07V32

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- a catalog word placed in colour `p0` -/
def wordIn {R P : ℕ} (p0 : Fin P) (z : Cat d R → ℤ) : Fin P → Cat d R → ℤ :=
  fun p v => if p = p0 then z v else 0

lemma sum_wordIn_smul {R P : ℕ} {Q : Type*} [AddCommGroup Q] (p0 : Fin P) (z : Cat d R → ℤ)
    (g : Cat d R → Q) : ∑ p, ∑ v, wordIn p0 z p v • g v = ∑ v, z v • g v := by
  rw [sum_eq_single p0 (fun p _ hp => by simp [wordIn, hp]) (by simp)]
  simp [wordIn]

lemma cost_wordIn_le {R P : ℕ} (p0 : Fin P) (z : Cat d R → ℤ) (p : Fin P) :
    ∑ v, (wordIn p0 z p v).natAbs ≤ ∑ v, (z v).natAbs := by
  by_cases hp : p = p0
  · simp [wordIn, hp]
  · simp [wordIn, hp]

lemma total_cost_wordIn {R P : ℕ} (p0 : Fin P) (z : Cat d R → ℤ) :
    ∑ p, ∑ v, (wordIn p0 z p v).natAbs = ∑ v, (z v).natAbs := by
  rw [sum_eq_single p0 (fun p _ hp => by simp [wordIn, hp]) (by simp)]
  simp [wordIn]

lemma sum_natAbs_le_of_int {R : ℕ} (z : Cat d R → ℤ) {cost : ℕ}
    (h : ∑ v, |z v| ≤ (cost : ℤ)) : ∑ v, (z v).natAbs ≤ cost := by
  have : ((∑ v, (z v).natAbs : ℕ) : ℤ) = ∑ v, |z v| := by
    rw [Nat.cast_sum]; exact sum_congr rfl fun v _ => Int.natCast_natAbs _
  exact_mod_cast (this ▸ h)

/-- **coupling-free physical activation of a catalog word** -/
theorem activate_payment_word {R P q Ecell zmax L N : ℕ}
    {C0 : CoreCompression H lab F W d c E} (hM : MacroBank (childSetting C0 R P q Ecell zmax) L N)
    (j : ℕ) (p0 : Fin P) (Z : Finset V) (x : Sym2 V → ℤ) (z : Cat d R → ℤ)
    (hK : clsQ H lab F W x + ∑ v, z v • gCat C0 R v ∈ KZ H lab F W Z)
    (hact : ∀ v, z v ≠ 0 →
      gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N j))
    {cost : ℕ} (hcost : ∑ v, |z v| ≤ (cost : ℤ))
    (hm : cost ≤ mStrat (childSetting C0 R P q Ecell zmax) N j) :
    ∃ hs : (stratBank (childSetting C0 R P q Ecell zmax) N j).Supplies (wordIn p0 z),
      PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N j)
        (gCat C0 R) (wordIn p0 z) hs Ecell ∧
      chargeQ H lab F W (Bank.payload hs) = ∑ v, z v • gCat C0 R v ∧
      clsQ H lab F W x + chargeQ H lab F W (Bank.payload hs) ∈ KZ H lab F W Z ∧
      (Bank.payload hs).card ≤ Ecell * cost ∧
      Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N j) (Bank.payload hs) := by
  have hnat := sum_natAbs_le_of_int z hcost
  have hact' : ∀ p v, wordIn p0 z p v ≠ 0 →
      gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N j) := by
    intro p v hv
    refine hact v fun h0 => hv ?_
    simp [wordIn, h0]
  have hz : ∀ p, ∑ v, (wordIn p0 z p v).natAbs ≤
      mStrat (childSetting C0 R P q Ecell zmax) N j :=
    fun p => (cost_wordIn_le p0 z p).trans (hnat.trans hm)
  obtain ⟨hs, hPA, hav, -⟩ := native_stratum_activation hM j (wordIn p0 z) hact' hz
  have hch : chargeQ H lab F W (Bank.payload hs) = ∑ v, z v • gCat C0 R v := by
    rw [hPA.2.2.2.2.2.2.1, sum_wordIn_smul]
  refine ⟨hs, hPA, hch, by rw [hch]; exact hK, ?_, hav⟩
  refine hPA.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans (Nat.mul_le_mul_left _ ?_)
  rw [total_cost_wordIn]
  exact hnat

/-- **V44 payment + physical activation, coupling-free.**  The numeric premise
`A (1 + ‖physMon x‖₁) ≤ cost ≤ m_j` and the activity of the entries of `Cset` in stratum `j` are
explicit premises. -/
theorem PhysicalMonitors.pay_activate {R : ℕ} {Z : Finset V} {A M K : ℕ}
    {C0 : CoreCompression H lab F W d c E} (Pk : PhysicalMonitors C0 R Z A M K)
    {P q Ecell zmax L N : ℕ} (hM : MacroBank (childSetting C0 R P q Ecell zmax) L N) (j : ℕ)
    (p0 : Fin P) (Cset : Finset (Cat d R))
    (hact : ∀ v ∈ Cset,
      gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N j))
    (x : MCore H lab F W)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ AddSubgroup.closure (gCat C0 R '' (Cset : Set _)))
    {cost : ℕ} (hcost : (A : ℤ) * (1 + l1 (physMon C0 (Dset C0 R Z) Pk.psi x)) ≤ cost)
    (hm : cost ≤ mStrat (childSetting C0 R P q Ecell zmax) N j) :
    ∃ z : Cat d R → ℤ, (∀ v, v ∉ Cset → z v = 0) ∧ (∀ v, z v ≠ 0 → Realizable C0 v.1) ∧
      ∃ hs : (stratBank (childSetting C0 R P q Ecell zmax) N j).Supplies (wordIn p0 z),
        PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N j)
          (gCat C0 R) (wordIn p0 z) hs Ecell ∧
        chargeQ H lab F W (Bank.payload hs) = ∑ v, z v • gCat C0 R v ∧
        clsQ H lab F W (x : Sym2 V → ℤ) + chargeQ H lab F W (Bank.payload hs) ∈
          KZ H lab F W Z ∧
        (Bank.payload hs).card ≤ Ecell * cost ∧
        Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N j) (Bank.payload hs) := by
  obtain ⟨z, hz0, hzr, hzK, hzc⟩ := Pk.pay Cset x hx
  refine ⟨z, hz0, hzr, ?_⟩
  refine activate_payment_word hM j p0 Z _ z hzK (fun v hv => ?_) (hzc.trans hcost) hm
  by_contra hvC
  exact hv (hz0 v fun h => hvC (hact v h))

end S07V44
