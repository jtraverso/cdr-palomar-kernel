/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V43.ChildSetting
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V43 §5 — physical activation in a stratum of the ACTUAL V40 bank

`native_stratum_activation` : for the actual V40 bank `run (childSetting …) N` (given its
invariants `MacroBank`), every integer word `z : Fin P → Cat d R → ℤ`

* supported on catalog entries active in stratum `j` (`gCat c ∈ K_{Zstrat j}`), and
* of colour cost `∑_c |z p c| ≤ m_j` (the exact per-label count of the stratum, V40
  `countP_stratum`),

is supplied by the stratum bank (occurrences = list positions), and its selection satisfies
`PhysicalActivation` (items 1–5 of §2) with the cell bound `Ecell`, in the ACTUAL intrinsic
quotient `Q = (Sym2 V → ℤ) ⧸ Λ(H[W])`.  In addition the payload and the cover avoid the initial
saturated set `Zstrat j` of the stratum, lie in the used edges `Br N`, and the payload has local
degrees `< q + Bstar * Ecell`.

`native_activation_of_inputs` composes this with `childSetting_macroBank`: from the V42 inputs
(not constructed here) the activation is executable in every stratum.
-/

open Finset Classical

noncomputable section

namespace S07V43

open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V42 S07V40

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

/-- **Physical activation in a stratum of the actual V40 bank.** -/
theorem native_stratum_activation {d c E R P q Ecell zmax L N : ℕ}
    {C0 : CoreCompression H lab F W d c E}
    (hM : MacroBank (childSetting C0 R P q Ecell zmax) L N) (j : ℕ)
    (z : Fin P → Cat d R → ℤ)
    (hact : ∀ p v, z p v ≠ 0 →
      gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N j))
    (hz : ∀ p, ∑ v, (z p v).natAbs ≤ mStrat (childSetting C0 R P q Ecell zmax) N j) :
    ∃ hs : (stratBank (childSetting C0 R P q Ecell zmax) N j).Supplies z,
      PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N j)
        (gCat C0 R) z hs Ecell ∧
      Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N j) (Bank.payload hs) ∧
      Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N j) (Bank.cover hs) ∧
      Bank.payload hs ⊆ Br (childSetting C0 R P q Ecell zmax) N ∧
      Bank.cover hs ⊆ Br (childSetting C0 R P q Ecell zmax) N ∧
      ∀ x, deg (Bank.payload hs) x <
        q + (childSetting C0 R P q Ecell zmax).Bstar * Ecell := by
  set S := childSetting C0 R P q Ecell zmax with hS
  have hs : (stratBank S N j).Supplies z :=
    stratBank_supplies (fun p v hv => (childSetting_g_mem_K_iff C0 R P q Ecell zmax v _).2
      (hact p v hv)) hz
  obtain ⟨hv, hY⟩ := child_stratBank_valid hM j
  have hE : ∀ k, ((stratBank S N j).tot k).card ≤ Ecell :=
    fun k => (hM.cells _ (get_mem_run k)).1.2.2.2.1
  have hav := stratBank_avoids (j := j) hM
  refine ⟨hs, physical_activation hv hY hE hs, Bank.payload_avoids_of hs hav,
    fun e he => hav e (Bank.cover_subset_total hs he),
    (Bank.payload_subset_total hs).trans stratBank_total_subset,
    (Bank.cover_subset_total hs).trans stratBank_total_subset, fun x => ?_⟩
  exact lt_of_le_of_lt (deg_mono (Bank.payload_subset_total hs) x) (stratBank_deg_lt hM x)

universe u v

/-- **Activation is executable in every stratum of the actual bank, from the V42 inputs.**
Constants `t, Ecell, ε, n0` are fixed before the host.  The inputs that are hypotheses here (and
are NOT constructed in this project) are exactly those of V42 `nativeSetting_supply`: the core
compression `C0`, a deleted compression for every small `Z`, and V31 terminal supplies; plus the
numeric premises `0 < q`, `zmax ≤ coreDelta·|W|`, `q + Bstar·Ecell ≤ ε|W|` and the cap. -/
theorem native_activation_of_inputs {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' s : ℕ)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) :
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
      ∀ (j : ℕ) (z : Fin P → Cat d (catR β d c E d' c' E') → ℤ),
      (∀ p w, z p w ≠ 0 → gCat C0 (catR β d c E d' c' E') w ∈
        KZ H lab F W (Zstrat (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) N j)) →
      (∀ p, ∑ w, (z p w).natAbs ≤
        mStrat (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) N j) →
      ∃ hs : (stratBank (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) N j).Supplies z,
        PhysicalActivation H lab F W
          (stratBank (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) N j)
          (gCat C0 (catR β d c E d' c' E')) z hs Ecell ∧
        Avoids (Zstrat (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) N j)
          (Bank.payload hs) := by
  obtain ⟨t, Ecell, ε, hε, n0, hbank⟩ := childSetting_macroBank.{u, v} h hβ d c E d' c' E' s hβ₁
  refine ⟨t, Ecell, ε, hε, n0, ?_⟩
  intro V _ I H lab F W hH3 hH4 hWc hWn C0 P q zmax N hq hzmax hqB hcap CZ hterm j z hact hz
  have hM := hbank hH3 hH4 hWc hWn C0 P q zmax N hq hzmax hqB hcap CZ hterm
  obtain ⟨hs, hPA, hav, -⟩ := native_stratum_activation hM j z hact hz
  exact ⟨hs, hPA, hav⟩

end S07V43
