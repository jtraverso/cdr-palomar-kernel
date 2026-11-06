/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.SimulLayer

@[expose] public section

/-!
# The finite scheduling induction of S07 §7 — V21

Roots of `Z` are processed one at a time (finset induction: any order).  At the current root
`a`, with selectors `σ v` already fixed for the processed roots `Z'`:

* deleted vertex window `Z0 = Z ∪ N_X(a) ∪ N_{B0}(a) ∪ Sat`, where `Sat` is the set of
  vertices already used as auxiliaries `q` times (`satSet`); `|Sat| ≤ A·r·|Z'| / q`;
* forbidden edge window `Bf = E(X) ∪ E(B0) ∪ ⋃_{v ∈ Z'} P_v` (all previous bases), whose
  maximum degree is `≤ r + b + 60·(r + q)`: ports counted by degree (`≤ r` roots),
  auxiliaries by the counter (`≤ q` roots), each contributing `≤ 60`;
* the local availability premise of the root `a` (ONE root, exact windows) supplies its
  selector; ports are never deleted: they are the specified boundary, and the contract
  already forbids using a port as an auxiliary.

The root objects (fuel, bases, auxiliaries) are all chosen here, BEFORE any mode.

`schedule` proves that this produces a family satisfying `SimulFamily`, under the two
verifiable window conditions

  `|Z| + r + b + A·r·|Z| / q ≤ ζw`,     `b + 61·r + 60·q ≤ ρw`.

`simultaneous_layer` composes the schedule with the layer theorems of `SimulLayer.lean`:
one fixed fuel `R`, (7.3), and for every locally admissible `L ⊆ E(X)` the exact positive
partition (7.4) and the charge identity (7.5).  `X[Z]` empty is a hypothesis of this layer
only.  Nothing is claimed about the lattice membership or decomposability of `K_0` or `Y_L`.
-/

namespace SelSimul

open Finset SelBridge SelTyped

variable {V I : Type*} [DecidableEq V] [Fintype V]

/-- **Scheduling induction**: from the single-root availability premises, a simultaneous
family with disjoint bases and auxiliary counters `≤ q`. -/
theorem schedule (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z : Finset V)
    (Adm : V → Finset V → Prop) {A q r b ζw ρw : ℕ}
    (hAvail : ∀ v ∈ Z, LocalAvail G lab F v (X.neighborFinset v) (Adm v) A ζw ρw)
    (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r) (hB : ∀ x, B0.degree x ≤ b)
    (hζ : Z.card + r + b + A * r * Z.card / q ≤ ζw) (hρ : b + 61 * r + 60 * q ≤ ρw) :
    ∃ σ : V → LocalSel V, SimulFamily G lab F X B0 Z Adm A q σ := by
  have key : ∀ Z' : Finset V, Z' ⊆ Z → ∃ σ : V → LocalSel V,
      (∀ v ∈ Z', (σ v).Valid G lab F v (X.neighborFinset v) (Adm v)
        (Z ∪ X.neighborFinset v ∪ B0.neighborFinset v) (X.edgeFinset ∪ B0.edgeFinset) A) ∧
      (∀ v ∈ Z', ∀ v' ∈ Z', v ≠ v' → Disjoint (σ v).P (σ v').P) ∧
      (∀ x, auxCount Z' (fun v => (σ v).W) x ≤ q) := by
    intro Z'
    induction Z' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ⟨∅, ∅, fun _ => ∅⟩, by simp, by simp, fun x => by simp [auxCount]⟩
    | insert a Z' ha ih =>
      intro hsub
      have haZ : a ∈ Z := hsub (mem_insert_self a Z')
      obtain ⟨σ, hval, hdisj, hcnt⟩ := ih ((subset_insert a Z').trans hsub)
      set Wf : V → Finset V := fun v => (σ v).W with hWf
      -- per-root auxiliary bound `A·r`
      have hWcard : ∀ v ∈ Z', (Wf v).card ≤ A * r := by
        intro v hv
        refine ((hval v hv).card_le).trans (Nat.mul_le_mul_left _ ?_)
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX v
      -- the saturated set
      set Sat := satSet Z' Wf q with hSat
      have hSatc : Sat.card ≤ A * r * Z.card / q := by
        refine (satSet_card_le Z' Wf hq hWcard).trans (Nat.div_le_div_right ?_)
        exact Nat.mul_le_mul_left _ (card_le_card ((subset_insert a Z').trans hsub))
      -- the deleted vertex window
      set Z0 := Z ∪ X.neighborFinset a ∪ B0.neighborFinset a ∪ Sat with hZ0
      have hZ0c : Z0.card ≤ ζw := by
        rw [hZ0]
        have h1 := card_union_le (Z ∪ X.neighborFinset a ∪ B0.neighborFinset a) Sat
        have h2 := card_union_le (Z ∪ X.neighborFinset a) (B0.neighborFinset a)
        have h3 := card_union_le Z (X.neighborFinset a)
        have h4 : (X.neighborFinset a).card ≤ r := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX a
        have h5 : (B0.neighborFinset a).card ≤ b := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hB a
        omega
      -- the forbidden edge window
      set Bf := X.edgeFinset ∪ B0.edgeFinset ∪ Z'.biUnion (fun v => (σ v).P) with hBf
      have hBfd : ∀ y, edeg Bf y ≤ ρw := by
        intro y
        rw [hBf]
        have h1 := edeg_union_le (X.edgeFinset ∪ B0.edgeFinset) (Z'.biUnion (fun v => (σ v).P)) y
        have h2 := edeg_union_le X.edgeFinset B0.edgeFinset y
        rw [edeg_edgeFinset] at h2
        rw [edeg_edgeFinset] at h2
        have h3 := edeg_biUnion_le Z' (fun v => (σ v).P) (fun v => X.neighborFinset v ∪ (σ v).W)
          (fun v hv => (hval v hv).deg_le)
          (fun v hv f hf y hy => mem_union.mpr ((hval v hv).supp f hf y hy)) y
        have h4 := filter_or_card_le Z' (fun v => y ∈ X.neighborFinset v) (fun v => y ∈ (σ v).W)
        have h5 := portCount_le X Z' y
        have h6 : (Z'.filter (fun v => y ∈ (σ v).W)).card ≤ q := hcnt y
        have h7 := hX y
        have h8 := hB y
        simp only [mem_union] at h3
        have h9 : 60 * (Z'.filter (fun v => y ∈ X.neighborFinset v ∨ y ∈ (σ v).W)).card ≤
            60 * (r + q) := Nat.mul_le_mul_left _ (by omega)
        omega
      -- the local selector of the current root
      obtain ⟨σa, hσa⟩ := hAvail a haZ Z0 Bf hZ0c hBfd
      refine ⟨Function.update σ a σa, ?_, ?_, ?_⟩
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · rw [Function.update_self]
          exact hσa.mono (fun x hx => by rw [hZ0]; exact mem_union_left _ hx)
            (fun f hf => by rw [hBf]; exact mem_union_left _ hf)
        · have hva : v ≠ a := fun h => ha (h ▸ hv)
          rw [Function.update_of_ne hva]
          exact hval v hv
      · intro v hv v' hv' hne
        have hPa : ∀ w ∈ Z', Disjoint σa.P (σ w).P := fun w hw =>
          hσa.avoidB.mono_right (fun f hf => by
            rw [hBf]; exact mem_union_right _ (mem_biUnion.mpr ⟨w, hw, hf⟩))
        have hupd : ∀ w ∈ Z', Function.update σ a σa w = σ w := fun w hw =>
          Function.update_of_ne (by rintro rfl; exact ha hw) _ _
        rcases mem_insert.mp hv with hva | hvZ <;> rcases mem_insert.mp hv' with hva' | hvZ'
        · exact absurd (hva.trans hva'.symm) hne
        · rw [hva, Function.update_self, hupd v' hvZ']; exact hPa v' hvZ'
        · rw [hva', Function.update_self, hupd v hvZ]; exact (hPa v hvZ).symm
        · rw [hupd v hvZ, hupd v' hvZ']; exact hdisj v hvZ v' hvZ' hne
      · have hcong : ∀ v ∈ Z', (fun v => (Function.update σ a σa v).W) v = Wf v := by
          intro v hv
          simp only [hWf]
          rw [Function.update_of_ne (by rintro rfl; exact ha hv)]
        intro x
        refine auxCount_insert_le ha _ hq (fun y => ?_) ?_ x
        · rw [auxCount_congr hcong]; exact hcnt y
        · rw [satSet_congr hcong, Function.update_self]
          exact hσa.avoidZ.mono_right (fun y hy => by rw [hZ0]; exact mem_union_right _ hy)
  obtain ⟨σ, h1, h2, h3⟩ := key Z (subset_refl _)
  exact ⟨σ, ⟨h1, h2, h3⟩⟩

/-- **The S07 ceiling (7.1) pays the saturated set**: if `4·A·|Z|·r ≤ q·m` (as for
`q = ⌈4A|Z|r/m⌉`, `m = ζn`) and `|Z| + r + b + m/4 ≤ ζw`, then the vertex-window condition
of `schedule` holds. -/
theorem window_of_ceiling {A q r b ζw m z : ℕ} (hq : 0 < q) (h : 4 * A * z * r ≤ q * m)
    (h' : z + r + b + m / 4 ≤ ζw) : z + r + b + A * r * z / q ≤ ζw := by
  have := sat_budget_of_ceiling hq h
  omega

/-- **The simultaneous finite layer (S07 §7)**, from single-root availability premises.

Hypotheses: `X[Z]` empty (a hypothesis of this layer only), `Δ(X) ≤ r`, `Δ(B0) ≤ b`,
`q > 0`, every root `v ∈ Z` satisfies the single-root availability premise with ports
`N_X(v)` and windows `ζw`, `ρw`, the empty demand is admissible, and
`|Z| + r + b + A·r·|Z|/q ≤ ζw`, `b + 61r + 60q ≤ ρw`.

Conclusion: there are root objects `σ v` (chosen BEFORE any mode) with
* pairwise disjoint fuels; the fuel `R = ⋃ R_v` avoids `X ∪ B0`; bases and auxiliaries lie
  outside `Z`; every vertex is an auxiliary of at most `q` roots;
* (7.3) `Δ(R) ≤ max(A·r, 60·r + 61·q)`;
* for EVERY `L ⊆ E(X)` whose stars at `Z` are admissible, with the SAME `R`: (7.4) the
  packing `D_L` of pairwise edge-disjoint permitted triangles rooted in `Z` and the residual
  `Y_L` satisfy `R ∩ L = ∅`, `R ∪ L = E(D_L) ⊔ Y_L`, `Y_L` has no edge meeting `Z`,
  `Δ(Y_L) ≤ 61r + 60q`; and (7.5) for every additive charge `c`,
  `c(Y_L) − c(K_0) = c(L) − (c(D_L) − c(D_0))`, `K_0 = Y_∅`.

Nothing is asserted about `K_0` or `Y_L` lying in the triangle lattice. -/
theorem simultaneous_layer (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z : Finset V)
    (Adm : V → Finset V → Prop) {A q r b ζw ρw : ℕ}
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hAvail : ∀ v ∈ Z, LocalAvail G lab F v (X.neighborFinset v) (Adm v) A ζw ρw)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r) (hB : ∀ x, B0.degree x ≤ b)
    (hζ : Z.card + r + b + A * r * Z.card / q ≤ ζw) (hρ : b + 61 * r + 60 * q ≤ ρw) :
    ∃ σ : V → LocalSel V,
      (∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' →
        Disjoint (fuel v (σ v).P (σ v).W) (fuel v' (σ v').P (σ v').W)) ∧
      Disjoint (fuelU Z σ) (X.edgeFinset ∪ B0.edgeFinset) ∧
      (∀ v ∈ Z, (∀ w ∈ (σ v).W, w ∉ Z) ∧ ∀ f ∈ (σ v).P, ∀ y ∈ f, y ∉ Z) ∧
      (∀ x, auxCount Z (fun v => (σ v).W) x ≤ q) ∧
      (∀ y, edeg (fuelU Z σ) y ≤ max (A * r) (60 * r + 61 * q)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → (∀ v ∈ Z, Adm v (demand X L v)) →
        Disjoint (fuelU Z σ) L ∧
        fuelU Z σ ∪ L = packEdges (packing X Z σ L) ∪ residual X Z σ L ∧
        Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L) ∧
        (packing X Z σ L : Set (V × Sym2 V)).PairwiseDisjoint (fun p => triE p.1 p.2) ∧
        (∀ p ∈ packing X Z σ L, p.1 ∈ Z ∧ ∃ x y, p.2 = s(x, y) ∧ x ≠ y ∧
          TypedTriangle.SparseEdge.IsAllowed G lab F {p.1, x, y}) ∧
        (∀ f ∈ residual X Z σ L, ∀ v ∈ Z, v ∉ f) ∧
        (∀ y, edeg (residual X Z σ L) y ≤ 61 * r + 60 * q) ∧
        ∀ {M : Type} [AddCommGroup M] (c : Sym2 V → M),
          ∑ f ∈ residual X Z σ L, c f - ∑ f ∈ residual X Z σ ∅, c f =
            ∑ f ∈ L, c f - (∑ p ∈ packing X Z σ L, ∑ f ∈ triE p.1 p.2, c f -
              ∑ p ∈ packing X Z σ ∅, ∑ f ∈ triE p.1 p.2, c f) := by
  obtain ⟨σ, h⟩ := schedule G lab F X B0 Z Adm hAvail hq hX hB hζ hρ
  refine ⟨σ, fun v hv v' hv' hne => h.fuels_disjoint hZ hv hv' hne, h.fuelU_avoid,
    h.outside_Z hZ, h.cnt, h.fuelU_edeg_le hZ hX, fun L hL hadm => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.layer_partition hZ hX hL hadm
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun c => h.charge_identity hZ hX hAdm0 hL hadm c⟩

end SelSimul
