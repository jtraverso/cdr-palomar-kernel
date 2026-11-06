/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V27.CoreAssembly
public import RequestProject.Selectors.SimulSchedule

@[expose] public section

/-!
# V27 — the NEW simultaneous layer inside the core (no `|Z|` window)

`schedule_core` replaces the vertex window `Z ∪ N_X(a) ∪ N_{B0}(a) ∪ Sat` of the old
`SelSimul.schedule` by `N_X(a) ∪ N_{B0}(a) ∪ Sat`: the root set `Z` (which may contain almost
all vertices) is NOT deleted.  It is avoided because each selector lives in the core
(`CoreAvail`: non-port vertices in `Wc`) and `Z ∩ Wc = ∅`.  Saturation is paid with the total
number `≤ A·r·n` of auxiliary positions: `|Sat| ≤ A·r·n/q`.

`simultaneous_layer_core` composes it with the unchanged layer theorems of
`SelSimul` (`SimulLayer.lean`): one fixed fuel `R` (chosen before `L`), congestion
`Δ(R) ≤ max(A·r, 60·r + 61·q)`, and for EVERY later admissible `L ⊆ E(X)` the exact positive
partition and the charge identity.
-/

namespace S07V27

open Finset SelBridge SelTyped SelSimul

variable {V I : Type*} [DecidableEq V]

/-- Enlarging the deleted vertex window by a set the selector already avoids. -/
theorem _root_.SelSimul.LocalSel.Valid.extendZ {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {v : V} {U : Finset V} {Adm : Finset V → Prop} {Z0 Z1 : Finset V}
    {Bf : Finset (Sym2 V)} {A : ℕ} {σ : LocalSel V} (h : σ.Valid G lab F v U Adm Z0 Bf A)
    (h1 : Disjoint σ.W Z1) : σ.Valid G lab F v U Adm (Z0 ∪ Z1) Bf A where
  typed := h.typed
  avoidB := h.avoidB
  supp := h.supp
  wing := h.wing
  avoidZ := disjoint_union_right.mpr ⟨h.avoidZ, h1⟩
  portFree := h.portFree
  card_le := h.card_le
  deg_le := h.deg_le
  modes := h.modes

variable [Fintype V]

/-- **Scheduling induction inside the core.**  Roots are processed one at a time; the deleted
vertex window of the current root `a` is `N_X(a) ∪ N_{B0}(a) ∪ Sat` (NO root set `Z`), where
`Sat` (vertices already used `q` times as auxiliaries) is bounded through the TOTAL number of
auxiliary positions `∑_{v} |W_v| ≤ A·r·n`: `|Sat| ≤ A·r·n/q`.  The forbidden edge window is
`E(X) ∪ E(B0) ∪ (earlier bases)`, of degree `≤ r + b + 60(r + q)` (separate port-use counter
`≤ r` and auxiliary-use counter `≤ q`).  Roots outside the core are avoided because every
selector has its non-port vertices in the core `Wc` and `Z ∩ Wc = ∅`.  The output is a
`SimulFamily` (the invariant of the old layer, with its window `Z ∪ N_X(v) ∪ N_{B0}(v)`), so all
the old layer theorems apply verbatim. -/
theorem schedule_core (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z Wc : Finset V)
    (hZW : Disjoint Z Wc)
    (Adm : V → Finset V → Prop) {A q r b ζw ρw : ℕ}
    (hAvail : ∀ v ∈ Z, CoreAvail G lab F v (X.neighborFinset v) (Adm v) A ζw ρw Wc)
    (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r) (hB : ∀ x, B0.degree x ≤ b)
    (hζ : r + b + A * r * Fintype.card V / q ≤ ζw) (hρ : b + 61 * r + 60 * q ≤ ρw) :
    ∃ σ : V → LocalSel V, SimulFamily G lab F X B0 Z Adm A q σ ∧ ∀ v ∈ Z, (σ v).W ⊆ Wc := by
  have key : ∀ Z' : Finset V, Z' ⊆ Z → ∃ σ : V → LocalSel V,
      (∀ v ∈ Z', (σ v).Valid G lab F v (X.neighborFinset v) (Adm v)
        (Z ∪ X.neighborFinset v ∪ B0.neighborFinset v) (X.edgeFinset ∪ B0.edgeFinset) A) ∧
      (∀ v ∈ Z', ∀ v' ∈ Z', v ≠ v' → Disjoint (σ v).P (σ v').P) ∧
      (∀ x, auxCount Z' (fun v => (σ v).W) x ≤ q) ∧ (∀ v ∈ Z', (σ v).W ⊆ Wc) := by
    intro Z'
    induction Z' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ⟨∅, ∅, fun _ => ∅⟩, by simp, by simp, fun x => by simp [auxCount],
        by simp⟩
    | insert a Z' ha ih =>
      intro hsub
      have haZ : a ∈ Z := hsub (mem_insert_self a Z')
      obtain ⟨σ, hval, hdisj, hcnt, hsubW⟩ := ih ((subset_insert a Z').trans hsub)
      set Wf : V → Finset V := fun v => (σ v).W with hWf
      -- per-root auxiliary bound `A·r`
      have hWcard : ∀ v ∈ Z', (Wf v).card ≤ A * r := by
        intro v hv
        refine ((hval v hv).card_le).trans (Nat.mul_le_mul_left _ ?_)
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hX v
      -- the saturated set
      set Sat := satSet Z' Wf q with hSat
      have hSatc : Sat.card ≤ A * r * Fintype.card V / q := by
        refine (satSet_card_le Z' Wf hq hWcard).trans (Nat.div_le_div_right ?_)
        exact Nat.mul_le_mul_left _ (card_le_univ _)
      -- the deleted vertex window
      set Z0 := X.neighborFinset a ∪ B0.neighborFinset a ∪ Sat with hZ0
      have hZ0c : Z0.card ≤ ζw := by
        rw [hZ0]
        have h1 := card_union_le (X.neighborFinset a ∪ B0.neighborFinset a) Sat
        have h2 := card_union_le (X.neighborFinset a) (B0.neighborFinset a)
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
      obtain ⟨σa, hσa, hσaW⟩ := hAvail a haZ Z0 Bf hZ0c hBfd
      have hσaZ : Disjoint σa.W Z := (hZW.symm.mono_left hσaW)
      refine ⟨Function.update σ a σa, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · rw [Function.update_self]
          have hval' := (hσa.extendZ hσaZ).mono (Z0' := Z ∪ X.neighborFinset v ∪
              B0.neighborFinset v) (Bf' := X.edgeFinset ∪ B0.edgeFinset)
            (fun x hx => by
              rw [hZ0]
              simp only [mem_union] at hx ⊢
              tauto)
            (fun f hf => by rw [hBf]; exact mem_union_left _ hf)
          exact hval'
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
      · intro v hv
        rcases mem_insert.mp hv with rfl | hv'
        · rw [Function.update_self]; exact hσaW
        · have hva : v ≠ a := fun h => ha (h ▸ hv')
          rw [Function.update_of_ne hva]; exact hsubW v hv'
  obtain ⟨σ, h1, h2, h3, h4⟩ := key Z (subset_refl _)
  exact ⟨σ, ⟨h1, h2, h3⟩, h4⟩


/-- **The simultaneous PAR/BAL layer inside the core (no `|Z|` term).**

Hypotheses: `X[Z]` empty, `Z ∩ Wc = ∅`, `Δ(X) ≤ r`, `Δ(B0) ≤ b`, `q > 0`, every root has the
core availability premise with ports `N_X(v)`, the empty demand is admissible, and
`r + b + A·r·n/q ≤ ζw`, `b + 61r + 60q ≤ ρw`.

Conclusion: root objects `σ v` (chosen BEFORE any `L`) with non-port vertices in the core,
pairwise disjoint fuels, the fuel avoiding `X ∪ B0`, auxiliary-use counters `≤ q`, the
uniform congestion bound `Δ(R) ≤ max(A·r, 60·r + 61·q)`, and for EVERY later `L ⊆ E(X)` whose
stars are admissible: the exact positive partition `R ∪ L = E(D_L) ⊔ Y_L` with permitted
triangles rooted in `Z`, `Y_L` avoiding `Z`, `Δ(Y_L) ≤ 61r + 60q`, and the charge identity. -/
theorem simultaneous_layer_core (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj] (Z Wc : Finset V)
    (Adm : V → Finset V → Prop) {A q r b ζw ρw : ℕ}
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') (hZW : Disjoint Z Wc)
    (hAvail : ∀ v ∈ Z, CoreAvail G lab F v (X.neighborFinset v) (Adm v) A ζw ρw Wc)
    (hAdm0 : ∀ v ∈ Z, Adm v ∅)
    (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r) (hB : ∀ x, B0.degree x ≤ b)
    (hζ : r + b + A * r * Fintype.card V / q ≤ ζw) (hρ : b + 61 * r + 60 * q ≤ ρw) :
    ∃ σ : V → LocalSel V,
      (∀ v ∈ Z, (σ v).W ⊆ Wc) ∧
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
  obtain ⟨σ, h, hW⟩ := schedule_core G lab F X B0 Z Wc hZW Adm hAvail hq hX hB hζ hρ
  refine ⟨σ, hW, fun v hv v' hv' hne => h.fuels_disjoint hZ hv hv' hne, h.fuelU_avoid,
    h.outside_Z hZ, h.cnt, h.fuelU_edeg_le hZ hX, fun L hL hadm => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.layer_partition hZ hX hL hadm
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun c => h.charge_identity hZ hX hAdm0 hL hadm c⟩

end S07V27
