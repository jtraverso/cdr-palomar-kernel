/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ActualPackingEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The stock is removed before the nibble and restored for cover-down. The
nibble's protected-load hypothesis is therefore vacuous; its residue tolerance
can be chosen after the stock completion supply κ. Both monitor families are
measured on the same actual residual and transferred unchanged to cover-down.
-/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry
open BasalIncidence ProtectedNibble LocalizedCover

theorem g4_nibble_after_stock_deletion {I : Type} (F : Set (Multiset I))
    (C α κ η τ L : ℝ) (h qMon : ℕ) (hC : 1 ≤ C) (hα : 0 < α)
    (hκ : 0 < κ) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D DR : Finset (Finset V)) (R : Finset (Sym2 V)),
        n₀ ≤ Fintype.card V →
        let S := cover D∪R
        let J := subHost H (edges H\S)
        IsDiffuseSeed J F C φ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
        IsPhysical H F (edges H) →
        IsDecomposition H F (cover D) D → IsDecomposition H F R DR →
        Disjoint (cover D) R →
        (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ),
          ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^qMon →
          (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤
            3*L*(T∩bad k).card) →
          (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
          ∃ Q : Finset (Finset V), IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) R ∧
            (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d+2*q:ℕ):ℝ) ≤ η*Fintype.card V ∧
              (∀ k, |edgeSum (loc k) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (loc k) (cover D)| ≤
                τ*Fintype.card V*(bad k).card+
                  (3*L*(bad k).card)*(2*d+2*q:ℕ)/2) ∧
              ∀ j, |edgeSum (full j) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (full j) (cover D)| ≤
                τ*(Fintype.card V:ℝ)^2+
                  (3*L*Fintype.card V)*(2*d+2*q:ℕ)/2 := by
  obtain ⟨εc,hεc,nW,hW⟩ := cover_down_window κ η hκ hη
  let δ := min (εc/4) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨εN,hεN,nP,hP⟩ :=
    joint_physical_moment_packing F C α δ τ L h qMon hC hα hδ hτ hL
  refine ⟨max nP (max nW ⌈2/εc⌉₊),?_⟩
  intro V _ H φ D DR R hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hXR hSupply
    κi ι _ _ bad loc full hcount hloc hfull
  let S := cover D∪R
  let J := subHost H (edges H\S)
  have hEmptyDec : IsDecomposition J F ∅ (∅ : Finset (Finset V)) := by
    simp [IsDecomposition]
  have hAllowLoc : ∀ k T, IsAllowed J F T →
      |triSum (loc k) T| ≤ 3*L*(T∩bad k).card := by
    intro k T hT
    exact hloc k T (isAllowed_mono (subHost_le H _) rfl hT)
  have hAllowFull : ∀ j T, IsAllowed J F T →
      |triSum (full j) T| ≤ 3*L*T.card := by
    intro j T hT
    exact hfull j T (isAllowed_mono (subHost_le H _) rfl hT)
  have hnP : nP ≤ Fintype.card V := (le_max_left _ _).trans hn
  obtain ⟨P,hPJ,hPEmpty,hUphys,hSparse,hLocal,hGlobal⟩ :=
    hP J φ ∅ ∅ 0 hnP hSeed hPhysJ h3 h4 hEmptyDec
      (by intro v; simp [degIn])
      (by simpa using (show (0:ℝ) ≤ εN*Fintype.card V from by positivity))
      κi ι bad loc full hcount hAllowLoc hAllowFull
  have hPH : IsPacking H F P :=
    ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hPJ.1 T hT),hPJ.2⟩
  have hPE : P.biUnion triEdges ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hPJ.1 T hT) heT
  have hPDis : Disjoint (P.biUnion triEdges) S := by
    apply disjoint_left.mpr
    intro e heP heS
    have hh : e ∈ edges H\S := by
      rw [←Residual.edges_subHost_eq (sdiff_subset : edges H\S ⊆ edges H)]
      exact hPE heP
    exact (mem_sdiff.mp hh).2 heS
  let U := edges J\P.biUnion triEdges
  let d := ⌈δ*Fintype.card V⌉₊
  have hdU : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    have hv : (((edges J\∅)\P.biUnion triEdges).filter
        (fun e => v ∈ e)).card ≤ d := by
      exact_mod_cast (hSparse v).trans (Nat.le_ceil _)
    simpa only [U, sdiff_empty] using hv
  have hnε : 2 ≤ εc*Fintype.card V := by
    have h1 : 2/εc ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hεc).mp h1
    nlinarith
  have hdε : (d:ℝ) ≤ εc*Fintype.card V := by
    have hc : (d:ℝ) < δ*Fintype.card V+1 := Nat.ceil_lt_add_one (by positivity)
    have hδc : δ ≤ εc/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hδc (by positivity : (0:ℝ) ≤ Fintype.card V)]
  have hdiag : ∀ e ∈ U, ¬e.IsDiag := by
    intro e he
    have heJ : e ∈ edges J := (mem_sdiff.mp he).1
    have heH : e ∈ edges H := (mem_sdiff.mp (by
      simpa only [J, Residual.edges_subHost_eq sdiff_subset] using heJ :
        e ∈ edges H\S)).1
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using heH)
  have hm := Envelope.two_card_le_card_mul_degree U hdiag hdU
  obtain ⟨q,hwin,hqdeg⟩ := hW (Fintype.card V) U.card d
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    (by omega) hdε
  have hJE : edges J = edges H\S := Residual.edges_subHost_eq sdiff_subset
  obtain ⟨Q,hQ,hQR,hrem,hQphys,hQl,hQg⟩ :=
    joint_monitored_stock_transition H F D DR P R hD hR hXR hPhysH
      hPH hPDis hSupply d q
      (by simpa only [S,J,U,hJE] using hdU)
      (by simpa only [S,J,U,hJE] using hwin)
      bad loc full L τ τ hL.le hloc hfull
       (by simpa only [S,J,U,hJE,sdiff_empty] using hLocal)
       (by simpa only [S,J,U,hJE,sdiff_empty] using hGlobal)
  exact ⟨Q,hQ,hQR,hrem,hQphys,d,q,hqdeg,hQl,hQg⟩

end TypedTriangle.StockEntry
