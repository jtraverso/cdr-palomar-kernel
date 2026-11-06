/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4UnprotectedNibbleEntry
public import RequestProject.TypedTriangle.TriangleMonitorJointPacking
public import RequestProject.TypedTriangle.TriangleMonitorStockTransition
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

theorem g4_nibble_after_stock_deletion_with_triangle_monitors {I : Type} (F : Set (Multiset I))
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
        ∀ (κi ι ν : Type) [Fintype κi] [Fintype ι] [Fintype ν]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ) (w : ν → Finset V → ℝ),
          ((Fintype.card κi+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^qMon →
          (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤
            3*L*(T∩bad k).card) →
          (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
          (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
          ∃ P₀ Q : Finset (Finset V), P₀ ⊆ Q ∧ IsPacking H F P₀ ∧
            (∀ T ∈ P₀, IsAllowed J F T) ∧
            (∀ v, (((edges J\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
            (∀ k, |(∑ T ∈ P₀, w k T)-(∑ T ∈ allowed J F, φ T*w k T)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
            IsPacking H F Q ∧
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
  let δ := min (εc/4) (min (1/4) η)
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) hη)
  obtain ⟨nP,hP⟩ :=
    WeightedStar.joint_sparse_packing_with_triangle_monitors C α δ τ L qMon
      (by linarith) hα hδ hτ hL
  refine ⟨max nP (max nW ⌈2/εc⌉₊),?_⟩
  intro V _ H φ D DR R hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hXR hSupply
    κi ι ν _ _ _ bad loc full w hcount hloc hfull hw
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
  have hAllowW : ∀ k T, IsAllowed J F T → |w k T| ≤ 1 :=
    fun k T hT => hw k T (isAllowed_mono (subHost_le H _) rfl hT)
  obtain ⟨P,hPsub,hPJ,hSparse,hLocal,hGlobal,hTriangles⟩ :=
    hP J F φ hnP hSeed h3 κi ι ν bad loc full w hcount hAllowLoc hAllowFull hAllowW
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
    have hv : ((edges J\P.biUnion triEdges).filter
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
  obtain ⟨Q,hPQ,hQ,hQR,hrem,hQphys,hMom⟩ :=
    monitored_stock_transition_retaining_initial_packing H F D DR P R hD hR hXR hPhysH
      hPH hPDis hSupply d q
      (by simpa only [S,J,U,hJE] using hdU)
      (by simpa only [S,J,U,hJE] using hwin)
  refine ⟨P,Q,hPQ,hPH,hPJ.1,?_,hTriangles,hQ,hQR,hrem,hQphys,d,q,hqdeg,?_,?_⟩
  · intro v
    exact (hSparse v).trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (Nat.cast_nonneg _))
  · intro k
    exact hMom (loc k) (bad k) L (τ*Fintype.card V*(bad k).card)
      hL.le (hloc k) (by simpa only [S,J,hJE] using hLocal k)
  · intro k
    have htri : ∀ T, IsAllowed H F T →
        |triSum (full k) T| ≤ 3*L*(T∩(univ : Finset V)).card := by
      intro T hT
      simpa only [inter_univ] using hfull k T hT
    simpa only [card_univ] using hMom (full k) (univ : Finset V) L
      (τ*(Fintype.card V:ℝ)^2) hL.le htri
      (by simpa only [S,J,hJE] using hGlobal k)

#print axioms g4_nibble_after_stock_deletion_with_triangle_monitors
end TypedTriangle.StockEntry
