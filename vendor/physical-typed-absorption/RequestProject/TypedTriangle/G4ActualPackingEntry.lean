/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4JointStockMonitors
public import RequestProject.TypedTriangle.JointPhysicalMomentPacking
public import RequestProject.TypedTriangle.BasalStockEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! One physical host, one protected weighted packing, one cover-down, and one
actual leftover. Both monitor families refer to this same outcome. This is the
packing-to-stock stage; selector and bank act only after its positive residue. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry
open BasalIncidence ProtectedNibble LocalizedCover

theorem g4_actual_packing_to_stock {I : Type} (F : Set (Multiset I))
    (C α κ τ L : ℝ) (h qMon : ℕ) (hC : 1 ≤ C) (hα : 0 < α)
    (hκ : 0 < κ) (hτ : 0 < τ) (hL : 0 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D DR : Finset (Finset V)) (R : Finset (Sym2 V)) (dS : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
        IsDecomposition H F (cover D) D → IsDecomposition H F R DR →
        Disjoint (cover D) R →
        (∀ v, degIn (cover D∪R) v ≤ dS) →
        (dS:ℝ) ≤ ε*Fintype.card V →
        (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ),
          ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^qMon →
          (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
          (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
          ∃ Q : Finset (Finset V), IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) R ∧
            (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d+2*q:ℕ):ℝ) ≤ Fintype.card V ∧
              (∀ k, |edgeSum (loc k) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (loc k) (cover D)| ≤
                τ*Fintype.card V*(bad k).card+
                  (3*L*(bad k).card)*(2*d+2*q:ℕ)/2) ∧
              ∀ j, |edgeSum (full j) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (full j) (cover D)| ≤
                τ*(Fintype.card V:ℝ)^2+
                  (3*L*Fintype.card V)*(2*d+2*q:ℕ)/2 := by
  obtain ⟨εc,hεc,nW,hW⟩ := cover_down_window κ 1 hκ (by norm_num)
  let δ := min (εc/4) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨ε,hε,nP,hP⟩ := joint_physical_moment_packing F C α δ τ L h qMon
    hC hα hδ hτ hL
  refine ⟨ε,hε,max nP (max nW ⌈2/εc⌉₊),?_⟩
  intro V _ H φ D DR R dS hn hseed hphys hH3 hH4 hD hR hXR hdeg hsmall
    hSupply κi ι _ _ bad loc full hcount hloc hfull
  let S := cover D∪R
  have hSD : IsDecomposition H F S (D∪DR) :=
    S07V26.isDecomposition_union hXR hD hR
  obtain ⟨P,hPack,hPS,hUphys,hSparse,hLocal,hGlobal⟩ :=
    hP H φ S (D∪DR) dS ((le_max_left _ _).trans hn) hseed hphys hH3 hH4
      hSD hdeg hsmall κi ι bad loc full hcount hloc hfull
  let U := (edges H\S)\P.biUnion triEdges
  let d := ⌈δ*Fintype.card V⌉₊
  have hdU : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    exact_mod_cast (hSparse v).trans (Nat.le_ceil _)
  have hN : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hnε : 2 ≤ εc*Fintype.card V := by
    have h1 : 2/εc ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hεc).mp h1
    nlinarith
  have hdε : (d:ℝ) ≤ εc*Fintype.card V := by
    have hc : (d:ℝ) < δ*Fintype.card V+1 := Nat.ceil_lt_add_one (by positivity)
    have hδc : δ ≤ εc/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hδc hN]
  have hdiag : ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using
      (mem_sdiff.mp (mem_sdiff.mp he).1).1)
  have hm := Envelope.two_card_le_card_mul_degree U hdiag hdU
  obtain ⟨q,hwin,hqdeg⟩ := hW (Fintype.card V) U.card d
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    (by omega) hdε
  obtain ⟨Q,hQ,hQR,hrem,hQphys,hQl,hQg⟩ :=
    joint_monitored_stock_transition H F D DR P R hD hR hXR hphys
      hPack hPS hSupply d q (by simpa only [S,U] using hdU)
      (by simpa only [S,U] using hwin) bad loc full L τ τ hL.le
      hloc hfull (by simpa only [S,U] using hLocal)
      (by simpa only [S,U] using hGlobal)
  exact ⟨Q,hQ,hQR,hrem,hQphys,d,q,by simpa only [one_mul] using hqdeg,hQl,hQg⟩

end TypedTriangle.StockEntry
