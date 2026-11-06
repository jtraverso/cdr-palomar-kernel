/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LocalizedCoverDown
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.LocalizedCover
variable {V I : Type*} [Fintype V]

/-- One actual protected cover-down simultaneously preserves ambient integer
physicality and the localized bound for every monitor. The residual is the
unused part of X, whose full size is retained in the identity. -/
theorem physical_monitored_cover_down (H : Host V I) (F : Set (Multiset I))
    (U X B : Finset (Sym2 V)) (hUX : Disjoint U X) (hUB : Disjoint U B)
    (hU : ∀ e ∈ U, ¬e.IsDiag) (hUphys : IsPhysical H F U) (hXphys : IsPhysical H F X)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d q f : ℕ} (hdeg : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d)
    (hBdeg : ∀ v, (B.filter (fun e => v ∈ e)).card ≤ f)
    (hcand : ∀ e ∈ U, U.card+q*(2*d+4*q+2*f) < q*(Cand e).card) :
    ∃ P : Finset (Finset V), IsPacking H F P ∧ U ⊆ P.biUnion triEdges ∧
      P.biUnion triEdges ⊆ U∪X ∧ Disjoint (P.biUnion triEdges) B ∧
      (∀ v, ((P.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ 2*d+2*q) ∧
      IsPhysical H F (X\P.biUnion triEdges) ∧
      ∀ (lam : Sym2 V → ℝ) (bad : Finset V) (L E0 : ℝ), 0 ≤ L →
        (∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) →
        |edgeSum lam U| ≤ E0 →
        |edgeSum lam (X\P.biUnion triEdges)-edgeSum lam X| ≤
          E0+(3*L*bad.card)*(2*d+2*q:ℕ)/2 := by
  obtain ⟨P,hP,hCov,hSub,hDis,hDeg⟩ :=
    cover_down_protected H F U X B hUX hUB hU Cand hCand hdeg hBdeg hcand
  have hEq : (U∪X)\P.biUnion triEdges = X\P.biUnion triEdges := by
    ext e
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hu|hx,hn⟩
      · exact False.elim (hn (hCov hu))
      · exact ⟨hx,hn⟩
    · rintro ⟨hx,hn⟩
      exact ⟨Or.inr hx,hn⟩
  have hPhys : IsPhysical H F (X\P.biUnion triEdges) := by
    rw [←hEq]
    exact isPhysical_sdiff (isPhysical_union hUphys hXphys hUX)
      (isPhysical_of_isDecomposition hP.isDecomposition) hSub
  refine ⟨P,hP,hCov,hSub,hDis,hDeg,hPhys,?_⟩
  intro lam bad L E0 hL htri hUmon
  exact localized_cover_down_entry U X P hP hUX hCov hSub (2*d+2*q:ℕ) L E0 hL
    (fun v => by exact_mod_cast hDeg v) bad lam htri hUmon
end TypedTriangle.LocalizedCover
