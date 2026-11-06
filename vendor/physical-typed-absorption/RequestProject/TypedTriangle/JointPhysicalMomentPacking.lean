/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ProtectedLocalizedMoments
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ProtectedNibble
open LocalizedCover

/-- One protected packing controls BOTH the localized stratum tests at n|Z|
and the full tests at n^2. Its index budget counts both families together.
The global tests are not asserted to annihilate physical triangles. -/
theorem joint_physical_moment_packing {I : Type} (F : Set (Multiset I))
    (C α η τ L : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
        (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ),
        ((Fintype.card κ+Fintype.card ι:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
        (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card) ∧
          ∀ j, |edgeSum (full j) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*(Fintype.card V:ℝ)^2 := by
  obtain ⟨ε,hε,n₀,hpack⟩ := localized_physical_moment_packing F C α η τ L h q hC hα hη hτ hL
  refine ⟨ε,hε,n₀,?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ ι _ _ bad loc full hcard hloc hfull
  let bad' : κ ⊕ ι → Finset V := Sum.elim bad (fun _ => univ)
  let lam : κ ⊕ ι → Sym2 V → ℝ := Sum.elim loc full
  have hcount : (Fintype.card (κ ⊕ ι):ℝ) ≤ (Fintype.card V:ℝ)^q := by
    simpa only [Fintype.card_sum] using hcard
  have htri : ∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad' k).card := by
    intro k T hT
    cases k with
    | inl k => exact hloc k T hT
    | inr j => simpa [lam,bad'] using hfull j T hT
  obtain ⟨P,hP,hDis,hPhys,hSparse,hQuota⟩ :=
    hpack H φ R D d hn hφ h2 h3 h4 hD hdeg hd (κ ⊕ ι) bad' lam hcount htri
  refine ⟨P,hP,hDis,hPhys,hSparse,fun k => hQuota (.inl k),?_⟩
  intro j
  have hh := hQuota (.inr j)
  simpa [lam,bad',pow_two,mul_assoc] using hh

end TypedTriangle.ProtectedNibble
