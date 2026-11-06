/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSharedCorePreparation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference
variable {V I : Type*} [Fintype V]

/-- Literal raw weights on the actual membership subtype; normalization is by
the sampling probability, not an asserted exact seed on the induced graph. -/
def sampledWeights (φ : Finset V → ℝ) (W : Finset V) (q : ℝ)
    (T : Finset {v // v ∈ W}) : ℝ := φ (T.map (Function.Embedding.subtype _))/q

theorem sampled_boundary (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (W : Finset V) (q : ℝ)
    (u v : {x // x ∈ W}) (huv : u ≠ v) :
    bdry (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)
      F (sampledWeights φ W q) s(u,v) = S07V48.sampW H.G H.lab F φ W u.1 v.1/q := by
  let J : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let μ : Finset {x // x ∈ W} → ℝ := fun T => φ (T.map (Function.Embedding.subtype _))
  have hs := S07V48.sum_compW_eq_load J.G J.lab F μ huv
  have hsets : univ.filter (fun T => SparseEdge.IsAllowed J.G J.lab F T ∧
      s(u,v) ∈ SparseEdge.triEdges T) = triOn J F s(u,v) := by
    ext T
    simp only [triOn,allowed,mem_filter,mem_univ,true_and]
    rfl
  rw [hsets] at hs
  calc
    _ = (∑ T ∈ triOn J F s(u,v), μ T)/q := by
      rw [bdry_eq_sum_triOn,sum_div]
      rfl
    _ = S07V48.subSum H.G H.lab F φ W u v/q := by rw [←hs]; rfl
    _ = _ := by rw [S07V48.subSum_eq]

/-- Convert the profile already produced on the SAME W to the exact input
interface of the approximate-seed nibble and the dense-reference constructor. -/
theorem sampled_raw_profile {H : Host V I} {F : Set (Multiset I)}
    {φ : Finset V → ℝ} {C q ξ : ℝ} (hφ : IsDiffuseSeed H F C φ)
    (hC : 0 < C) (hq : 0 < q) (W : Finset V)
    (hWlo : q*Fintype.card V/2 ≤ W.card) (hWhi : (W.card:ℝ) < 2*q*Fintype.card V)
    (hraw : ∀ u v, H.G.Adj u v → |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ξ) :
    let J : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    (∀ T, IsAllowed J F T →
      (1/(2*C))/Fintype.card {x // x ∈ W} ≤ sampledWeights φ W q T ∧
        sampledWeights φ W q T ≤ (2*C)/Fintype.card {x // x ∈ W}) ∧
    ∀ e ∈ edges J, |bdry J F (sampledWeights φ W q) e-1| ≤ ξ := by
  let J : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  constructor
  · intro T hT
    have hLift : SparseEdge.IsAllowed H.G H.lab F (T.map (Function.Embedding.subtype _)) :=
      (S07V48.isAllowed_subtype_iff T).mp hT
    have hh := S07V48.coeff_window (CorePaid.diffuse_seed_for_sample hφ) hC hq
      (by norm_num : (0:ℝ) < 2) hWlo hWhi hLift
    simpa only [Fintype.card_coe,div_div,sampledWeights] using hh
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have ha : J.G.Adj u v := by simpa only [edges,mem_filter,mem_univ,true_and,
        SimpleGraph.mem_edgeSet] using he
      rw [sampled_boundary H F φ W q u v ha.ne]
      exact hraw u.1 v.1 ha

end TypedTriangle.RawReference
