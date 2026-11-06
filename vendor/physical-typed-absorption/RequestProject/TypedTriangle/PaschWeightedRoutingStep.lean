module
public import RequestProject.Selectors.GreedyEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelEmbed SelSubdiv
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {α V : Type*} [DecidableEq α] [DecidableEq V]

/-- Install one prescribed retained walk in the actual subdivision routing.
This is the original routing step with its walk supplied explicitly, so a
weighted selection is retained rather than replaced by an existential choice. -/
theorem route_step_of_prescribed_walk [Fintype α]
    {H : SimpleGraph V} {φ : α → V} {src tgt : Sym2 α → α}
    {ℓ : ℕ} {Z0 : Finset V} {Q' : Finset (Sym2 α)} {e : Sym2 α}
    (heQ' : e ∉ Q') {t : Sym2 α → ℕ} {int : Sym2 α → ℕ → V}
    (hok : RouteOK H φ src tgt ℓ Z0 Q' t int)
    (w : H.Walk (φ (src e)) (φ (tgt e))) (hpath : w.IsPath)
    (t0 : ℕ) (ht0 : w.length = 2*t0+1) (hlen : w.length ≤ ℓ)
    (hsupp : ∀ z ∈ w.support, z ∉ forbidden φ Z0 Q' t int (φ (src e)) (φ (tgt e))) :
    RouteOK H φ src tgt ℓ Z0 (insert e Q')
      (Function.update t e t0) (Function.update int e (fun j => w.getVert j)) := by
  let a := φ (src e)
  let b := φ (tgt e)
  let Z := forbidden φ Z0 Q' t int a b
  have hints : ∀ e' ∈ Q', ∀ j, 1 ≤ j → j ≤ 2 * t e' → int e' j ∈ Z := by
    intro e' he' j h1 h2
    refine mem_union_right _ (mem_biUnion.mpr ⟨e', he', mem_image.mpr ⟨j, ?_, rfl⟩⟩)
    rw [mem_Icc]; exact ⟨h1, h2⟩
  have himg : ∀ x, φ x ≠ a → φ x ≠ b → φ x ∈ Z := by
    intro x ha hb
    refine mem_union_left _ (mem_union_right _ ?_)
    rw [mem_erase, mem_erase]
    exact ⟨hb, ha, mem_image_of_mem _ (mem_univ x)⟩
  have hZ0 : Z0 ⊆ Z := fun z hz => mem_union_left _ (mem_union_left _ hz)
  have hwZ : ∀ i, w.getVert i ∉ Z := fun i => hsupp _ (w.getVert_mem_support i)
  have hwinj : ∀ i i', i ≤ w.length → i' ≤ w.length → w.getVert i = w.getVert i' → i = i' :=
    fun i i' hi hi' h => hpath.getVert_injOn hi hi' h
  have hte : Function.update t e t0 e = t0 := Function.update_self ..
  have hie : Function.update int e (fun j => w.getVert j) e = fun j => w.getVert j :=
    Function.update_self ..
  have hto : ∀ e' ∈ Q', Function.update t e t0 e' = t e' := fun e' he' =>
    Function.update_of_ne (fun h => heQ' (by rw [← h]; exact he')) _ _
  have hio : ∀ e' ∈ Q', Function.update int e (fun j => w.getVert j) e' = int e' :=
    fun e' he' => Function.update_of_ne (fun h => heQ' (by rw [← h]; exact he')) _ _
  have hpv : ∀ j, j ≤ 2 * t0 + 1 →
      pv φ src tgt (Function.update t e t0) (Function.update int e (fun j => w.getVert j)) e j =
        w.getVert j := by
    intro j hj
    simp only [pv, hte, hie]
    split_ifs with h0 h1
    · subst h0; rw [SimpleGraph.Walk.getVert_zero]
    · subst h1; rw [← ht0, SimpleGraph.Walk.getVert_length]
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e1 he1 e2 he2 j j' h1 h2 h1' h2' h
    rcases mem_insert.mp he1 with h1e | he1 <;> rcases mem_insert.mp he2 with h2e | he2
    · rw [h1e] at h2 h ⊢; rw [h2e] at h2' h ⊢
      rw [hte] at h2 h2'
      rw [hie] at h
      exact ⟨rfl, hwinj j j' (by omega) (by omega) h⟩
    · rw [h1e] at h2 h; rw [hte] at h2; rw [hto e2 he2] at h2'
      rw [hie, hio e2 he2] at h
      beta_reduce at h
      exact absurd (h ▸ hints e2 he2 j' h1' h2') (hwZ j)
    · rw [h2e] at h2' h; rw [hto e1 he1] at h2; rw [hte] at h2'
      rw [hie, hio e1 he1] at h
      beta_reduce at h
      exact absurd (h ▸ hints e1 he1 j h1 h2) (hwZ j')
    · rw [hto e1 he1] at h2; rw [hto e2 he2] at h2'
      rw [hio e1 he1, hio e2 he2] at h
      exact hok.inj e1 he1 e2 he2 j j' h1 h2 h1' h2' h
  · intro e1 he1 j h1 h2 x
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte] at h2
      rw [hie]
      intro h
      beta_reduce at h
      by_cases hxa : φ x = a
      · rw [hxa] at h
        have := hwinj j 0 (by omega) (by omega) (h.trans (SimpleGraph.Walk.getVert_zero w).symm)
        omega
      by_cases hxb : φ x = b
      · rw [hxb] at h
        have := hwinj j _ (by omega) le_rfl (h.trans (SimpleGraph.Walk.getVert_length w).symm)
        omega
      exact hwZ j (h ▸ himg x hxa hxb)
    · rw [hto e1 he1] at h2; rw [hio e1 he1]
      exact hok.ne e1 he1 j h1 h2 x
  · intro e1 he1 j hj
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte] at hj
      rw [hpv j (by omega), hpv (j + 1) (by omega)]
      exact w.adj_getVert_succ (by omega)
    · rw [hto e1 he1] at hj
      rw [pv_congr φ src tgt (hto e1 he1) (hio e1 he1),
        pv_congr φ src tgt (hto e1 he1) (hio e1 he1)]
      exact hok.adj e1 he1 j hj
  · intro e1 he1
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte]; omega
    · rw [hto e1 he1]; exact hok.len e1 he1
  · intro e1 he1 j h1 h2
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hie]; exact fun h => hwZ j (hZ0 h)
    · rw [hto e1 he1] at h2; rw [hio e1 he1]
      exact hok.avoid e1 he1 j h1 h2

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.route_step_of_prescribed_walk
