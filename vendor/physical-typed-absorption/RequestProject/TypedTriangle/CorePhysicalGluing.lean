/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreRealPairing
public import RequestProject.TypedTriangle.NativeCoreKernel
public import RequestProject.TypedTriangle.NestedVertexQuotients
public import RequestProject.S07V39.PhysicalGluing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CoreMonitor
open CorePayment
variable {V I : Type*} [Fintype V]

lemma deleted_core_local_lift (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    {x : Sym2 (Survivors outer) → ℤ}
    (hx : x ∈ Composition.localProfile
      (S07V39.delG (restrictedHost H outer).G (bad.subtype (· ∉ outer)))
      (restrictedHost H outer).lab F) :
    edgeZeroExtend outer x ∈ Composition.localProfile (S07V39.delG H.G bad) H.lab F := by
  have heq : restrictedHost (vertexDeleted H bad) outer =
      (⟨S07V39.delG (restrictedHost H outer).G (bad.subtype (· ∉ outer)),
        (restrictedHost H outer).lab⟩ : Host (Survivors outer) I) := by
    rw [restrictedHost_vertexDeleted]
    rfl
  have hc : x ∈ localGroup (restrictedHost (vertexDeleted H bad) outer) F := by
    rw [heq,localGroup_eq_localProfile]
    exact hx
  have hext := edgeZeroExtend_mem_localGroup (vertexDeleted H bad) F outer hc
  have hh := localGroup_mono (vertexDeleted_le (vertexDeleted H bad) outer) rfl hext
  exact hh

def deletedCoreMap (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V) :
    Composition.localProfile (S07V39.delG (restrictedHost H outer).G (bad.subtype (· ∉ outer)))
      (restrictedHost H outer).lab F →ₗ[ℤ]
    Composition.localProfile (S07V39.delG H.G bad) H.lab F where
  toFun x := ⟨edgeZeroExtend outer x.1,deleted_core_local_lift H F outer bad x.2⟩
  map_add' _ _ := Subtype.ext ((edgeZeroExtend outer).map_add _ _)
  map_smul' _ _ := Subtype.ext ((edgeZeroExtend outer).map_smul _ _)

/-- Physical localization with a genuine core subtype. The bounded functionals
are inputs to this gluing lemma; their native bank construction is separate.
The actual weights, sign matching and row potential are constructed. -/
theorem core_physical_gluing (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    {β A : ℝ} {h : ℕ} (hβ : 0 < β) (hA : 0 ≤ A)
    (h3 : CommonNbrCond (restrictedHost H outer) F β)
    (h4 : HingeCond (restrictedHost H outer) F β h)
    (hn : S07V25.n1Of β ≤ Fintype.card (Survivors outer))
    (hbad : ((bad.subtype (· ∉ outer)).card:ℝ) ≤ S07V37.delOf β h*Fintype.card (Survivors outer))
    (f : Composition.localProfile (restrictedHost H outer).G (restrictedHost H outer).lab F →ₗ[ℤ] ℝ)
    (f0 : Composition.localProfile (S07V39.delG H.G bad) H.lab F →ₗ[ℤ] ℝ)
    (hf : ∀ x, |f x| ≤ A*∑ e, |(((x : Sym2 (Survivors outer) → ℤ) e):ℝ)|)
    (hf0 : ∀ x, |f0 x| ≤ A*∑ e, |(((x : Sym2 V → ℤ) e):ℝ)|)
    (hagree : ∀ x, f (Submodule.inclusion (S07V39.localProfile_delG_le (restrictedHost H outer).G
      (bad.subtype (· ∉ outer))) x) = f0 (deletedCoreMap H F outer bad x))
    (hann : ∀ x (hx : x ∈ SparseEdge.lattice (S07V39.delG H.G bad) H.lab F),
      f0 ⟨x,Composition.lattice_le_localProfile _ _ _ hx⟩ = 0) :
    ∃ lam : Sym2 V → ℝ, (∀ e, |lam e| ≤ S07V39.glueConst β A) ∧
      (∀ x : Composition.localProfile (restrictedHost H outer).G (restrictedHost H outer).lab F,
        ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ) = f x) ∧
      (∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e = 0) ∧
      ∀ T, IsAllowed H F T →
        |∑ e ∈ triEdges T, lam e| ≤ 3*S07V39.glueConst β A*(T∩bad).card := by
  let K := restrictedHost H outer
  let D := bad.subtype (· ∉ outer)
  obtain ⟨lamH,hH,hrepH⟩ := S07V38.bounded_extension _ f hA hf
  obtain ⟨lam0,h0,hrep0⟩ := S07V38.bounded_extension _ f0 hA hf0
  let lam0K : Sym2 (Survivors outer) → ℝ := fun e => lam0 (edgeLift outer e)
  have hJ : ∀ x : Sym2 (Survivors outer) → ℤ,
      ComponentRows.IsLocalProfile (S07V39.delG K.G D) K.lab F x →
      ∑ e : S07V36.NCol (S07V39.delG K.G D) K.lab F, lamH e.1*(x e.1:ℝ) =
        ∑ e : S07V36.NCol (S07V39.delG K.G D) K.lab F, lam0K e.1*(x e.1:ℝ) := by
    intro x hx
    rw [S07V39.sum_ncol_profile hx lamH,S07V39.sum_ncol_profile hx lam0K]
    have h₁ := hrepH (Submodule.inclusion (S07V39.localProfile_delG_le K.G D) ⟨x,hx⟩)
    have h₂ := hrep0 (deletedCoreMap H F outer bad ⟨x,hx⟩)
    change (∑ e, lam0 e*(edgeZeroExtend outer x e:ℝ)) = _ at h₂
    rw [pairing_zeroExtend] at h₂
    change (∑ e, lamH e*(x e:ℝ)) = _ at h₁
    change (∑ e, lam0K e*(x e:ℝ)) = _ at h₂
    rw [h₁,h₂]
    exact hagree ⟨x,hx⟩
  obtain ⟨t,ht,htb⟩ := S07V39.matching_potential_delG hβ h3 hbad
    (fun e => lam0K e.1) (fun e => lamH e.1) hA (fun e => h0 _) (fun e => hH _) hJ
  let Tb := (6/β^2+1)*(2*A)
  have hTb : 0 ≤ Tb := by positivity
  let p : Sym2 (Survivors outer) → ℝ := S07V39.rowField K.G K.lab F (S07V39.liftPot K.G K.lab F D t)
  let S : Set (Sym2 (Survivors outer)) := {e | S07V36.IsNCol K.G K.lab F e}
  have hp : ∀ e, |p e| ≤ 2*Tb := fun e =>
    S07V39.rowField_abs_le _ hTb (S07V39.liftPot_abs_le t hTb htb) e
  have hmatch : ∀ e ∈ S, (∀ v ∈ edgeLift outer e, v ∉ bad) → lamH e-p e=lam0 (edgeLift outer e) := by
    intro e he hav
    have havK : ∀ v ∈ e, v ∉ D := by
      intro v hv
      exact fun hvD => hav v.1 (Sym2.mem_map.mpr ⟨v,hv,rfl⟩) (mem_subtype.mp hvD)
    have heG : e ∈ (S07V39.delG K.G D).edgeSet := by
      have hE := S07V38.ncol_mem_edges he
      induction e using Sym2.ind with
      | _ u v =>
        change (S07V39.delG K.G D).Adj u v
        have hAdj : K.G.Adj u v := by simpa only [SparseEdge.edges,mem_filter,mem_univ,true_and,SimpleGraph.mem_edgeSet] using hE
        exact ⟨hAdj,havK u (by simp),havK v (by simp)⟩
    exact S07V39.glue_overlap (G:=K.G) hβ h3 h4 hn hbad lamH lam0K t ht he heG
  let lam := glued outer bad S lamH p lam0
  have hconst : S07V39.glueConst β A = A+2*Tb := by dsimp [S07V39.glueConst,Tb]; ring
  have hbound : ∀ e, |lam e| ≤ S07V39.glueConst β A := by
    intro e
    rw [hconst]
    exact glued_bound outer bad S lamH p lam0 hA (by positivity) hH hp h0 e
  have hrep : ∀ x : Composition.localProfile K.G K.lab F,
      ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ)=f x := by
    intro x
    rw [glued_pairing outer bad S lamH p lam0 x.1
      (S07V38.localProfile_supp x.2) (S07V39.rowField_pairing_zero _ x.2)]
    exact hrepH x
  have htri : ∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e=0 := by
    intro T hT
    have hav := (S07V39.allowed_delG_iff.mp hT).2
    have heq : ∀ e ∈ triEdges T, lam e=lam0 e := by
      intro e he
      apply glued_agrees_away outer bad S lamH p lam0 hmatch e
      intro v hv
      exact hav v (Finset.mem_sym2_iff.mp (mem_filter.mp he).1 v hv)
    rw [sum_congr rfl heq]
    exact S07V39.triangle_sum_zero lam0 f0 hrep0 hann hT
  refine ⟨lam,hbound,hrep,htri,?_⟩
  intro T hT
  apply triangle_monitor_bound lam bad (S07V39.glueConst β A) (by rw [hconst]; positivity) hbound T hT.1
  intro hd
  exact htri T (S07V39.allowed_delG_iff.mpr ⟨hT,fun v hv hb => disjoint_left.mp hd hv hb⟩)
end TypedTriangle.CoreMonitor
