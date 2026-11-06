module
public import RequestProject.TypedTriangle.PaschStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def mapConfiguration (e : V ↪ W) (S : Finset (Finset V)) : Finset (Finset W) :=
  S.map (Finset.mapEmbedding e).toEmbedding

theorem mem_mapConfiguration {e : V ↪ W} {S : Finset (Finset V)} {T : Finset W} :
    T ∈ mapConfiguration e S ↔ ∃ A ∈ S, A.map e = T := by
  simp only [mapConfiguration,mem_map]
  rfl

theorem support_mapConfiguration (e : V ↪ W) (S : Finset (Finset V)) :
    (mapConfiguration e S).biUnion id = (S.biUnion id).map e := by
  ext w
  constructor
  · intro hw
    obtain ⟨T,hT,hwT⟩ := mem_biUnion.mp hw
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hT
    obtain ⟨v,hv,hvw⟩ := mem_map.mp hwT
    exact mem_map.mpr ⟨v,mem_biUnion.mpr ⟨A,hA,hv⟩,hvw⟩
  · intro hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    obtain ⟨A,hA,hvA⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨A.map e,mem_mapConfiguration.mpr ⟨A,hA,rfl⟩,
      mem_map.mpr ⟨v,hvA,rfl⟩⟩

theorem filter_mapConfiguration (e : V ↪ W) (S : Finset (Finset V)) (v : V) :
    (mapConfiguration e S).filter (fun T => e v ∈ T) =
      mapConfiguration e (S.filter (fun T => v ∈ T)) := by
  unfold mapConfiguration
  rw [filter_map]
  congr 1
  apply filter_congr
  intro A _
  change (e v ∈ A.map e ↔ v ∈ A)
  exact mem_map' e

theorem IsPasch.mapEmbedding {S : Finset (Finset V)} (hS : IsPasch S) (e : V ↪ W) :
    IsPasch (mapConfiguration e S) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [mapConfiguration,card_map,hS.1]
  · intro T hT
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hT
    rw [card_map,hS.2.1 A hA]
  · rw [support_mapConfiguration,card_map,hS.2.2.1]
  · intro w hw
    rw [support_mapConfiguration] at hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    rw [filter_mapConfiguration,mapConfiguration,card_map]
    exact hS.2.2.2.1 v hv
  · intro A hA B hB hAB
    obtain ⟨A',hA',rfl⟩ := mem_mapConfiguration.mp hA
    obtain ⟨B',hB',rfl⟩ := mem_mapConfiguration.mp hB
    have hne : A' ≠ B' := fun he => hAB (congrArg (fun T => T.map e) he)
    rw [← map_inter,card_map]
    exact hS.2.2.2.2 hA' hB' hne

/-- The standard 2 by 2 by 2 grid, in consecutive coordinate pairs. -/
def gridPasch : Finset (Finset (Fin 6)) :=
  {{0,2,4},{0,3,5},{1,2,5},{1,3,4}}

theorem gridPasch_isPasch : IsPasch gridPasch := by decide

theorem gridPasch_support : gridPasch.biUnion id = univ := by decide

def gridImage (f : Fin 6 → V) : Finset (Finset V) :=
  gridPasch.image (fun T => T.image f)

theorem gridImage_eq_map (f : Fin 6 → V) (hf : Function.Injective f) :
    gridImage f = mapConfiguration ⟨f,hf⟩ gridPasch := by
  simp only [gridImage,mapConfiguration,map_eq_image]
  congr 1
  funext T
  change T.image f = T.map ⟨f,hf⟩
  rw [map_eq_image]
  rfl

theorem gridImage_isPasch (f : Fin 6 → V) (hf : Function.Injective f) : IsPasch (gridImage f) := by
  rw [gridImage_eq_map f hf]
  exact gridPasch_isPasch.mapEmbedding ⟨f,hf⟩

theorem gridImage_support (f : Fin 6 → V) (hf : Function.Injective f) :
    (gridImage f).biUnion id = univ.image f := by
  rw [gridImage_eq_map f hf,support_mapConfiguration,gridPasch_support,map_eq_image]
  rfl

/-- At most 6^6 injective labelings can represent a given six-vertex
configuration. The coarser bound avoids imposing an orientation. -/
theorem gridImage_fiber_card_le [Fintype V] (S : Finset (Finset V))
    (hS : (S.biUnion id).card = 6) :
    (univ.filter (fun f : Fin 6 → V => Function.Injective f ∧ gridImage f = S)).card ≤ 6^6 := by
  let A := univ.filter (fun f : Fin 6 → V => Function.Injective f ∧ gridImage f = S)
  have hRange (f : {f // f ∈ A}) (i : Fin 6) : f.val i ∈ S.biUnion id := by
    obtain ⟨hf,heq⟩ := (mem_filter.mp f.property).2
    rw [← heq,gridImage_support f.val hf]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  let g : {f // f ∈ A} → (Fin 6 → {v // v ∈ S.biUnion id}) := fun f i => ⟨f.val i,hRange f i⟩
  have hg : Function.Injective g := by
    intro f h heq
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun heq i)
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,hS] using hc

#print axioms support_mapConfiguration
#print axioms IsPasch.mapEmbedding
#print axioms gridPasch_isPasch
#print axioms gridImage_isPasch
#print axioms gridImage_fiber_card_le
end TypedTriangle.Pasch
