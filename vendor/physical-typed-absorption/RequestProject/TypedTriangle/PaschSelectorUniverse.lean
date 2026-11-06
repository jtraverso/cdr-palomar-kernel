module
public import RequestProject.Selectors.SimulLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.Pasch
open SelSimul SelBridge
variable {V I : Type*} [Fintype V] [DecidableEq V]

def selectorTriangle (v : V) (e : Sym2 V) : Finset V := insert v e.toFinset

/-- A fixed universe for every later selector demand: all permitted base edges,
not the union of choices over demands. -/
def selectorUniverse (Z : Finset V) (σ : V → LocalSel V) : Finset (Finset V) :=
  Z.biUnion (fun v => (σ v).P.image (selectorTriangle v))

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {X B0 : SimpleGraph V} [DecidableRel X.Adj] [DecidableRel B0.Adj]
  {Z : Finset V} {Adm : V → Finset V → Prop} {A q : ℕ} {σ : V → LocalSel V}

theorem selectorUniverse_allowed (h : SimulFamily G lab F X B0 Z Adm A q σ) :
    ∀ T ∈ selectorUniverse Z σ, SparseEdge.IsAllowed G lab F T := by
  intro T hT
  obtain ⟨v,hv,hT⟩ := mem_biUnion.mp hT
  obtain ⟨e,he,rfl⟩ := mem_image.mp hT
  obtain ⟨x,y,rfl,_,hAllowed⟩ := (h.valid v hv).permitted he
  simpa only [selectorTriangle,Sym2.toFinset_mk_eq] using hAllowed

theorem selector_modes_subset_universe (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (L : Finset (Sym2 V)) (hAdm : ∀ v ∈ Z, Adm v (demand X L v)) :
    (packing X Z σ L).image (fun p => selectorTriangle p.1 p.2) ⊆ selectorUniverse Z σ := by
  intro T hT
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hT
  obtain ⟨v,hv,hp⟩ := mem_biUnion.mp hp
  obtain ⟨e,he,rfl⟩ := mem_image.mp hp
  have heP : e ∈ (σ v).P :=
    ((h.valid v hv).modes _ (filter_subset _ _) (hAdm v hv)).1 he
  exact mem_biUnion.mpr ⟨v,hv,mem_image.mpr ⟨e,heP,rfl⟩⟩

private theorem pair_at_root_subset (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {a b : V} (haZ : a ∈ Z) (hab : a ≠ b) :
    (selectorUniverse Z σ).filter (fun T => a ∈ T ∧ b ∈ T) ⊆
      ((σ a).P.filter (fun e => b ∈ e)).image (selectorTriangle a) := by
  intro T hT
  obtain ⟨hUniverse,ha,hb⟩ := mem_filter.mp hT
  obtain ⟨v,hv,hT⟩ := mem_biUnion.mp hUniverse
  obtain ⟨e,he,rfl⟩ := mem_image.mp hT
  have hav : a = v := by
    rcases mem_insert.mp ha with hav | ha
    · exact hav
    · exact False.elim ((h.base_vert_not_Z hZ hv he (Sym2.mem_toFinset.mp ha)) haZ)
  subst v
  have hbE : b ∈ e := by
    rcases mem_insert.mp hb with hba | hb
    · exact False.elim (hab hba.symm)
    · exact Sym2.mem_toFinset.mp hb
  exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hbE⟩,rfl⟩

private theorem pair_at_root_card_le (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') {a b : V} (haZ : a ∈ Z) (hab : a ≠ b) :
    ((selectorUniverse Z σ).filter (fun T => a ∈ T ∧ b ∈ T)).card ≤ 60 := by
  calc
    _ ≤ (((σ a).P.filter (fun e => b ∈ e)).image (selectorTriangle a)).card :=
      card_le_card (pair_at_root_subset h hZ haZ hab)
    _ ≤ ((σ a).P.filter (fun e => b ∈ e)).card := card_image_le
    _ ≤ 60 := (h.valid a haZ).deg_le b

private theorem base_of_outside_pair (h : SimulFamily G lab F X B0 Z Adm A q σ)
    {a b v : V} (haZ : a ∉ Z) (hbZ : b ∉ Z) (hab : a ≠ b) (hv : v ∈ Z)
    {e : Sym2 V} (ha : a ∈ selectorTriangle v e) (hb : b ∈ selectorTriangle v e) :
    e = s(a,b) := by
  have haE : a ∈ e := by
    rcases mem_insert.mp ha with hav | ha
    · exact False.elim (haZ (hav.symm ▸ hv))
    · exact Sym2.mem_toFinset.mp ha
  have hbE : b ∈ e := by
    rcases mem_insert.mp hb with hbv | hb
    · exact False.elim (hbZ (hbv.symm ▸ hv))
    · exact Sym2.mem_toFinset.mp hb
  exact Sym2.eq_of_ne_mem hab haE hbE (by simp) (by simp)

/-- The universe of every possible selector mode has pair-codegree at most 60.
Input edges can recur across demands, but each rooted base graph has degree 60
and bases belonging to distinct roots are disjoint. -/
theorem selectorUniverse_pair_degree_le (h : SimulFamily G lab F X B0 Z Adm A q σ)
    (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') (a b : V) (hab : a ≠ b) :
    ((selectorUniverse Z σ).filter (fun T => a ∈ T ∧ b ∈ T)).card ≤ 60 := by
  by_cases haZ : a ∈ Z
  · exact pair_at_root_card_le h hZ haZ hab
  by_cases hbZ : b ∈ Z
  · have hh := pair_at_root_card_le h hZ hbZ hab.symm
    have heq : (selectorUniverse Z σ).filter (fun T => a ∈ T ∧ b ∈ T) =
        (selectorUniverse Z σ).filter (fun T => b ∈ T ∧ a ∈ T) := by
      ext T
      simp only [mem_filter,and_comm]
    rw [heq]
    exact hh
  have hOne : ((selectorUniverse Z σ).filter (fun T => a ∈ T ∧ b ∈ T)).card ≤ 1 := by
    apply card_le_one.mpr
    intro S hS T hT
    obtain ⟨hS,haS,hbS⟩ := mem_filter.mp hS
    obtain ⟨hT,haT,hbT⟩ := mem_filter.mp hT
    obtain ⟨v,hv,hS⟩ := mem_biUnion.mp hS
    obtain ⟨e,he,rfl⟩ := mem_image.mp hS
    obtain ⟨w,hw,hT⟩ := mem_biUnion.mp hT
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hT
    have heq := base_of_outside_pair h haZ hbZ hab hv haS hbS
    have hfeq := base_of_outside_pair h haZ hbZ hab hw haT hbT
    have hvw : v = w := by
      by_contra hne
      have hDis := h.disjP v hv w hw hne
      have hef : e = f := heq.trans hfeq.symm
      exact disjoint_left.mp hDis he (hef.symm ▸ hf)
    subst w
    rw [heq,hfeq]
  omega

/-- All candidate triangles together are no more numerous than the fixed fuel
edges. In particular the existing sparse-fuel budget controls their total size. -/
theorem selectorUniverse_card_le_fuel (h : SimulFamily G lab F X B0 Z Adm A q σ) :
    (selectorUniverse Z σ).card ≤ (fuelU Z σ).card := by
  calc
    _ ≤ ∑ v ∈ Z, ((σ v).P.image (selectorTriangle v)).card := card_biUnion_le
    _ ≤ ∑ v ∈ Z, (σ v).P.card := sum_le_sum (fun _ _ => card_image_le)
    _ = (Z.biUnion (fun v => (σ v).P)).card :=
      (card_biUnion (fun v hv w hw hne => h.disjP v hv w hw hne)).symm
    _ ≤ (fuelU Z σ).card := by
      apply card_le_card
      intro e he
      obtain ⟨v,hv,he⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨v,hv,mem_union_left _ he⟩

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.selectorUniverse_allowed
#print axioms TypedTriangle.Pasch.selector_modes_subset_universe
#print axioms TypedTriangle.Pasch.selectorUniverse_pair_degree_le
#print axioms TypedTriangle.Pasch.selectorUniverse_card_le_fuel
