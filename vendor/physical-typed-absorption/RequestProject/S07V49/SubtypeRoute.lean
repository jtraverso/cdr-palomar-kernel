/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.EdgeRoutes
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §2bis — routes on the TRUE surviving subtype host

For `U : Finset V` and a host `K` (here `K = G \ B`, `U = W ∖ Z`), the true subtype host is
`K.comap val` on `{a // a ∈ U}` (no isolated deleted vertices). Its link at `v` is the
restriction of the ambient link (`link_comap_adj`), walks of the ambient link supported in `U`
lift (`lift_walk`), and the edge-deleted contract gives, for every residual admissible pair
with endpoints in `U`, a path of length exactly `t` in the link of the true subtype host
(`subtype_route`).
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25 S07V45 S07V48

variable {V I : Type*} [Fintype V] [DecidableEq V] {lab : V → I} {F : Set (Multiset I)}

omit [Fintype V] in
/-- the link of the true subtype host is the restriction of the ambient link -/
theorem link_comap_adj {K : SimpleGraph V} {U : Finset V} {v x y : {a // a ∈ U}} :
    (link (K.comap Subtype.val) (lab ∘ Subtype.val) F v).Adj x y ↔
      (link K lab F v.1).Adj x.1 y.1 := by
  constructor
  · rintro ⟨hne, hA⟩
    refine ⟨fun h => hne (Subtype.ext h), ?_⟩
    rw [isAllowed_subtype_iff] at hA
    convert hA using 1
    ext z; simp
  · rintro ⟨hne, hA⟩
    refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
    rw [isAllowed_subtype_iff]
    convert hA using 1
    ext z; simp

omit [Fintype V] in
/-- ambient link walks supported in `U` lift to the true subtype host -/
theorem lift_walk {K : SimpleGraph V} {U : Finset V} (v : {a // a ∈ U}) :
    ∀ {x y : V} (p : (link K lab F v.1).Walk x y) (hx : x ∈ U) (hy : y ∈ U),
      (∀ z ∈ p.support, z ∈ U) →
      ∃ q : (link (K.comap Subtype.val) (lab ∘ Subtype.val) F v).Walk ⟨x, hx⟩ ⟨y, hy⟩,
        q.support.map Subtype.val = p.support
  | _, _, .nil, hx, hy, _ => ⟨.nil, by simp⟩
  | _, _, @SimpleGraph.Walk.cons _ _ a m b h p, hx, hy, hs => by
    have hm : m ∈ U := hs m (by simp)
    obtain ⟨q, hq⟩ := lift_walk v p hm hy (fun z hz => hs z (by simp [hz]))
    have hadj : (link (K.comap Subtype.val) (lab ∘ Subtype.val) F v).Adj ⟨a, hx⟩ ⟨m, hm⟩ :=
      link_comap_adj.2 h
    exact ⟨.cons hadj q, by simp [hq]⟩

/-- **routes on the true surviving subtype host**, from any core path contract -/
theorem subtype_route {K : SimpleGraph V} {U : Finset V} {t : ℕ}
    (hCt : CorePathContract K lab F U t) (v x y : {a // a ∈ U})
    (hxy : OrigAdm K lab F v.1 x.1 y.1) :
    ∃ q : (link (K.comap Subtype.val) (lab ∘ Subtype.val) F v).Walk x y,
      q.length = t ∧ q.IsPath := by
  obtain ⟨p, hpl, hpp, hpU⟩ := hCt v.1 v.2 x.1 y.1 hxy
  have hs : ∀ z ∈ p.support, z ∈ U := by
    intro z hz
    obtain ⟨k, rfl, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · rcases lt_or_eq_of_le hk with hlt | heq
      · exact hpU k h0 (hpl ▸ hlt)
      · rw [heq, SimpleGraph.Walk.getVert_length]; exact y.2
  obtain ⟨q, hq⟩ := lift_walk v p x.2 y.2 hs
  have hlen : q.length = p.length := by
    have h1 := congrArg List.length hq
    rw [List.length_map, SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_support] at h1
    omega
  refine ⟨q, hlen.trans hpl, ?_⟩
  rw [SimpleGraph.Walk.isPath_def]
  have : (q.support.map Subtype.val).Nodup := by rw [hq]; exact hpp.support_nodup
  exact this.of_map _

end S07V49
