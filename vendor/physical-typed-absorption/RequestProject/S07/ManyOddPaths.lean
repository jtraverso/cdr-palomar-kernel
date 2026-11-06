/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.WalkBound
public import RequestProject.S07.PathCount

@[expose] public section

/-!
# V24 / S07 §1 (1.1): many simple odd paths of ONE fixed length

**Interfaces (intermediate, produced by S03 §§4–6 from the original H3/H4; NOT new hypotheses
of T).** A component `K` of a link is modelled as a finite graph on a type `V` with:

* minimum degree `≥ c n` and maximum degree `≤ n`, where `n` is the AMBIENT host order;
* `|V| ≤ n` (a link lives inside the host);
* edge expansion with ambient normalisation: `κ n |S| ≤ cut(S)` for every `S` with
  `2|S| ≤ |V(K)|` (bipartite case), resp. the same for every `S ⊆ V × Bool` with
  `2|S| ≤ 2|V|` in the double cover `dcover K` (non-bipartite case, S03 (6.1)).

**Scaling.** Everything is normalised by the ambient `n`, not by `|V(K)|`: the minimum degree
forces `c n ≤ |V(K)| ≤ n`, so the two scales agree up to `c`. The proof uses `|V(H)| ≤ 2n`
for the graph `H` on which the spectral estimate runs (`H = K` or `H = dcover K`), and the
stationary mass of the endpoint is `dg y / vol(H) ≥ c n / (|V(H)| n) ≥ c / (2n)`.

**Results.**

* `walks_lower_core`: in a graph with a proper 2-colouring and the above premises,
  `A^(k+2)(x,y) ≥ c^(k+3) n^(k+1) / 2` for opposite colours and every odd `k` with
  `(1-κ²/2)^(2k) ≤ c^5/4`. Both exact eigen-directions `±1` are kept and handled.
* `many_odd_paths_bipartite`: constants `t` (odd, `≥ 3`), `a > 0`, `n₀` depending only on
  `(c, κ)` are produced BEFORE the host; then every bipartite component with the premises has
  `≥ a n^(t-1)` simple paths of length EXACTLY `t` between any two vertices of opposite sides.
* `many_odd_paths_nonbipartite`: same, with the expansion premise on the double cover, for
  EVERY pair of distinct vertices. The cover expansion is exactly what rules out an
  almost-bipartite obstruction (no bipartiteness assumption is needed or made: a bipartite `K`
  would have a disconnected cover, violating the premise).
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- core walk-count lower bound on a properly 2-coloured expander -/
theorem walks_lower_core (H : SimpleGraph V) [DecidableRel H.Adj] {c κ : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hκ1 : κ ≤ 1) {n : ℕ} (hn : 0 < n)
    (hmin : ∀ v, c * n ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ n)
    (hcard : Fintype.card V ≤ 2 * n)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ * n * S.card ≤ cutCount H S)
    (col : V → Bool) (hcol : ∀ v w, H.Adj v w → col v ≠ col w)
    (k : ℕ) (hk : Odd k) (hkb : ((1 - κ ^ 2 / 2) ^ 2) ^ k ≤ c ^ 5 / 4)
    (x y : V) (hxy : col x ≠ col y) :
    c ^ (k + 3) * (n : ℝ) ^ (k + 1) / 2 ≤ (H.adjMatrix ℝ ^ (k + 2)) x y := by
  set σ : V → ℝ := fun v => if col v then 1 else -1 with hσdef
  have hσ : ∀ v, σ v ^ 2 = 1 := by intro v; simp only [hσdef]; split_ifs <;> norm_num
  have hσadj : ∀ v w, H.Adj v w → σ w = -σ v := by
    intro v w h; have := hcol v w h; simp only [hσdef]
    cases hv : col v <;> cases hw : col w <;> simp_all
  have hσxy : σ y = -σ x := by
    simp only [hσdef]; cases hv : col x <;> cases hw : col y <;> simp_all
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set D : ℝ := c * n with hD
  have hDpos : 0 < D := mul_pos hc hnR
  have hDle : ∀ v, D ≤ dg H v := fun v => by rw [dg_eq_degree]; exact hmin v
  have hMle : ∀ v, dg H v ≤ n := fun v => by rw [dg_eq_degree]; exact_mod_cast hmax v
  have hdg : ∀ v, 0 < dg H v := fun v => lt_of_lt_of_le hDpos (hDle v)
  have hexpv := vol_expansion_of_count (H := H) (n := (n : ℝ)) hκ.le hMle hexp
  have hκ2 : κ ^ 2 < 2 := by nlinarith
  have hmain := main_term_sq hdg hκ.le hκ2 hexpv σ hσ hσadj hDpos hDle hMle x y hσxy k hk
  set P := (Pop H ^ (k + 2)) (dirac y) x
  set U := vol H univ
  have hc1 : c ≤ 1 := by
    have := (hmin x).trans (by exact_mod_cast hmax x : ((H.degree x : ℕ) : ℝ) ≤ n)
    nlinarith
  -- the error is at most c/(2n)
  have herr : ((1 - κ ^ 2 / 2) ^ 2) ^ k * (1 / D ^ 2) * (n / D) ≤ (c / (2 * n)) ^ 2 := by
    have e : (1 / D ^ 2) * (n / D) = 1 / (c ^ 3 * n ^ 2) := by
      rw [hD]; field_simp
    rw [mul_assoc, e]
    calc ((1 - κ ^ 2 / 2) ^ 2) ^ k * (1 / (c ^ 3 * n ^ 2)) ≤ c ^ 5 / 4 * (1 / (c ^ 3 * n ^ 2)) :=
          mul_le_mul_of_nonneg_right hkb (by positivity)
      _ = (c / (2 * n)) ^ 2 := by field_simp; ring
  have hsq := hmain.trans herr
  have hUle : U ≤ 2 * n * n := by
    calc U = ∑ v, dg H v := rfl
      _ ≤ ∑ _v : V, (n : ℝ) := Finset.sum_le_sum fun v _ => hMle v
      _ = Fintype.card V * n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 2 * n * n := by
          apply mul_le_mul_of_nonneg_right _ hnR.le; exact_mod_cast hcard
  have hUpos : 0 < U := by
    have : dg H y ≤ U := Finset.single_le_sum (fun v _ => dg_nonneg v) (mem_univ y)
    linarith [hdg y]
  have hstat : c / n ≤ 2 * dg H y / U := by
    rw [div_le_div_iff₀ hnR hUpos]
    have := hDle y
    nlinarith
  have hP : c / (2 * n) ≤ P := by
    by_contra hlt; push_neg at hlt
    have h1 : c / (2 * n) < 2 * dg H y / U - P := by
      have : c / (2 * n) = c / n - c / (2 * n) := by field_simp; ring
      linarith
    have h2 : 0 ≤ c / (2 * n) := by positivity
    nlinarith
  have hwalk := (Pop_pow_le_adj hdg hDpos hDle y (k + 2) x).2
  have hDk : 0 < D ^ (k + 2) := pow_pos hDpos _
  have := hP.trans hwalk
  rw [le_div_iff₀ hDk] at this
  calc c ^ (k + 3) * (n : ℝ) ^ (k + 1) / 2 = c / (2 * n) * D ^ (k + 2) := by
        rw [hD]; field_simp; ring
    _ ≤ _ := this

/-! ### Choice of the constants (before the host) -/

/-- an odd `k` with `((1-κ²/2)²)^k ≤ c^5/4` exists -/
lemma exists_odd_k {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ k : ℕ, Odd k ∧ ((1 - κ ^ 2 / 2) ^ 2) ^ k ≤ c ^ 5 / 4 := by
  set r := (1 - κ ^ 2 / 2) ^ 2
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by
    have h1 : 0 ≤ 1 - κ ^ 2 / 2 := by nlinarith
    have h2 : 1 - κ ^ 2 / 2 < 1 := by nlinarith
    calc r = (1 - κ ^ 2 / 2) ^ 2 := rfl
      _ < 1 := by nlinarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < c ^ 5 / 4 by positivity) hr1
  refine ⟨2 * j + 1, odd_two_mul_add_one j, ?_⟩
  calc r ^ (2 * j + 1) ≤ r ^ j := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    _ ≤ c ^ 5 / 4 := hj.le

/-- all the constants, from `(c, κ)` only -/
noncomputable def kOf (c κ : ℝ) : ℕ :=
  if h : 0 < min c 1 ∧ 0 < min κ 1 then
    Classical.choose (exists_odd_k h.1 h.2 (min_le_right κ 1))
  else 1

lemma kOf_spec {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    Odd (kOf c κ) ∧ ((1 - (min κ 1) ^ 2 / 2) ^ 2) ^ (kOf c κ) ≤ (min c 1) ^ 5 / 4 := by
  have h : 0 < min c 1 ∧ 0 < min κ 1 := ⟨lt_min hc one_pos, lt_min hκ one_pos⟩
  unfold kOf; rw [dif_pos h]
  exact Classical.choose_spec (exists_odd_k h.1 h.2 (min_le_right κ 1))

/-- from walk counts to path counts, with `|V| ≤ n` -/
lemma paths_from_walks (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} (hc : 0 < c)
    (k n : ℕ) (hn : 4 * (k + 2) ^ 2 / c ^ (k + 3) ≤ n) (hcard : Fintype.card V ≤ n)
    (x y : V) (hxy : x ≠ y)
    (hw : c ^ (k + 3) * (n : ℝ) ^ (k + 1) / 2 ≤ (G.adjMatrix ℝ ^ (k + 2)) x y) :
    c ^ (k + 3) / 4 * (n : ℝ) ^ (k + 1) ≤ (pathsLen G (k + 2) x y).card := by
  have h := card_paths_ge (G := G) (k + 1) hxy
  simp only [Nat.add_sub_cancel] at h
  have hck : 0 < c ^ (k + 3) := pow_pos hc _
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < 4 * (k + 2) ^ 2 / c ^ (k + 3) := by positivity
    linarith
  have hN : (Fintype.card V : ℝ) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcard) k
  have hbig : 4 * ((k : ℝ) + 2) ^ 2 ≤ c ^ (k + 3) * n := by
    have := (div_le_iff₀ hck).1 hn; linarith [mul_comm (n : ℝ) (c ^ (k + 3))]
  have hnk : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have h3 : ((k + 1 : ℕ) + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ k ≤
      c ^ (k + 3) * (n : ℝ) ^ (k + 1) / 4 := by
    have : ((k + 1 : ℕ) + 1 : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [this, show (n : ℝ) ^ (k + 1) = (n : ℝ) ^ k * n from pow_succ _ _]
    nlinarith [mul_le_mul_of_nonneg_right hbig hnk,
      mul_le_mul_of_nonneg_left hN (sq_nonneg ((k : ℝ) + 2))]
  have : (k + 1 + 1 : ℕ) = k + 2 := rfl
  rw [this] at h
  push_cast at h h3
  linarith

/-- the threshold `n₀` -/
noncomputable def n0Of (c κ : ℝ) : ℕ :=
  ⌈4 * ((kOf c κ : ℝ) + 2) ^ 2 / (min c 1) ^ (kOf c κ + 3)⌉₊ + 1

/-- **S07 (1.1), bipartite component, explicit constants** `t = kOf c κ + 2`,
`a = (min c 1)^(t+1)/4`, `n₀ = n0Of c κ`. -/
theorem odd_paths_bip_explicit (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (K : SimpleGraph V) [DecidableRel K.Adj] (n : ℕ) (hn : n0Of c κ ≤ n)
    (hmin : ∀ v, c * n ≤ K.degree v) (hmax : ∀ v, K.degree v ≤ n) (hcard : Fintype.card V ≤ n)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ * n * S.card ≤ cutCount K S)
    (col : V → Bool) (hcol : ∀ v w, K.Adj v w → col v ≠ col w) (x y : V) (hxy : col x ≠ col y) :
    (min c 1) ^ (kOf c κ + 3) / 4 * (n : ℝ) ^ (kOf c κ + 1) ≤
      (pathsLen K (kOf c κ + 2) x y).card := by
  obtain ⟨hkodd, hkb⟩ := kOf_spec hc hκ
  set k := kOf c κ
  set c' := min c 1
  set κ' := min κ 1
  have hc' : 0 < c' := lt_min hc one_pos
  have hκ' : 0 < κ' := lt_min hκ one_pos
  have hxy' : x ≠ y := fun h => hxy (h ▸ rfl)
  have hn0 : (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3)) ≤ n := by
    have := Nat.le_ceil (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3))
    have h2 : ((n0Of c κ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold n0Of at h2; push_cast at h2; linarith
  have hnpos : 0 < n := by
    have : (0 : ℝ) < 4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3) := by positivity
    exact_mod_cast (lt_of_lt_of_le this hn0)
  have hmin' : ∀ v, c' * n ≤ K.degree v := fun v =>
    le_trans (mul_le_mul_of_nonneg_right (min_le_left c 1) (Nat.cast_nonneg _)) (hmin v)
  have hexp' : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ' * n * S.card ≤ cutCount K S :=
    fun S hS => le_trans (by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left κ 1)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (hexp S hS)
  have hw := walks_lower_core K hc' hκ' (min_le_right κ 1) hnpos hmin' hmax (by omega) hexp'
    col hcol k hkodd hkb x y hxy
  have := paths_from_walks K hc' k n hn0 hcard x y hxy' hw
  exact this


/-- **S07 (1.1), bipartite component.** -/
theorem many_odd_paths_bipartite (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ t : ℕ, Odd t ∧ 3 ≤ t ∧ ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
        (n : ℕ), n₀ ≤ n →
        (∀ v, c * n ≤ K.degree v) → (∀ v, K.degree v ≤ n) → Fintype.card V ≤ n →
        (∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ * n * S.card ≤ cutCount K S) →
        ∀ col : V → Bool, (∀ v w, K.Adj v w → col v ≠ col w) →
        ∀ x y : V, col x ≠ col y →
          a * (n : ℝ) ^ (t - 1) ≤ (pathsLen K t x y).card := by
  obtain ⟨hkodd, -⟩ := kOf_spec hc hκ
  have hc' : 0 < min c 1 := lt_min hc one_pos
  refine ⟨kOf c κ + 2, hkodd.add_even even_two, by obtain ⟨j, hj⟩ := hkodd; omega,
    (min c 1) ^ (kOf c κ + 3) / 4, by positivity, n0Of c κ, ?_⟩
  intro V _ _ K _ n hn hmin hmax hcard hexp col hcol x y hxy
  have := odd_paths_bip_explicit c κ hc hκ K n hn hmin hmax hcard hexp col hcol x y hxy
  simpa using this

/-! ### The double cover -/

/-- the bipartite double cover -/
def dcover (K : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj p q := K.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (K : SimpleGraph V) [DecidableRel K.Adj] : DecidableRel (dcover K).Adj :=
  fun p q => inferInstanceAs (Decidable (K.Adj p.1 q.1 ∧ p.2 ≠ q.2))

lemma dcover_adj (K : SimpleGraph V) (p q : V × Bool) :
    (dcover K).Adj p q ↔ K.Adj p.1 q.1 ∧ p.2 ≠ q.2 := Iff.rfl

omit [DecidableEq V] in
lemma dcover_degree (K : SimpleGraph V) [DecidableRel K.Adj] (v : V) (b : Bool) :
    (dcover K).degree (v, b) = K.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have : (dcover K).neighborFinset (v, b) =
      (K.neighborFinset v).map ⟨fun w => (w, !b), fun a a' h => by simpa using h⟩ := by
    ext ⟨w, b'⟩
    simp only [SimpleGraph.mem_neighborFinset, dcover_adj, Finset.mem_map,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w,h1,by cases b <;> cases b' <;> simp_all⟩
    · rintro ⟨w',h1,hpair⟩
      change (w',!b) = (w,b') at hpair
      rcases Prod.mk.inj hpair with ⟨rfl,rfl⟩
      exact ⟨h1,by cases b <;> simp⟩
  rw [this, Finset.card_map]

lemma dcover_walks_le (K : SimpleGraph V) [DecidableRel K.Adj] :
    ∀ t : ℕ, ∀ (x y : V) (b b' : Bool),
      ((dcover K).adjMatrix ℝ ^ t) (x, b) (y, b') ≤ (K.adjMatrix ℝ ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y b b'
    simp only [pow_zero, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  | succ t ih =>
    intro x y b b'
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    apply Finset.sum_le_sum; intro w _
    rw [Fintype.sum_bool]
    have hnn : ∀ q, 0 ≤ ((dcover K).adjMatrix ℝ ^ t) (w, q) (y, b') := by
      intro q; rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]; positivity
    simp only [SimpleGraph.adjMatrix_apply, dcover_adj]
    by_cases hadj : K.Adj x w
    · cases b
      · simp [hadj]; exact ih w y true b'
      · simp [hadj]; exact ih w y false b'
    · simp [hadj]

/-- **S07 (1.1), non-bipartite component, explicit constants** (same `t`, `a`, `n₀`). -/
theorem odd_paths_nonbip_explicit (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (K : SimpleGraph V) [DecidableRel K.Adj] (n : ℕ) (hn : n0Of c κ ≤ n)
    (hmin : ∀ v, c * n ≤ K.degree v) (hmax : ∀ v, K.degree v ≤ n) (hcard : Fintype.card V ≤ n)
    (hexp : ∀ S : Finset (V × Bool), 2 * S.card ≤ Fintype.card (V × Bool) →
      κ * n * S.card ≤ cutCount (dcover K) S)
    (x y : V) (hxy : x ≠ y) :
    (min c 1) ^ (kOf c κ + 3) / 4 * (n : ℝ) ^ (kOf c κ + 1) ≤
      (pathsLen K (kOf c κ + 2) x y).card := by
  obtain ⟨hkodd, hkb⟩ := kOf_spec hc hκ
  set k := kOf c κ
  set c' := min c 1
  set κ' := min κ 1
  have hc' : 0 < c' := lt_min hc one_pos
  have hκ' : 0 < κ' := lt_min hκ one_pos
  have hn0 : (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3)) ≤ n := by
    have := Nat.le_ceil (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3))
    have h2 : ((n0Of c κ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold n0Of at h2; push_cast at h2; linarith
  have hnpos : 0 < n := by
    have : (0 : ℝ) < 4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3) := by positivity
    exact_mod_cast (lt_of_lt_of_le this hn0)
  have hmin' : ∀ p : V × Bool, c' * n ≤ (dcover K).degree p := fun p => by
    rw [dcover_degree]
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left c 1) (Nat.cast_nonneg _)) (hmin p.1)
  have hmax' : ∀ p : V × Bool, (dcover K).degree p ≤ n := fun p => by
    rw [dcover_degree]; exact hmax p.1
  have hcard' : Fintype.card (V × Bool) ≤ 2 * n := by
    rw [Fintype.card_prod, Fintype.card_bool]; omega
  have hexp' : ∀ S : Finset (V × Bool), 2 * S.card ≤ Fintype.card (V × Bool) →
      κ' * n * S.card ≤ cutCount (dcover K) S :=
    fun S hS => le_trans (by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left κ 1)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (hexp S hS)
  have hw := walks_lower_core (dcover K) hc' hκ' (min_le_right κ 1) hnpos hmin' hmax' hcard'
    hexp' Prod.snd (fun p q h => h.2) k hkodd hkb (x, false) (y, true) (by simp)
  have hw' := hw.trans (dcover_walks_le K (k + 2) x y false true)
  have := paths_from_walks K hc' k n hn0 hcard x y hxy hw'
  exact this


/-- **S07 (1.1), non-bipartite component** (expansion of the double cover). -/
theorem many_odd_paths_nonbipartite (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ t : ℕ, Odd t ∧ 3 ≤ t ∧ ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
        (n : ℕ), n₀ ≤ n →
        (∀ v, c * n ≤ K.degree v) → (∀ v, K.degree v ≤ n) → Fintype.card V ≤ n →
        (∀ S : Finset (V × Bool), 2 * S.card ≤ Fintype.card (V × Bool) →
          κ * n * S.card ≤ cutCount (dcover K) S) →
        ∀ x y : V, x ≠ y →
          a * (n : ℝ) ^ (t - 1) ≤ (pathsLen K t x y).card := by
  obtain ⟨hkodd, -⟩ := kOf_spec hc hκ
  have hc' : 0 < min c 1 := lt_min hc one_pos
  refine ⟨kOf c κ + 2, hkodd.add_even even_two, by obtain ⟨j, hj⟩ := hkodd; omega,
    (min c 1) ^ (kOf c κ + 3) / 4, by positivity, n0Of c κ, ?_⟩
  intro V _ _ K _ n hn hmin hmax hcard hexp x y hxy
  have := odd_paths_nonbip_explicit c κ hc hκ K n hn hmin hmax hcard hexp x y hxy
  simpa using this

end S07V24
