/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# G1-Z, proveedor 5 (tramo algebraico): levantamiento entero en dimensión fija

Lema matricial de S01 §5, en una forma con constante uniforme declarada.

Para `d, R` fijos existe una constante `K = K(d,R)` tal que, para TODA matriz entera
con `d` filas y una cantidad ARBITRARIA de columnas `A i ∈ ℤ^d` con entradas `|A i j| ≤ R`,
todo vector `v` de su IMAGEN ENTERA (el subgrupo `span ℤ (range A)`, sin saturar
racionalmente) admite una preimagen entera `a` con

  `‖a‖₁ ≤ K · ‖v‖₁`.

La constante no depende del número de columnas (el «rango ambiental») ni de `v`.

Prueba (distinta de la cuenta por menores de S01 §5, permitida por la guía V4 §C
siempre que la constante sea uniforme):

* Para un conjunto finito fijo `S ⊆ ℤ^d` se procede por inducción sobre `S`. Al añadir `s`:
  - si algún múltiplo `N s` (`N > 0`) está en `span ℤ S'`, el coeficiente de `s` se reduce
    módulo `N` (`|k| < N`) y el resto se paga con `‖v‖₁ ≥ 1`;
  - si no, `s ∉ span ℚ S'` (limpieza de denominadores) y un funcional `ℚ`-lineal que se
    anula en `S'` determina el coeficiente `k = φ(v)/φ(s)`, acotado por `M‖v‖₁`.
* Las columnas sólo toman valores en la caja finita `[-R,R]^d`; el conjunto de columnas
  distintas es un subconjunto de esa caja y se toma el máximo de las constantes sobre los
  finitos subconjuntos posibles. Las columnas repetidas no aumentan el coste.

No se reemplaza la cota por un máximo sobre demandas `v` (conjunto infinito): el máximo se
toma sobre los subconjuntos de la caja, un conjunto finito fijado por `d` y `R`.
-/

open Finset Submodule

namespace TypedTriangle.IntLift

variable {d : ℕ}

/-- Norma `ℓ¹` de un vector entero. -/
def l1 (v : Fin d → ℤ) : ℤ := ∑ j, |v j|

lemma l1_nonneg (v : Fin d → ℤ) : 0 ≤ l1 v := sum_nonneg fun _ _ => abs_nonneg _

lemma l1_add_le (v w : Fin d → ℤ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1; rw [← sum_add_distrib]
  exact sum_le_sum fun j _ => abs_add_le _ _

lemma l1_neg (v : Fin d → ℤ) : l1 (-v) = l1 v := by simp [l1]

lemma l1_sub_le (v w : Fin d → ℤ) : l1 (v - w) ≤ l1 v + l1 w := by
  rw [sub_eq_add_neg]; exact (l1_add_le _ _).trans (by rw [l1_neg])

lemma l1_smul (k : ℤ) (v : Fin d → ℤ) : l1 (k • v) = |k| * l1 v := by
  simp [l1, abs_mul, mul_sum]

lemma one_le_l1 {v : Fin d → ℤ} (hv : v ≠ 0) : 1 ≤ l1 v := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  have : |v j| ≤ l1 v := single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (mem_univ j)
  have : 1 ≤ |v j| := Int.one_le_abs hj
  linarith

/-- Inclusión `ℤ^d → ℚ^d`. -/
def castL : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℚ) where
  toFun v j := (v j : ℚ)
  map_add' v w := by ext j; simp
  map_smul' k v := by ext j; simp

lemma castL_apply (v : Fin d → ℤ) (j : Fin d) : castL v j = (v j : ℚ) := rfl

lemma castL_injective : Function.Injective (castL (d := d)) := by
  intro v w h; funext j
  have := congrFun h j; simp only [castL_apply] at this; exact_mod_cast this

/-- Cota lineal de un funcional `ℚ`-lineal sobre vectores enteros. -/
lemma abs_functional_le (φ : (Fin d → ℚ) →ₗ[ℚ] ℚ) (v : Fin d → ℤ) :
    |φ (castL v)| ≤ (∑ j, |φ (Pi.single j 1)|) * (l1 v : ℚ) := by
  have hv : castL v = ∑ j, (v j : ℚ) • (Pi.single j 1 : Fin d → ℚ) := by
    ext i; simp [castL_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  calc |∑ j, (v j : ℚ) * φ (Pi.single j 1)|
      ≤ ∑ j, |(v j : ℚ)| * |φ (Pi.single j 1)| := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_); simp [abs_mul]
    _ ≤ ∑ j, |(v j : ℚ)| * (∑ i, |φ (Pi.single i 1)|) := by
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact single_le_sum (f := fun i => |φ (Pi.single i 1)|) (fun _ _ => abs_nonneg _)
          (mem_univ j)
    _ = (∑ j, |φ (Pi.single j 1)|) * (l1 v : ℚ) := by
        rw [← sum_mul, mul_comm]; simp [l1]

/-- La imagen por `castL` de `span ℤ S` está en `span ℚ (castL '' S)`. -/
lemma castL_mem_span_rat {S : Set (Fin d → ℤ)} {w : Fin d → ℤ} (hw : w ∈ span ℤ S) :
    castL w ∈ span ℚ (castL '' S) := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ]; exact smul_mem _ _ hx

/-- Limpieza de denominadores: si `s` está en el `ℚ`-span de `S'`, algún múltiplo positivo
de `s` está en el `ℤ`-span. -/
lemma exists_mul_mem_span_of_rat {S' : Finset (Fin d → ℤ)} {s : Fin d → ℤ}
    (h : castL s ∈ span ℚ (castL '' (S' : Set (Fin d → ℤ)))) :
    ∃ N : ℤ, 0 < N ∧ N • s ∈ span ℤ (S' : Set (Fin d → ℤ)) := by
  classical
  have h' : castL s ∈ span ℚ ((S'.image castL : Finset (Fin d → ℚ)) : Set (Fin d → ℚ)) := by
    rwa [coe_image]
  obtain ⟨f, -, hf⟩ := mem_span_finset.1 h'
  set T := S'.image castL
  let N : ℕ := ∏ t ∈ T, (f t).den
  have hNpos : 0 < N := prod_pos fun t _ => (f t).den_pos
  have hint : ∀ t ∈ T, ∃ z : ℤ, (N : ℚ) * f t = z := by
    intro t ht
    obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun t => (f t).den) ht
    refine ⟨m * (f t).num, ?_⟩
    have hm' : (N : ℚ) = (f t).den * m := by exact_mod_cast hm
    rw [hm']; push_cast; rw [← Rat.mul_den_eq_num]; ring
  choose! z hz using hint
  refine ⟨N, by exact_mod_cast hNpos, ?_⟩
  have key : castL ((N : ℤ) • s) = ∑ t ∈ T, z t • t := by
    rw [map_smul, ← hf, smul_sum]
    refine sum_congr rfl fun t ht => ?_
    ext j
    have := hz t ht
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
    rw [← this]; push_cast; ring
  have hmem : ∑ t ∈ T, z t • t ∈ span ℤ (castL '' (S' : Set (Fin d → ℤ))) := by
    refine sum_mem fun t ht => smul_mem _ _ (subset_span ?_)
    simpa [T] using ht
  rw [← key, ← Submodule.map_span] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  rwa [← castL_injective hyeq]

/-- Paso inductivo: al añadir `s`, el coeficiente de `s` puede acotarse linealmente. -/
lemma coeff_bound (S' : Finset (Fin d → ℤ)) (s : Fin d → ℤ) :
    ∃ Kk : ℕ, ∀ v ∈ span ℤ (insert s (S' : Set (Fin d → ℤ))), v ≠ 0 →
      ∃ k : ℤ, ∃ w ∈ span ℤ (S' : Set (Fin d → ℤ)), v = k • s + w ∧ |k| ≤ Kk * l1 v := by
  classical
  by_cases hq : castL s ∈ span ℚ (castL '' (S' : Set (Fin d → ℤ)))
  · obtain ⟨N, hN, hNs⟩ := exists_mul_mem_span_of_rat hq
    refine ⟨N.toNat, fun v hv hv0 => ?_⟩
    obtain ⟨k, w, hw, rfl⟩ := mem_span_insert.1 hv
    refine ⟨k % N, w + (k / N) • (N • s), add_mem hw (smul_mem _ _ hNs), ?_, ?_⟩
    · have := Int.emod_add_mul_ediv k N
      rw [smul_smul, add_comm w, ← add_assoc, ← add_smul]
      congr 1; congr 1; linarith
    · have h0 : 0 ≤ k % N := Int.emod_nonneg _ hN.ne'
      have h1 : k % N < N := Int.emod_lt_of_pos _ hN
      have h2 := one_le_l1 hv0
      rw [abs_of_nonneg h0, Int.toNat_of_nonneg hN.le]
      nlinarith
  · obtain ⟨φ, hφs, hφ⟩ := exists_dual_map_eq_bot_of_notMem hq inferInstance
    have hvan : ∀ w ∈ span ℤ (S' : Set (Fin d → ℤ)), φ (castL w) = 0 := by
      intro w hw
      have : φ (castL w) ∈ (span ℚ (castL '' (S' : Set (Fin d → ℤ)))).map φ :=
        mem_map_of_mem (castL_mem_span_rat hw)
      rw [hφ] at this; exact (Submodule.mem_bot ℚ).1 this
    set M := ∑ j, |φ (Pi.single j 1)|
    refine ⟨⌈M / |φ (castL s)|⌉₊, fun v hv _ => ?_⟩
    obtain ⟨k, w, hw, rfl⟩ := mem_span_insert.1 hv
    refine ⟨k, w, hw, rfl, ?_⟩
    have hk : φ (castL (k • s + w)) = k * φ (castL s) := by
      rw [map_add, map_add, hvan w hw, map_smul, ← Int.cast_smul_eq_zsmul ℚ, map_smul]
      simp
    have hb := abs_functional_le φ (k • s + w)
    rw [hk, abs_mul] at hb
    have hpos : 0 < |φ (castL s)| := abs_pos.2 hφs
    have hl := l1_nonneg (k • s + w)
    have : (|k| : ℚ) ≤ (M / |φ (castL s)|) * (l1 (k • s + w) : ℚ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      linarith
    have hc : (M / |φ (castL s)|) * (l1 (k • s + w) : ℚ) ≤
        (⌈M / |φ (castL s)|⌉₊ : ℚ) * (l1 (k • s + w) : ℚ) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by exact_mod_cast hl)
    exact_mod_cast this.trans hc

/-- Versión para un conjunto finito fijo de columnas. -/
theorem exists_bound_finset (S : Finset (Fin d → ℤ)) :
    ∃ K : ℕ, ∀ v ∈ span ℤ (S : Set (Fin d → ℤ)), ∃ a : (Fin d → ℤ) → ℤ,
      ∑ s ∈ S, a s • s = v ∧ ∑ s ∈ S, |a s| ≤ K * l1 v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, fun v hv => ⟨0, ?_, by simp⟩⟩
    simp only [coe_empty, span_empty, mem_bot] at hv; simp [hv]
  | insert s S' hs ih =>
    obtain ⟨K', hK'⟩ := ih
    obtain ⟨Kk, hKk⟩ := coeff_bound S' s
    refine ⟨Kk + K' * (1 + Kk * (l1 s).toNat), fun v hv => ?_⟩
    rw [coe_insert] at hv
    by_cases hv0 : v = 0
    · exact ⟨0, by simp [hv0], by simp [hv0, l1]⟩
    obtain ⟨k, w, hw, hvw, hk⟩ := hKk v hv hv0
    obtain ⟨b, hb, hbc⟩ := hK' w hw
    refine ⟨Function.update b s k, ?_, ?_⟩
    · rw [sum_insert hs, Function.update_self, hvw, ← hb]
      congr 1
      refine sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (by rintro rfl; exact hs ht)]
    · rw [sum_insert hs, Function.update_self]
      have hsum : ∑ t ∈ S', |Function.update b s k t| = ∑ t ∈ S', |b t| :=
        sum_congr rfl fun t ht => by rw [Function.update_of_ne (by rintro rfl; exact hs ht)]
      rw [hsum]
      have h1 := one_le_l1 hv0
      have hwv : w = v - k • s := by rw [hvw]; abel
      have hlw : l1 w ≤ (1 + Kk * l1 s) * l1 v := by
        rw [hwv]
        refine (l1_sub_le _ _).trans ?_
        rw [l1_smul]
        have := l1_nonneg s
        nlinarith
      have hls : ((l1 s).toNat : ℤ) = l1 s := Int.toNat_of_nonneg (l1_nonneg s)
      push_cast; rw [hls]
      have hK'0 : (0 : ℤ) ≤ K' := by positivity
      nlinarith

/-- Transferencia a familias indexadas: columnas repetidas no aumentan el coste. -/
lemma transfer_indexed {ι : Type*} [Fintype ι] (A : ι → Fin d → ℤ) (aS : (Fin d → ℤ) → ℤ) :
    ∃ a : ι → ℤ, ∑ i, a i • A i = ∑ s ∈ univ.image A, aS s • s ∧
      ∑ i, |a i| = ∑ s ∈ univ.image A, |aS s| := by
  classical
  let r : ι → ι := fun i => Classical.choose (⟨i, rfl⟩ : ∃ j, A j = A i)
  have hr : ∀ s (hs : ∃ j, A j = s) i, A i = s → r i = Classical.choose hs := by
    intro s hs i h; subst h; rfl
  refine ⟨fun i => if r i = i then aS (A i) else 0, ?_, ?_⟩
  · rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image A) (g := A)
      (fun i _ => mem_image_of_mem A (mem_univ i))]
    refine sum_congr rfl fun s hs => ?_
    obtain ⟨j0, -, hj0⟩ := mem_image.1 hs
    have hex : ∃ j, A j = s := ⟨j0, hj0⟩
    have hc : A (Classical.choose hex) = s := Classical.choose_spec hex
    rw [sum_congr rfl (g := fun i => if i = Classical.choose hex then aS s • s else 0)]
    · rw [sum_ite_eq']; simp [hc]
    · intro i hi
      have hi' : A i = s := (mem_filter.1 hi).2
      simp only []
      rw [hr s hex i hi', hi']
      by_cases h : Classical.choose hex = i
      · subst h; simp
      · simp [h, Ne.symm h]
  · rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image A) (g := A)
      (fun i _ => mem_image_of_mem A (mem_univ i))]
    refine sum_congr rfl fun s hs => ?_
    obtain ⟨j0, -, hj0⟩ := mem_image.1 hs
    have hex : ∃ j, A j = s := ⟨j0, hj0⟩
    have hc : A (Classical.choose hex) = s := Classical.choose_spec hex
    rw [sum_congr rfl (g := fun i => if i = Classical.choose hex then |aS s| else 0)]
    · rw [sum_ite_eq']; simp [hc]
    · intro i hi
      have hi' : A i = s := (mem_filter.1 hi).2
      simp only []
      rw [hr s hex i hi', hi']
      by_cases h : Classical.choose hex = i
      · subst h; simp
      · simp [h, Ne.symm h]

/-- **Levantamiento entero uniforme en dimensión fija (S01 §5, constante declarada).**
Para `d, R` fijos hay `K` tal que, para cualquier número de columnas `A i ∈ ℤ^d` con
entradas acotadas por `R`, todo `v` de la imagen entera tiene una preimagen entera de
coste `ℓ¹` a lo sumo `K ‖v‖₁`. -/
theorem int_lift_uniform (d R : ℕ) :
    ∃ K : ℕ, ∀ {ι : Type*} [Fintype ι] (A : ι → Fin d → ℤ), (∀ i j, |A i j| ≤ R) →
      ∀ v ∈ span ℤ (Set.range A), ∃ a : ι → ℤ, ∑ i, a i • A i = v ∧ ∑ i, |a i| ≤ K * l1 v := by
  classical
  let box : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Icc (-(R : ℤ)) R
  choose Kf hKf using fun S : Finset (Fin d → ℤ) => exists_bound_finset S
  refine ⟨box.powerset.sup Kf, fun {ι} _ A hA v hv => ?_⟩
  set S := univ.image A
  have hSbox : S ∈ box.powerset := by
    rw [mem_powerset]; intro s hs
    obtain ⟨i, -, rfl⟩ := mem_image.1 hs
    simp only [box, Fintype.mem_piFinset, mem_Icc]
    intro j; exact abs_le.1 (hA i j)
  have hspan : (S : Set (Fin d → ℤ)) = Set.range A := by simp [S]
  rw [← hspan] at hv
  obtain ⟨aS, haS, haSc⟩ := hKf S v hv
  obtain ⟨a, ha, hac⟩ := transfer_indexed A aS
  refine ⟨a, ha.trans haS, ?_⟩
  rw [hac]
  refine haSc.trans (mul_le_mul_of_nonneg_right ?_ (l1_nonneg v))
  exact_mod_cast le_sup (f := Kf) hSbox

/-- **Empalme de recuperación (G1-Z, conexión `c_final = C₀(x) + Σ a_r q_r`).**
Sea `∂ : ℤ^𝒯 → ℤ^E` lineal (la incidencia), `emb : ℤ^d → ℤ^E` una inclusión de
coordenadas que conserva la norma `ℓ¹` (las aristas de `E(W)`), y columnas residuales
`B₀ r ∈ ℤ^d` con entradas `≤ R`, cada una con un realizador físico `q r` de coste `≤ J`
(`∂ (q r) = emb (B₀ r)`). Si la eliminación lineal da `x − emb y = ∂ c₀` con
`‖c₀‖₁ ≤ H‖x‖₁`, `‖y‖₁ ≤ D‖x‖₁` y `y` en la imagen ENTERA de `B₀`, entonces `x = ∂ c`
con `‖c‖₁ ≤ (H + J K D)‖x‖₁`, donde `K = K(d,R)` es la constante de `int_lift_uniform`,
independiente del número de columnas residuales y de cualquier certificado previo. -/
theorem recovery_splice (d R : ℕ) :
    ∃ K : ℕ, ∀ {𝒯 E ι : Type*} [Fintype 𝒯] [Fintype E] [Fintype ι]
      (bd : (𝒯 → ℤ) →ₗ[ℤ] (E → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (E → ℤ))
      (B₀ : ι → Fin d → ℤ) (q : ι → 𝒯 → ℤ) (H D J : ℕ),
      (∀ r j, |B₀ r j| ≤ R) → (∀ r, bd (q r) = emb (B₀ r)) → (∀ r, ∑ t, |q r t| ≤ J) →
      ∀ (x : E → ℤ) (c₀ : 𝒯 → ℤ) (y : Fin d → ℤ),
        x - emb y = bd c₀ → ∑ t, |c₀ t| ≤ H * ∑ e, |x e| → l1 y ≤ D * ∑ e, |x e| →
        y ∈ span ℤ (Set.range B₀) →
        ∃ c : 𝒯 → ℤ, bd c = x ∧ ∑ t, |c t| ≤ (H + J * K * D) * ∑ e, |x e| := by
  classical
  obtain ⟨K, hK⟩ := int_lift_uniform d R
  refine ⟨K, fun {𝒯 E ι} _ _ _ bd emb B₀ q H D J hB hq hJ x c₀ y hx hc₀ hy hspan => ?_⟩
  obtain ⟨a, ha, hac⟩ := hK B₀ hB y hspan
  refine ⟨c₀ + ∑ r, a r • q r, ?_, ?_⟩
  · have hy' : ∑ r, a r • emb (B₀ r) = emb y := by
      rw [← ha, map_sum]; simp only [map_zsmul]
    rw [map_add, map_sum, ← hx]
    simp only [map_zsmul, hq]
    rw [hy']; abel
  · have hx0 : 0 ≤ ∑ e, |x e| := sum_nonneg fun _ _ => abs_nonneg _
    have h1 : ∑ t, |(c₀ + ∑ r, a r • q r) t| ≤ ∑ t, |c₀ t| + ∑ r, |a r| * J := by
      calc ∑ t, |(c₀ + ∑ r, a r • q r) t|
          ≤ ∑ t, (|c₀ t| + ∑ r, |a r| * |q r t|) := by
            refine sum_le_sum fun t _ => ?_
            simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
            refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            simp [abs_mul]
        _ = ∑ t, |c₀ t| + ∑ r, |a r| * ∑ t, |q r t| := by
            rw [sum_add_distrib, sum_comm]; simp [mul_sum]
        _ ≤ ∑ t, |c₀ t| + ∑ r, |a r| * J := by
            gcongr with r; exact hJ r
    have h2 : ∑ r, |a r| * (J : ℤ) ≤ J * K * D * ∑ e, |x e| := by
      rw [← sum_mul]
      have hK0 : (0 : ℤ) ≤ K := by positivity
      have hJ0 : (0 : ℤ) ≤ J := by positivity
      calc (∑ r, |a r|) * (J : ℤ) ≤ (K * l1 y) * J := mul_le_mul_of_nonneg_right hac hJ0
        _ ≤ (K * (D * ∑ e, |x e|)) * J := by gcongr
        _ = J * K * D * ∑ e, |x e| := by ring
    linarith

end TypedTriangle.IntLift
