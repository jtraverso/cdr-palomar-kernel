module
public import RequestProject.S07V41.Solver
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V41.Explicit

/-- Integer-pivot elimination gives a finite, dimension-recursive solver bound. -/
def solverBound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, K => (1+2*(n+1)*(max 1 K)^2)*(solverBound n (2*(max 1 K)^2)+1)

theorem solverBound_rest (n K : ℕ) :
    2*(max 1 K)*solverBound n (2*(max 1 K)^2)  ≤  solverBound (n+1) K := by
  let k := max 1 K
  let C := solverBound n (2*k^2)
  have hk : 1 ≤ k := le_max_left _ _
  have hk2 : k ≤ k^2 := by simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left k hk
  have hn : k^2 ≤ (n+1)*k^2 := by simpa using Nat.mul_le_mul_right (k^2) (show 1 ≤ n+1 by omega)
  have hc : 2*k ≤ 1+2*(n+1)*k^2 := by nlinarith
  change 2*k*C ≤ (1+2*(n+1)*k^2)*(C+1)
  exact (Nat.mul_le_mul_right C hc).trans (Nat.mul_le_mul_left _ (Nat.le_succ C))

theorem solverBound_pivot (n K : ℕ) :
    1+2*n*(max 1 K)^2*solverBound n (2*(max 1 K)^2)  ≤  solverBound (n+1) K := by
  let k := max 1 K
  let C := solverBound n (2*k^2)
  let F := 1+2*(n+1)*k^2
  have hc : 2*n*k^2 ≤ F := by dsimp [F]; nlinarith
  have hF : 1 ≤ F := by dsimp [F]; omega
  change 1+2*n*k^2*C ≤ F*(C+1)
  calc 1+2*n*k^2*C  ≤  1+F*C := Nat.add_le_add_left (Nat.mul_le_mul_right C hc) 1
    _  ≤  F+F*C := Nat.add_le_add_right hF _
    _ = F*(C+1) := by ring

private def eliminatedRow {n : ℕ} (p t : Fin (n+1) → ℤ) (j : Fin (n+1)) : Fin n → ℤ :=
  fun k => p j*t (j.succAbove k)-t j*p (j.succAbove k)

private theorem dotZ_split {n : ℕ} (u : Fin (n+1) → ℝ) (t : Fin (n+1) → ℤ)
    (j : Fin (n+1)) :
    dotZ u t = u j*(t j:ℝ)+∑ k : Fin n, u (j.succAbove k)*(t (j.succAbove k):ℝ) := by
  unfold dotZ
  rw [Fin.sum_univ_succAbove _ j] <;> ring

private theorem eliminatedRow_dot {n : ℕ} (u : Fin (n+1) → ℝ)
    (p t : Fin (n+1) → ℤ) (j : Fin (n+1)) :
    dotZ (fun k => u (j.succAbove k)) (eliminatedRow p t j) =
      (p j:ℝ)*dotZ u t-(t j:ℝ)*dotZ u p := by
  rw [dotZ_split u t j,dotZ_split u p j]
  have hs : dotZ (fun k => u (j.succAbove k)) (eliminatedRow p t j) =
      (p j:ℝ)*(∑ k : Fin n, u (j.succAbove k)*(t (j.succAbove k):ℝ))-
      (t j:ℝ)*(∑ k : Fin n, u (j.succAbove k)*(p (j.succAbove k):ℝ)) := by
    unfold dotZ eliminatedRow
    rw [mul_sum,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    push_cast
    ring
  rw [hs]
  ring

private theorem eliminatedRow_bound {n K : ℕ} (p t : Fin (n+1) → ℤ)
    (hp : ∀ i, |p i| ≤ (K:ℤ)) (ht : ∀ i, |t i| ≤ (K:ℤ)) (j : Fin (n+1)) :
    ∀ k, |eliminatedRow p t j k| ≤ (2*K^2:ℕ) := by
  intro k
  calc |eliminatedRow p t j k|  ≤  |p j*t (j.succAbove k)|+|t j*p (j.succAbove k)| := abs_sub _ _
    _ = |p j| *|t (j.succAbove k)|+|t j| *|p (j.succAbove k)| := by rw [abs_mul,abs_mul]
    _  ≤  (K:ℤ)*K+(K:ℤ)*K := add_le_add
      (mul_le_mul (hp j) (ht _) (abs_nonneg _) (by positivity))
      (mul_le_mul (ht j) (hp _) (abs_nonneg _) (by positivity))
    _ = (2*K^2:ℕ) := by push_cast; ring

private theorem eliminatedRow_load {n K : ℕ} (u : Fin (n+1) → ℝ)
    (p t : Fin (n+1) → ℤ) (j : Fin (n+1)) (A : ℝ) (hA : 0 ≤ A)
    (hp : ∀ i, |p i| ≤ (K:ℤ)) (ht : ∀ i, |t i| ≤ (K:ℤ))
    (hpu : |dotZ u p| ≤ A) (htu : |dotZ u t| ≤ A) :
    |dotZ (fun k => u (j.succAbove k)) (eliminatedRow p t j)| ≤ 2*(K:ℝ)*A := by
  have hpj : |(p j:ℝ)| ≤ (K:ℝ) := by exact_mod_cast hp j
  have htj : |(t j:ℝ)| ≤ (K:ℝ) := by exact_mod_cast ht j
  rw [eliminatedRow_dot]
  calc |(p j:ℝ)*dotZ u t-(t j:ℝ)*dotZ u p|
       ≤  |(p j:ℝ)*dotZ u t|+|(t j:ℝ)*dotZ u p| := abs_sub _ _
    _ = |(p j:ℝ)| *|dotZ u t|+|(t j:ℝ)| *|dotZ u p| := by rw [abs_mul,abs_mul]
    _  ≤  (K:ℝ)*A+(K:ℝ)*A := add_le_add
      (mul_le_mul hpj htu (abs_nonneg _) (by positivity))
      (mul_le_mul htj hpu (abs_nonneg _) (by positivity))
    _ = 2*(K:ℝ)*A := by ring

/-- A given consistent indexed family admits a uniformly bounded realization.
The index family need not be finite or injective. -/
theorem bounded_realizer (d K : ℕ) :
    ∀ (ι : Type) (rows : ι → Fin d → ℤ) (u₀ : Fin d → ℝ) (A : ℝ), 0 ≤ A →
      (∀ t j, |rows t j| ≤ (K:ℤ)) → (∀ t, |dotZ u₀ (rows t)| ≤ A) →
      ∃ u : Fin d → ℝ, (∀ t, dotZ u (rows t)=dotZ u₀ (rows t)) ∧
        ∀ j, |u j| ≤ (solverBound d K:ℝ)*A := by
  induction d generalizing K with
  | zero =>
    intro ι rows u₀ A hA hrows hload
    refine ⟨0,?_,?_⟩
    · intro t; simp [dotZ]
    · intro j; exact Fin.elim0 j
  | succ n ih =>
    intro ι rows u₀ A hA hrows hload
    by_cases hz : ∀ t j, rows t j=0
    · refine ⟨0,?_,?_⟩
      · intro t; simp [dotZ,hz]
      · intro j; simp only [Pi.zero_apply,abs_zero]; positivity
    push_neg at hz
    obtain ⟨t₀,j,hp0⟩ := hz
    let k := max 1 K
    have hk : 1 ≤ k := le_max_left _ _
    have hrowsk : ∀ t i, |rows t i| ≤ (k:ℤ) := fun t i =>
      (hrows t i).trans (by exact_mod_cast le_max_right 1 K)
    let p := rows t₀
    let B : ι → Fin n → ℤ := fun t => eliminatedRow p (rows t) j
    let v₀ : Fin n → ℝ := fun i => u₀ (j.succAbove i)
    let k' := 2*k^2
    have hB : ∀ t i, |B t i| ≤ (k':ℤ) :=
      fun t => eliminatedRow_bound p (rows t) (hrowsk t₀) (hrowsk t) j
    have hBL : ∀ t, |dotZ v₀ (B t)| ≤ 2*(k:ℝ)*A := fun t =>
      eliminatedRow_load u₀ p (rows t) j A hA (hrowsk t₀) (hrowsk t) (hload t₀) (hload t)
    obtain ⟨v,hv,hvb⟩ := ih k' ι B v₀ (2*(k:ℝ)*A) (by positivity) hB hBL
    let a : ℤ := p j
    have ha0 : (a:ℝ) ≠ 0 := by exact_mod_cast hp0
    have ha1 : (1:ℝ) ≤ |(a:ℝ)| := by
      have hi : (1:ℤ) ≤ |a| := Int.one_le_abs hp0
      exact_mod_cast hi
    let S : ℝ := ∑ i : Fin n, v i*(p (j.succAbove i):ℝ)
    let b₀ : ℝ := dotZ u₀ p
    let pivot : ℝ := (b₀-S)/(a:ℝ)
    let u : Fin (n+1) → ℝ := Fin.insertNth j pivot v
    have hrest : (fun i => u (j.succAbove i))=v := by funext i; simp only [u,Fin.insertNth_apply_succAbove]
    have hup : dotZ u p=dotZ u₀ p := by
      rw [dotZ_split u p j]
      simp only [u,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
      change (b₀-S)/(a:ℝ)*(a:ℝ)+S=b₀
      field_simp <;> ring
    have hvalues : ∀ t, dotZ u (rows t)=dotZ u₀ (rows t) := by
      intro t
      have hnew := hv t
      have hdu := eliminatedRow_dot u p (rows t) j
      rw [hrest] at hdu
      rw [hdu,eliminatedRow_dot u₀ p (rows t) j,hup] at hnew
      have he : (p j:ℝ)*dotZ u (rows t)=(p j:ℝ)*dotZ u₀ (rows t) := by linarith only [hnew]
      exact mul_left_cancel₀ ha0 he
    let C := solverBound n k'
    have hCr : (2*(k:ℝ)*(C:ℝ)) ≤ (solverBound (n+1) K:ℝ) := by
      exact_mod_cast solverBound_rest n K
    have hCp : (1+2*(n:ℝ)*(k:ℝ)^2*(C:ℝ)) ≤ (solverBound (n+1) K:ℝ) := by
      exact_mod_cast solverBound_pivot n K
    have hS : |S| ≤ 2*(n:ℝ)*(k:ℝ)^2*(C:ℝ)*A := by
      calc |S|  ≤  ∑ i : Fin n, |v i*(p (j.succAbove i):ℝ)| := abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin n, |v i| *|(p (j.succAbove i):ℝ)| := by simp_rw [abs_mul]
        _  ≤  ∑ _ : Fin n, (C:ℝ)*(2*(k:ℝ)*A)*(k:ℝ) := by
          apply sum_le_sum
          intro i _
          have hp : |(p (j.succAbove i):ℝ)| ≤ (k:ℝ) := by exact_mod_cast hrowsk t₀ (j.succAbove i)
          exact mul_le_mul (hvb i) hp (abs_nonneg _) (by positivity)
        _ = 2*(n:ℝ)*(k:ℝ)^2*(C:ℝ)*A := by simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]; ring
    have hpivot : |pivot| ≤ (solverBound (n+1) K:ℝ)*A := by
      calc |pivot| = |b₀-S|/|(a:ℝ)| := abs_div _ _
        _  ≤  |b₀-S| := div_le_self (abs_nonneg _) ha1
        _  ≤  |b₀|+|S| := abs_sub _ _
        _  ≤  A+2*(n:ℝ)*(k:ℝ)^2*(C:ℝ)*A := add_le_add (hload t₀) hS
        _ = (1+2*(n:ℝ)*(k:ℝ)^2*(C:ℝ))*A := by ring
        _  ≤  (solverBound (n+1) K:ℝ)*A := mul_le_mul_of_nonneg_right hCp hA
    refine ⟨u,hvalues,(Fin.forall_iff_succAbove j).mpr ⟨?_,?_⟩⟩
    · simpa only [u,Fin.insertNth_apply_same] using hpivot
    · intro i
      simp only [u,Fin.insertNth_apply_succAbove]
      calc |v i| ≤ (C:ℝ)*(2*(k:ℝ)*A) := hvb i
        _ = (2*(k:ℝ)*(C:ℝ))*A := by ring
        _ ≤ (solverBound (n+1) K:ℝ)*A := mul_le_mul_of_nonneg_right hCr hA

def solverCost (d : ℕ) (K : ℤ) : ℝ := (solverBound d K.toNat:ℝ)

theorem solverCost_nonneg (d : ℕ) (K : ℤ) : 0 ≤ solverCost d K := by unfold solverCost; positivity

theorem bounded_solver_explicit (d : ℕ) (K : ℤ) :
    ∀ (T : Finset (Fin d → ℤ)), (∀ t∈T, ∀ i, |t i| ≤ K) →
      ∀ (b : (Fin d → ℤ) → ℝ) (A : ℝ), 0 ≤ A → (∀ t∈T, |b t| ≤ A) →
      RelCompat T b → ∃ u : Fin d → ℝ, (∀ t∈T, dotZ u t=b t) ∧
        ∀ i, |u i| ≤ solverCost d K*A := by
  intro T hT b A hA hb hcomp
  obtain ⟨u₀,hu₀⟩ := exists_solution T b hcomp
  obtain ⟨u,hu,hub⟩ := bounded_realizer d K.toNat T (fun t => t.val) u₀ A hA
    (fun t i => (hT t.val t.property i).trans (Int.self_le_toNat K))
    (fun t => by rw [hu₀ t]; exact hb t.val t.property)
  exact ⟨u,fun t ht => (hu ⟨t,ht⟩).trans (hu₀ ⟨t,ht⟩),hub⟩

#print axioms bounded_realizer
#print axioms bounded_solver_explicit
end S07V41.Explicit
