import chebyshev1.Jacobi.Gain
import chebyshev1.Jacobi.Resolvent
import chebyshev1.Jacobi.EndpointBound
import chebyshev1.Realization.StaticShift

/-! Endpoint Green profiles for arbitrary terminally exact Jacobi recurrences. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

/-- The diagonal Green profile in continuant coordinates. -/
def endpointProfile (N s : ℕ) : ℝ :=
  (J.leading s).eval 1 * (J.block (s + 1) (N - (s + 1))).eval 1 /
    (J.leading N).eval 1

/-- The squared Euclidean norm of the endpoint Green profile. -/
def endpointEnergy (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range N, (J.endpointProfile N s) ^ 2

theorem endpointProfile_nonneg {N : ℕ} (hmax : J.EndpointMax N)
    (s : ℕ) (hs : s < N) : 0 ≤ J.endpointProfile N s := by
  have hp (a n : ℕ) (hn : a + n ≤ N) : 0 ≤ (J.block a n).eval 1 :=
    (abs_nonneg _).trans (hmax a n hn 1 (by norm_num))
  exact div_nonneg (mul_nonneg (hp 0 s (by omega)) (hp (s + 1) (N - (s + 1)) (by omega)))
    (hp 0 N (by omega))

theorem endpointProfile_eq_resolvent (n : ℕ) (s : Fin (n + 1))
    (hsq : ∀ t, 0 ≤ J.aSq t) :
    J.endpointProfile (n + 1) s = (1 - J.matrix 0 (n + 1))⁻¹ s s := by
  have hlen : n + 1 - (s.val + 1) = n - s.val := by omega
  simpa [endpointProfile, hlen] using (J.resolvent_diagonal n s 1 hsq).symm

theorem endpoint_ratio {N : ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = C c * T ℝ N) :
    (J.leading N).eval 1 / J.den I N = I.epsilon N := by
  rw [den, ht]
  simp only [eval_mul, eval_C, T_eval_one, mul_one]
  change c / (c * I.den N) = 1 / I.den N
  field_simp

theorem kernel_endpoint_profile {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N)
    (s : ℕ) (hs : s < N) :
    (J.realization I).kernel N s I.mu I.mu =
      -(2 * I.epsilon N / I.delta) * J.endpointProfile N s := by
  have he : (J.leading N).eval 1 ≠ 0 := by simpa [ht] using hc
  have hr := J.endpoint_ratio I hc ht
  rw [J.kernel_eq I h s hs, I.z_mu, endpointProfile]
  field_simp [he, J.den_ne I h le_rfl, I.delta_pos.ne'] at hr ⊢
  rw [hr]

/-- The terminal Chebyshev polynomial fixes the mass of every endpoint profile. -/
theorem endpointProfile_mass {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    ∑ s ∈ Finset.range N, J.endpointProfile N s = (N : ℝ) ^ 2 := by
  have hd := (J.realization I).kernel_sum_derivative N I.mu
  rw [J.residualPolynomial_eq I h N le_rfl, J.terminal_residual I hc ht,
    I.residual_derivative_eval_mu] at hd
  have he : (∑ s ∈ Finset.range N, (J.realization I).kernel N s I.mu I.mu) =
      -(2 * I.epsilon N / I.delta) * ∑ s ∈ Finset.range N, J.endpointProfile N s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s hs =>
      J.kernel_endpoint_profile I h hc ht s (Finset.mem_range.mp hs))
  rw [he] at hd
  have hp : 0 < 2 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  apply mul_left_cancel₀ (neg_ne_zero.mpr hp.ne')
  calc
    _ = _ := hd
    _ = _ := by ring

theorem endpointEnergy_gap {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    (∑ s ∈ Finset.range N, (J.endpointProfile N s - (N : ℝ)) ^ 2) =
      J.endpointEnergy N - (N : ℝ) ^ 3 := by
  have he : (∑ s ∈ Finset.range N, (J.endpointProfile N s - (N : ℝ)) ^ 2) =
      J.endpointEnergy N - 2 * (N : ℝ) *
        (∑ s ∈ Finset.range N, J.endpointProfile N s) + (N : ℝ) ^ 3 := by
    simp only [sub_sq, endpointEnergy, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum (Finset.range N) (fun s => J.endpointProfile N s) 2]
    ring
  rw [he, J.endpointProfile_mass I h hc ht]
  ring

theorem endpointEnergy_ge_cube {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    (N : ℝ) ^ 3 ≤ J.endpointEnergy N := by
  have hp := Finset.sum_nonneg (fun s (_ : s ∈ Finset.range N) =>
    sq_nonneg (J.endpointProfile N s - (N : ℝ)))
  rw [J.endpointEnergy_gap I h hc ht] at hp
  linarith

theorem endpoint_kernelNorm {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    (J.realization I).kernelNorm N I.mu I.mu =
      2 * I.epsilon N / I.delta * Real.sqrt (J.endpointEnergy N) := by
  have he : (∑ s ∈ Finset.range N, ((J.realization I).kernel N s I.mu I.mu) ^ 2) =
      (2 * I.epsilon N / I.delta) ^ 2 * J.endpointEnergy N := by
    rw [endpointEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [J.kernel_endpoint_profile I h hc ht s (Finset.mem_range.mp hs)]
    ring
  rw [Realization.kernelNorm, he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (show 0 < 2 * I.epsilon N / I.delta from
      div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos)]

/-- The universal `N^(3/2)` lower bound, written without fractional powers. -/
theorem gain_ge_sqrt_cube {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    2 * I.epsilon N / I.delta * Real.sqrt ((N : ℝ) ^ 3) ≤
      (J.realization I).gain I N := by
  calc
    _ ≤ 2 * I.epsilon N / I.delta * Real.sqrt (J.endpointEnergy N) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (J.endpointEnergy_ge_cube I h hc ht))
        (div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos).le
    _ = (J.realization I).kernelNorm N I.mu I.mu :=
      (J.endpoint_kernelNorm I h hc ht).symm
    _ ≤ _ := Realization.kernelNorm_le_gain _ I N
      ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩

end
end chebyshev1.JacobiData
