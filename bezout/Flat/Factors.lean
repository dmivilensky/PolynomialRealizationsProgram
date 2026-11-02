import bezout.Flat.Scalars
import bezout.Synthesis.Normalized

/-!
Article: bezout, Equations (10)–(12) and Appendix B.
Use: explicit Flat query and response-factor polynomials.
Proof: feasible reservoirs make each response factor a convex Chebyshev mixture;
the positive leading query coefficient gives a normalized graded basis.
-/

namespace bezout.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The normalized second-kind virtual-state residual.
Use: the error-free virtual states of the four-vector algorithm. -/
def normalizedU (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ[X] :=
  C (1 / u I s) * U ℝ s

/-- Every virtual-state residual equals one at the exterior normalization point.
Use: affine causal queries preserve the initial error. -/
@[simp] theorem normalizedU_eta (I : chebyshev1.SpectralInterval) (s : ℕ) :
    (normalizedU I s).eval I.eta = 1 := by
  simp only [normalizedU, eval_mul, eval_C]
  change (1 / u I s) * u I s = 1
  exact one_div_mul_cancel (ne_of_gt (u_pos I s))

/-- Initial virtual-state residual.
Use: the startup query and predecessor convention. -/
@[simp] theorem normalizedU_zero (I : chebyshev1.SpectralInterval) : normalizedU I 0 = 1 := by
  simp [normalizedU]

/-- The explicit extrapolated query polynomial.
Use: the graded query basis of the actual Flat history. The predecessor at zero
is harmless because its extrapolation coefficient vanishes. -/
def queryPolynomial (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  C (1 + tau I N s) * normalizedU I s - C (tau I N s) * normalizedU I (s - 1)

/-- Flat queries retain the required exterior normalization.
Use: the constructive normalized-history theorem. -/
@[simp] theorem queryPolynomial_eta (I : chebyshev1.SpectralInterval) (N s : ℕ) :
    (queryPolynomial I N s).eval I.eta = 1 := by simp [queryPolynomial]

/-- Flat's recursively balanced first-kind Chebyshev mixture.
Use: the explicit response factor H_m in the article. -/
def factorPolynomial (I : chebyshev1.SpectralInterval) (N : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => C (1 - mass I N (m + 1) / reservoir I N (m + 1)) * factorPolynomial I N m +
      C (mass I N (m + 1) / reservoir I N (m + 1)) * T ℝ ((m + 1 : ℕ) : ℤ)

/-- The response-factor mixture equals one at the right normalized endpoint.
Use: simultaneous equality of all physical response magnitudes at mu. -/
@[simp] theorem factorPolynomial_one (I : chebyshev1.SpectralInterval) (N m : ℕ) :
    (factorPolynomial I N m).eval 1 = 1 := by
  induction m with
  | zero => simp [factorPolynomial]
  | succ m ih => simp [factorPolynomial, ih]

/-- Convex mixture coefficients lie in the unit interval.
Use: the uniform response-factor modulus estimate. -/
theorem mixture_mem (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) :
    0 ≤ mass I N m / reservoir I N m ∧ mass I N m / reservoir I N m ≤ 1 := by
  have hr := reservoir_pos I N hN m hm
  exact ⟨le_of_lt (div_pos (mass_pos I N m) hr), (div_le_one hr).mpr (mass_le_reservoir I N hN m hm)⟩

/-- Convex Chebyshev response mixtures have modulus at most one on the interval.
Use: the uniform equal-response bound. -/
theorem factorPolynomial_abs_le (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) (x : ℝ) (hx : |x| ≤ 1) :
    |(factorPolynomial I N m).eval x| ≤ 1 := by
  induction m with
  | zero => simp [factorPolynomial]
  | succ m ih =>
    have hi := ih (by omega)
    have hc := mixture_mem I N hN (m + 1) hm
    have ht := abs_eval_T_real_le_one ((m + 1 : ℕ) : ℤ) hx
    simp only [factorPolynomial, eval_add, eval_mul, eval_C]
    calc
      _ ≤ |1 - mass I N (m + 1) / reservoir I N (m + 1)| * |(factorPolynomial I N m).eval x|
          + |mass I N (m + 1) / reservoir I N (m + 1)| * |(T ℝ ((m + 1 : ℕ) : ℤ)).eval x| :=
        (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
      _ ≤ (1 - mass I N (m + 1) / reservoir I N (m + 1)) + mass I N (m + 1) / reservoir I N (m + 1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hc.2), abs_of_nonneg hc.1]
        exact add_le_add (by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hi)])
          (by nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr ht)])
      _ = 1 := by ring

/-- Normalized virtual states retain their exact degree.
Use: establishes the triangular leading coefficient of every Flat query. -/
theorem normalizedU_degree (I : chebyshev1.SpectralInterval) (s : ℕ) :
    (normalizedU I s).degree = (s : WithBot ℕ) := by
  rw [normalizedU, degree_C_mul (one_div_ne_zero (ne_of_gt (u_pos I s))), degree_U_natCast]

/-- Every Flat query has exactly its causal degree.
Use: reconstructs one actual Chebyshev-exact history from this concrete basis. -/
theorem queryPolynomial_degree (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : ℕ) (hs : s < N) : (queryPolynomial I N s).degree = (s : WithBot ℕ) := by
  cases s with
  | zero => simp [queryPolynomial, tau_zero I N hN]
  | succ s =>
    have hc : 1 + tau I N (s + 1) ≠ 0 := by have := tau_nonneg I N hN (s + 1) hs; linarith
    have hf : (C (1 + tau I N (s + 1)) * normalizedU I (s + 1)).degree =
        ((s + 1 : ℕ) : WithBot ℕ) := by rw [degree_C_mul hc, normalizedU_degree]
    have hp : (C (tau I N (s + 1)) * normalizedU I ((s + 1) - 1)).degree <
        ((s + 1 : ℕ) : WithBot ℕ) := by
      by_cases ht : tau I N (s + 1) = 0
      · simp [ht]
      · rw [degree_C_mul ht, normalizedU_degree]
        exact_mod_cast (by omega : s + 1 - 1 < s + 1)
    rw [queryPolynomial, degree_sub_eq_left_of_degree_lt (hp.trans_eq hf.symm), hf]

/-- The concrete Flat queries as a normalized graded family.
Use: actual causal history synthesis, with no assumed factorization certificate. -/
def queries (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) : GradedFamily N where
  poly s := queryPolynomial I N s
  degree_eq s := queryPolynomial_degree I N hN s s.isLt

/-- Weighted response recursion in scalar evaluation form.
Use: the cancellation of adjacent reservoir contributions. -/
theorem factor_balance (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) (x : ℝ) :
    reservoir I N m * (factorPolynomial I N m).eval x =
      mass I N m * (T ℝ m).eval x +
        if m = 0 then 0 else (reservoir I N (m - 1) - unitMass I N) *
          (factorPolynomial I N (m - 1)).eval x := by
  cases m with
  | zero => simp [reservoir, prefixMass, factorPolynomial]
  | succ m =>
    have hr := ne_of_gt (reservoir_pos I N hN (m + 1) hm)
    simp only [factorPolynomial, eval_add, eval_mul, eval_C, Nat.succ_ne_zero, ite_false,
      Nat.succ_sub_one]
    field_simp
    rw [reservoir_succ]
    ring

/-- Weighted extrapolation in its reservoir form.
Use: the other half of the tensor cancellation. -/
theorem query_balance (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : ℕ) (y : ℝ) :
    unitMass I N * (queryPolynomial I N s).eval y =
      reservoir I N (N - 1 - s) * (normalizedU I s).eval y -
        (reservoir I N (N - 1 - s) - unitMass I N) * (normalizedU I (s - 1)).eval y := by
  have hd := ne_of_gt (unitMass_pos I N hN)
  simp only [queryPolynomial, eval_sub, eval_mul, eval_C, tau]
  field_simp
  ring

end
end bezout.Flat
