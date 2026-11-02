import jacobi.Variational.FredholmSpectrum
import Mathlib.Analysis.PSeries

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
The nonnegative moment expansion holds also at and beyond a spectral pole.
It therefore supports Fredholm comparison without an unproved convergence
assumption or an illicit subtraction of two infinite quantities.
Source: mathlib's logarithm power series and Tonelli's theorem for nonnegative series.
Use: verifies the pole branch of the regularized logarithm's power series.
-/
namespace jacobi.Variational
noncomputable section
open Real
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The shifted harmonic series diverges in the extended nonnegative reals.
Use: verifies the pole branch of the regularized logarithm's power series.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Source: mathlib's divergence of the harmonic series.
Proof: a finite extended sum would give a summable real harmonic tail. -/
theorem harmonic_tail_eq_top :
    (∑' n : ℕ, ENNReal.ofReal (1/((n : ℝ)+2))) = ∞ := by
  -- Real summability of a finite ENNReal sum would contradict harmonic divergence.
  by_contra hf
  have hs := ENNReal.summable_toReal hf
  have hs' : Summable (fun n : ℕ => 1/((n : ℝ)+2)) :=
    hs.congr (fun n => ENNReal.toReal_ofReal (by positivity))
  apply not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hs'

/-- Power series of the real subcritical regularized logarithm.
Use: the finite branch of the full extended scalar expansion.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: remove the first term from mathlib's proved logarithm series. -/
theorem fredholmLog_hasSum {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hp : s*x < 1) :
    HasSum (fun n : ℕ => (s*x)^(n+2)/((n : ℝ)+2)) (fredholmLog s x) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg (mul_nonneg hs hx)]))
  simpa [fredholmLog,Nat.add_assoc,add_assoc,show (1 : ℝ)+1=2 by norm_num] using h

/-- Full nonnegative scalar series, including divergence at and beyond the pole.
Use: exchanges spectral and power-series sums in the actual Fredholm observation.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: below the pole use the logarithm series; at the pole compare termwise
with the divergent shifted harmonic series. -/
theorem fredholmTerm_series {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    fredholmTerm s x = ∑' n : ℕ, ENNReal.ofReal ((s*x)^(n+2)/((n : ℝ)+2)) := by
  -- The pole branch is proved separately rather than evaluated by the real logarithm.
  by_cases hp : s*x < 1
  · rw [fredholmTerm,ite_eq_right (not_le.mpr hp)]
    have h := fredholmLog_hasSum hs hx hp
    rw [← h.tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable
  · rw [fredholmTerm,ite_eq_left (not_lt.mp hp)]
    symm
    apply top_unique
    rw [← harmonic_tail_eq_top]
    apply ENNReal.tsum_le_tsum
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact one_le_pow₀ (not_lt.mp hp)

/-- The regularized determinant equals its nonnegative sum of actual spectral moments.
Use: Fredholm comparison follows from moment comparison, including poles.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: apply the full scalar series, exchange the two nonnegative sums, factor
the power coefficient, and use summability of every actual moment. -/
theorem fredholmSpectrum_series {s : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s)
    (ha : Summable a) (hn : ∀ j, 0 ≤ a j) :
    fredholmSpectrum s a = ∑' n : ℕ, ENNReal.ofReal (s^(n+2)/((n : ℝ)+2))*
      ENNReal.ofReal (∑' j, a j^(n+2)) := by
  -- Tonelli is valid even if the determinant is infinite; no real-series interchange is assumed.
  unfold fredholmSpectrum
  simp_rw [fredholmTerm_series hs (hn _)]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  have he (j : ℕ) : (s*a j)^(n+2)/((n : ℝ)+2)=
      (s^(n+2)/((n : ℝ)+2))*a j^(n+2) := by rw [mul_pow]; ring
  simp_rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ s^(n+2)/((n : ℝ)+2))]
  rw [ENNReal.tsum_mul_left,← ENNReal.ofReal_tsum_of_nonneg (fun j => pow_nonneg (hn j) _)
    (jacobi.Continuum.summable_powers ha hn (by omega : 0 < n+2))]

/-- Every actual density has the full extended Fredholm moment expansion.
Use: the Fredholm branch of the common variational foundations.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: specialize the spectral series to the already verified positive summable kernel spectrum. -/
theorem L1Source.fredholm_series (m : L1Source) {s : ℝ} (hs : 0 ≤ s) :
    m.fredholm s = ∑' n : ℕ, ENNReal.ofReal (s^(n+2)/((n : ℝ)+2))*
      ENNReal.ofReal (∑' j, m.spectrum j^(n+2)) :=
  fredholmSpectrum_series hs
    (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg

end
end jacobi.Variational
