import nesterov.Quadratic.Basic
import polyak.General.Roots

/-!
Article: Lemma `restquad`, including the negative determinant caused by
extrapolation.  The existing Polyak radius formula remains the exact maximum
over actual roots for every real determinant, with no sign restriction.
-/

noncomputable section

namespace nesterov.Quadratic

theorem scalarRootRadius_isGreatest (p q : ℝ) :
    IsGreatest {r : ℝ | ∃ z : ℂ, z ^ 2 - (p : ℂ) * z + (q : ℂ) = 0 ∧ r = ‖z‖}
      (polyak.General.rootRadius p q) := by
  by_cases hq : 0 ≤ q
  · exact polyak.General.rootRadius_isGreatest hq
  have hqneg : q < 0 := lt_of_not_ge hq
  have hd : ¬p ^ 2 ≤ 4 * q := by nlinarith [sq_nonneg p]
  have hd0 : 0 < p ^ 2 - 4 * q := by nlinarith [sq_nonneg p]
  have hs := Real.sq_sqrt hd0.le
  have hs0 := Real.sqrt_nonneg (p ^ 2 - 4 * q)
  have hreal {z : ℂ} (hz : z ^ 2 - (p : ℂ) * z + (q : ℂ) = 0) : z.im = 0 := by
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
    simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
    by_contra hi
    have hh : 2 * z.re - p = 0 :=
      (mul_eq_zero.mp (show z.im * (2 * z.re - p) = 0 by nlinarith)).resolve_left hi
    nlinarith [sq_nonneg z.im]
  have hbound {z : ℂ} (hz : z ^ 2 - (p : ℂ) * z + (q : ℂ) = 0) :
      ‖z‖ ≤ (|p| + Real.sqrt (p ^ 2 - 4 * q)) / 2 := by
    have hi := hreal hz
    have hre := congrArg Complex.re hz
    simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, Complex.zero_re,
      hi, mul_zero] at hre
    have hh : |2 * z.re - p| ≤ Real.sqrt (p ^ 2 - 4 * q) := by
      rw [abs_le]
      constructor <;> nlinarith
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hzreal, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le] at hh ⊢
    constructor <;> linarith [le_abs_self p, neg_abs_le p]
  rw [polyak.General.rootRadius, ite_eq_right hd]
  constructor
  · by_cases hp : 0 ≤ p
    · refine ⟨((p + Real.sqrt (p ^ 2 - 4 * q)) / 2 : ℝ), ?_, ?_⟩
      · have he : ((p + Real.sqrt (p ^ 2 - 4 * q)) / 2) ^ 2 -
            p * ((p + Real.sqrt (p ^ 2 - 4 * q)) / 2) + q = 0 := by nlinarith
        exact_mod_cast he
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg (by positivity)]
    · have hp : p < 0 := lt_of_not_ge hp
      refine ⟨((p - Real.sqrt (p ^ 2 - 4 * q)) / 2 : ℝ), ?_, ?_⟩
      · have he : ((p - Real.sqrt (p ^ 2 - 4 * q)) / 2) ^ 2 -
            p * ((p - Real.sqrt (p ^ 2 - 4 * q)) / 2) + q = 0 := by nlinarith
        exact_mod_cast he
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hp, abs_of_nonpos (by linarith)]
        ring
  · exact fun _ ⟨z, hz, hr⟩ => by rw [hr]; exact hbound hz

theorem scalarRoot_norm_le {p q : ℝ} {z : ℂ}
    (hz : z ^ 2 - (p : ℂ) * z + (q : ℂ) = 0) :
    ‖z‖ ≤ polyak.General.rootRadius p q := (scalarRootRadius_isGreatest p q).2 ⟨z, hz, rfl⟩

/-- The largest modulus of the article's characteristic polynomial, for one curvature. -/
def scalarRadius (β τ h lam : ℝ) : ℝ := polyak.General.rootRadius (S β τ h lam) (Q β τ h lam)

theorem scalarRadius_isGreatest (β τ h lam : ℝ) :
    IsGreatest {r : ℝ | ∃ z : ℂ, characteristic β τ h lam z = 0 ∧ r = ‖z‖}
      (scalarRadius β τ h lam) := by
  simpa only [characteristic_eq, scalarRadius] using scalarRootRadius_isGreatest (S β τ h lam) (Q β τ h lam)

end nesterov.Quadratic
