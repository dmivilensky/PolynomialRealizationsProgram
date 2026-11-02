import jacobi.Support.SineShiftBounds
import jacobi.Complex.SineModulus
import jacobi.Reference.CosineDomination

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The actual complex frequency has the original free-state gap and a
uniform sine lower bound in the oscillatory sector. The estimates
use the already proved positive compact sine comparison.
Use: the oscillatory support state has E=exp(abs(Im theta)) in its actual one-step propagation inequality.
-/
namespace jacobi.Support
noncomputable section
open Real Set

/-- The two genuine free exponential propagation factors have the exact original common strip bound.
Use: the oscillatory support state has E=exp(abs(Im theta)) in its actual one-step propagation inequality.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the complex exponential norm is the exponential of its real part, which here is plus or minus the original imaginary frequency. -/
theorem free_frequency_norms (theta:ℂ) :
    1≤exp |theta.im| ∧ ‖Complex.exp (theta*Complex.I)‖≤exp |theta.im| ∧
      ‖(Complex.exp (theta*Complex.I))⁻¹‖≤exp |theta.im| := by
  refine ⟨by simpa only [exp_zero] using exp_le_exp.mpr (abs_nonneg theta.im),?_,?_⟩
  · simpa only [Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
      using exp_le_exp.mpr (neg_le_abs theta.im)
  · rw [← Complex.exp_neg,Complex.norm_exp]
    simpa using exp_le_exp.mpr (le_abs_self theta.im)

/-- The actual free-state spectral gap is exactly twice the sine modulus of the same original frequency.
Use: the genuine support oscillatory error is divided by precisely the source's sine gap, with no independent nonresonance assumption.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the two exact complex Euler formulas identify their difference with 2*i*sin(theta); take its genuine complex norm. -/
theorem free_frequency_gap (theta:ℂ) :
    ‖Complex.exp (theta*Complex.I)-(Complex.exp (theta*Complex.I))⁻¹‖=2*‖Complex.sin theta‖ := by
  have he : Complex.exp (theta*Complex.I)-(Complex.exp (theta*Complex.I))⁻¹=
      2*Complex.sin theta*Complex.I := by
    rw [← Complex.exp_neg,show -(theta*Complex.I)=(-theta)*Complex.I by ring,
      Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
    ring
  rw [he,norm_mul,norm_mul,Complex.norm_I,Complex.norm_ofNat,mul_one]

/-- Every genuine oscillatory-sector frequency has the source's uniform positive sine-to-frequency comparison.
Use: the support oscillatory propagation absorbs its actual summable recurrence error uniformly after the genuine transition index.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the real part has at least half the full frequency modulus. The proved actual compact real sine comparison and the exact complex sine-square identity give the same positive lower bound for the full complex sine. -/
theorem oscillatory_sine_lower :
    ∃c:ℝ,0<c ∧ ∀theta:ℂ,|theta.re|≤4*π/5→|theta.im|≤‖theta‖/2→c*‖theta‖≤‖Complex.sin theta‖ := by
  -- The genuine imaginary sine contribution is nonnegative, so the same compact real sine constant controls the actual complex gap.
  obtain ⟨c,C,hc,hC,hbound⟩ := sine_compact_bounds (by norm_num : (0:ℝ)≤4/5) (by norm_num : (4:ℝ)/5<1)
  refine ⟨c/2,by positivity,?_⟩
  intro theta hre him
  have hpoint : |theta.re|/π∈Icc (0:ℝ) (4/5) :=
    ⟨by positivity,(div_le_iff₀ pi_pos).mpr (by linarith)⟩
  have hs := (hbound _ hpoint).1
  rw [mul_div_cancel₀ _ pi_ne_zero] at hs
  have habs : |sin (|theta.re|)|=|sin theta.re| := by
    rcases le_or_gt 0 theta.re with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,sin_neg,abs_neg]
  have hs' : c*|theta.re|≤‖Complex.sin theta‖ := by
    calc
      _ ≤ sin (|theta.re|) := hs
      _ ≤ |sin (|theta.re|)| := le_abs_self _
      _ = |sin theta.re| := habs
      _ ≤ _ := (jacobi.Complex.sine_modulus_lower theta).1
  have hn := Complex.norm_le_abs_re_add_abs_im theta
  nlinarith only [hs',hn,him,hc]

end
end jacobi.Support
