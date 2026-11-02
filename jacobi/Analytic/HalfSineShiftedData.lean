import jacobi.Analytic.ShiftedProfiles
import jacobi.GelfandLevitan.HalfSineCase
import jacobi.Analysis.HyperbolicFourierSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
Article: jacobi, Appendix E.1.
The actual sine Bessel spectrum discharges every pole-exclusion and
summability premise of the exact hyperbolic Fourier calculation. In
particular r*sinh(r) is nonzero at every nonzero admissible square shift.
Use: half_sine_all_denominators applies the exact periodic cosh calculation at every actual complex edge shift.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set jacobi.GelfandLevitan jacobi.Analysis

/-- Every genuine nonzero integer Fourier denominator is excluded by the original U shifted spectral domain.
Use: half_sine_all_denominators applies the exact periodic cosh calculation at every actual complex edge shift.
Article: jacobi, Appendix E.1.
Proof: the genuine U target spectrum is exactly pi^2*(k+1)^2;
substitute it in the previously proved original slit-domain pole exclusion. -/
theorem half_sine_positive_denominator (ha:-1<(1/2:ℝ)) (r:ℂ)
    (hw:r^2∈edgeDomain (1/2) ha) (k:ℕ) :
    r^2+(Real.pi:ℂ)^2*(k+1:ℂ)^2≠0 := by
  have h := shiftedEdge_denominator_ne (1/2) ha k hw
  rw [half_sine_spectrum] at h
  push_cast at h
  simpa only [add_comm] using h

/-- Every actual integer denominator, including the zero frequency, is nonzero for a nonzero admissible square shift.
Use: the genuine periodic cosh Fourier reconstruction has no extra denominator hypotheses in the final U formula.
Article: jacobi, Appendix E.1.
Proof: zero frequency is excluded by r!=0. Positive frequencies are
the genuine original sine spectrum, and negative frequencies have exactly the same squares. -/
theorem half_sine_all_denominators (ha:-1<(1/2:ℝ)) {r:ℂ} (hr:r≠0)
    (hw:r^2∈edgeDomain (1/2) ha) (n:ℤ) : r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0 := by
  -- This includes the auxiliary constant Fourier mode, separate from the positive source spectrum.
  cases n with
  | ofNat k =>
    change r^2+(Real.pi:ℂ)^2*(k:ℂ)^2≠0
    cases k with
    | zero => simpa only [Nat.cast_zero,zero_pow (by decide: (2:ℕ)≠0),mul_zero,add_zero] using pow_ne_zero 2 hr
    | succ k => simpa only [Nat.cast_add,Nat.cast_one] using half_sine_positive_denominator ha r hw k
  | negSucc k =>
    simp only [Int.cast_negSucc,neg_sq,Nat.cast_add,Nat.cast_one]
    exact half_sine_positive_denominator ha r hw k

/-- The original hyperbolic denominator is nonzero wherever all actual integer spectral denominators are nonzero.
Use: half_sine_shifted_profile divides the exact Fourier sum by the true source factor r*sinh(r).
Article: jacobi, Appendix E.1.
Proof: a zero sinh(r) would make sin(r*i) zero. The genuine complex
sine zero theorem gives r*i=n*pi; squaring contradicts the same original
integer spectral denominator. The zero r case is excluded by its constant mode. -/
theorem hyperbolic_denominator_ne {r:ℂ}
    (hD:∀n:ℤ,r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0) : r*Complex.sinh r≠0 := by
  -- Nonvanishing is derived from the actual full spectral pole exclusion, not assumed for the quotient.
  have hr : r≠0 := by intro h; apply hD 0; simp only [h,zero_pow (by decide: (2:ℕ)≠0),Int.cast_zero,mul_zero,add_zero]
  apply mul_ne_zero hr
  intro hs
  have hz : Complex.sin (r*Complex.I)=0 := by rw [Complex.sin_mul_I,hs,zero_mul]
  obtain ⟨n,hn⟩ := Complex.sin_eq_zero_iff.mp hz
  have hh := congrArg (fun z:ℂ => z^2) hn
  rw [mul_pow,Complex.I_sq,mul_neg_one,mul_pow] at hh
  apply hD n
  linear_combination -hh

/-- The genuine positive cosh Fourier tail is a scalar multiple of the original U shifted spectrum.
Use: half_sine_cosh_summable reuses its actual source-domain Rayleigh majorant.
Article: jacobi, Appendix E.1.
Proof: substitute the genuine original U sine spectrum and cancel the exact factor two. -/
theorem half_sine_cosh_coefficient (ha:-1<(1/2:ℝ)) (r:ℂ) (k:ℕ) :
    coshCoefficient r (k+1)=(r*Complex.sinh r/2)*shiftedEdge (1/2) ha k (r^2) := by
  rw [coshCoefficient,shiftedEdge,half_sine_spectrum]
  push_cast
  ring

/-- The actual cosh Fourier tail is genuinely summable on the complete original U slit domain.
Use: the final closed hyperbolic U formula has no additional Fourier convergence premise.
Article: jacobi, Appendix E.1.
Proof: the already proved compact shifted spectral majorant on the
actual singleton is a constant multiple of the genuine summable U
Rayleigh spectrum. Its scalar multiple is precisely the cosh Fourier tail. -/
theorem half_sine_cosh_summable (ha:-1<(1/2:ℝ)) (r:ℂ)
    (hw:r^2∈edgeDomain (1/2) ha) : Summable (fun k:ℕ => coshCoefficient r (k+1)) := by
  -- The convergence premise is obtained from the actual source shifted spectrum.
  obtain ⟨C,hC,hbound⟩ := shiftedEdge_compact_bound (1/2) ha (W:={r^2}) isCompact_singleton
    (by intro z hz; rw [mem_singleton_iff.mp hz]; exact hw)
  have hs : Summable (fun k:ℕ => shiftedEdge (1/2) ha k (r^2)) :=
    (((jacobi.Bessel.edgeValue_summable ha).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => hbound k (r^2) (mem_singleton _))).of_norm
  have he (k:ℕ) : coshCoefficient r ((k:ℤ)+1)=
      (r*Complex.sinh r/2)*shiftedEdge (1/2) ha k (r^2) :=
    half_sine_cosh_coefficient ha r k
  simp only [he]
  exact hs.mul_left (r*Complex.sinh r/2)

end
end jacobi.EdgeResolvent
