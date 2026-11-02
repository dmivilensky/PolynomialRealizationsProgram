import jacobi.Young.SineConvolution
import chebyshev2.Continuum.Eigenframe

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The explicit sine profiles define genuine nonzero vectors in the existing
real L2 space. The literal convolution identity becomes the actual compact
kernel operator's eigenvector equation. Distinct frequencies produce
orthogonal vectors, so finite normalized families can be used in min--max.
Source: self-adjointness of positive Green operators and Hilbert-space min--max.
Use: converts the explicit pointwise function into an actual operator eigenvector.
-/
namespace jacobi.Young
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Every distinguished sine mode belongs to the genuine L2 domain.
Use: converts the explicit pointwise function into an actual operator eigenvector.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the squared profile is bounded by the integrable sech-squared function. -/
theorem distinguishedMode_memLp (n : ℕ) : MemLp (distinguishedMode n) 2 volume := by
  -- Oscillatory factors have absolute value at most one, uniformly in the mode.
  apply (memLp_two_iff_integrable_sq (distinguishedMode_continuous n).aestronglyMeasurable).mpr
  refine sech_sq_integrable.mono' ((distinguishedMode_continuous n).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change (sech x*Real.sin (frequency n*intrinsic x))^2 ≤ sech x^2
  rw [mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.sin_sq_le_one _)

/-- The actual L2 vector represented by the nth intrinsic sine profile.
Use: finite normalized eigenframes give lower bounds for the actual sorted spectrum.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def sineVector (n : ℕ) : FeatureSpace := (distinguishedMode_memLp n).toLp (distinguishedMode n)

/-- The L2 representative agrees almost everywhere with the explicit profile.
Use: identifies the already constructed integral operator with the pointwise convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the standard Lp construction preserves its input almost everywhere. -/
theorem sineVector_coe (n : ℕ) : sineVector n =ᵐ[volume] distinguishedMode n :=
  (distinguishedMode_memLp n).coeFn_toLp

/-- Every sine profile takes a strictly positive value at an explicit point.
Use: proves nonvanishing of the genuine L2 eigenvector without a basis assumption.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: choose t=1/(2(n+1)), invert the intrinsic coordinate, and obtain sine(pi/2)=1. -/
theorem distinguishedMode_nonzero (n : ℕ) : ∃ x, 0 < distinguishedMode n x := by
  -- The chosen point lies at the first antinode, even for high frequencies.
  let t : ℝ := 1/(2*((n : ℝ)+1))
  have hn : 0 < (n : ℝ)+1 := by positivity
  have ht : t ∈ Ioo 0 1 := by
    constructor
    · dsimp [t]; positivity
    · dsimp [t]; apply (div_lt_one (by positivity)).mpr
      linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  refine ⟨Real.artanh (2*t-1),?_⟩
  rw [distinguishedMode,intrinsic_artanh ht]
  have hf : frequency n*t=Real.pi/2 := by
    dsimp [frequency,t]
    field_simp [hn.ne']
  rw [hf,Real.sin_pi_div_two,mul_one]
  exact sech_pos _

/-- Every constructed L2 eigenvector is nonzero.
Use: normalization yields actual orthonormal finite frames.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: a continuous profile which vanishes almost everywhere vanishes everywhere,
contradicting its explicit positive antinode. -/
theorem sineVector_ne_zero (n : ℕ) : sineVector n ≠ 0 := by
  intro hz
  have he : distinguishedMode n =ᵐ[volume] (0 : ℝ → ℝ) := by
    exact (sineVector_coe n).symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 volume)
  have h := ((distinguishedMode_continuous n).ae_eq_iff_eq volume continuous_zero).mp he
  obtain ⟨x,hx⟩ := distinguishedMode_nonzero n
  simp only [h,Pi.zero_apply,lt_self_iff_false] at hx

/-- The target positive eigenvalues in the article's zero-based convention.
Use: the eigenvector equations and trace exhaustion identify the whole ordered spectrum.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def sineEigenvalue (n : ℕ) : ℝ := 2/frequency n^2

/-- Every explicit sine profile is an eigenvector of the actual kernel operator.
Use: min--max supplies the lower bound for every sorted eigenvalue of m_U.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: replace the L2 representative almost everywhere, multiply by sqrt(m_U),
and apply the proved literal exponential convolution identity. -/
theorem sineVector_equation (n : ℕ) :
    kernelOperator distinguishedDensity.integrable distinguishedDensity.nonneg (sineVector n)=
      sineEigenvalue n • sineVector n := by
  -- Equality is established inside L2, rather than postulated for abstract spectral data.
  apply Lp.ext
  filter_upwards [kernelOperator_coe distinguishedDensity.integrable distinguishedDensity.nonneg
    (sineVector n),Lp.coeFn_smul (sineEigenvalue n) (sineVector n),sineVector_coe n] with x hx hs hf
  rw [hx,hs]
  change Real.sqrt (distinguished x)*(∫ y, Real.exp (-|x-y|)*Real.sqrt (distinguished y)*sineVector n y)=
    sineEigenvalue n*sineVector n x
  rw [hf]
  have he : (∫ y, Real.exp (-|x-y|)*Real.sqrt (distinguished y)*sineVector n y)=
      ∫ y, Real.exp (-|x-y|)*sineSource (frequency n) y := by
    apply integral_congr_ae
    filter_upwards [sineVector_coe n] with y hy
    rw [hy,distinguished_sqrt]
    dsimp [distinguishedMode,sineSource]
    ring
  rw [he,sineSource_convolution]
  rfl

end
end jacobi.Young
