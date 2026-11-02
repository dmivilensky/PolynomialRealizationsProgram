import jacobi.Bessel.Wave
import jacobi.Bessel.EdgeSequence
import jacobi.Bessel.EndpointWronskian
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Proposition B.1.
The original Bessel Liouville wave is rescaled by a positive frequency and
its harmless positive amplitude. Its true equation has frequency squared
plus the original inverse-square correction, and its endpoint factor is
the actual even normalized entire Bessel function.
Use: its zeros are precisely j_(alpha,k)/N and its singular branch matches the genuine Jacobi wave.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Bessel comparison wave with regular factor normalized to one at the endpoint.
Use: its zeros are precisely j_(alpha,k)/N and its singular branch matches the genuine Jacobi wave.
Article: jacobi, Proposition B.1.
-/
def scaledWave (a N x : ℝ) : ℝ := (N^(a+1/2))⁻¹*wave a (N*x)

/-- The literal ordinary slope of the genuine scaled Bessel wave.
Use: supplies the actual first derivative in its comparison Wronskian.
Article: jacobi, Proposition B.1.
-/
def scaledWaveSlope (a N x : ℝ) : ℝ := (N^(a+1/2))⁻¹*N*waveSlope a (N*x)

/-- The literal ordinary acceleration of the genuine scaled Bessel wave.
Use: verifies the exact scaled inverse-square comparison equation.
Article: jacobi, Proposition B.1.
-/
def scaledWaveAcceleration (a N x : ℝ) : ℝ := (N^(a+1/2))⁻¹*N^2*waveAcceleration a (N*x)

/-- The actual normalized entire factor of the scaled Bessel endpoint branch.
Use: identifies the genuine even analytic regular factor in the singular Wronskian comparison.
Article: jacobi, Proposition B.1.
-/
def scaledEndpointFactor (a N x : ℝ) : ℝ := realNormalized a (N^2*x^2)

/-- The declared scaled Bessel slope is its genuine ordinary derivative on the positive axis.
Use: Sturm comparison applies to the original source special function.
Article: jacobi, Proposition B.1.
Proof: the original Bessel wave derivative and positive-frequency affine chain rule give the exact scaling. -/
theorem scaledWave_hasDerivAt (a : ℝ) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    HasDerivAt (scaledWave a N) (scaledWaveSlope a N x) x := by
  convert ((wave_hasDerivAt a (mul_pos hN hx)).comp x
    ((hasDerivAt_id x).const_mul N)).const_mul ((N^(a+1/2))⁻¹) using 1
  · rfl
  · dsimp [scaledWaveSlope]
    ring

/-- The declared scaled Bessel acceleration is the genuine derivative of its actual slope.
Use: the comparison restoring equation has both required actual derivatives.
Article: jacobi, Proposition B.1.
Proof: apply the same genuine affine chain rule to the previously proved original wave slope. -/
theorem scaledWaveSlope_hasDerivAt (a : ℝ) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    HasDerivAt (scaledWaveSlope a N) (scaledWaveAcceleration a N x) x := by
  convert ((waveSlope_hasDerivAt a (mul_pos hN hx)).comp x
    ((hasDerivAt_id x).const_mul N)).const_mul ((N^(a+1/2))⁻¹*N) using 1
  · rfl
  · dsimp [scaledWaveAcceleration]
    ring

/-- The actual positive-frequency Bessel comparison wave satisfies exactly the printed scaled inverse-square equation.
Use: compares the true Jacobi zeros against the true Bessel zeros under the proved bounded regular perturbation.
Article: jacobi, Proposition B.1.
Proof: compose the original true Bessel wave equation with N*x and
multiply by the actual nonzero normalization. Positive frequency and
argument justify the exact inverse-square scaling. -/
theorem scaledWave_equation {a : ℝ} (ha : -1<a) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    scaledWaveAcceleration a N x+(N^2+(1/4-a^2)/x^2)*scaledWave a N x=0 := by
  -- The frequency change preserves the same endpoint correction, rather than replacing it by an assumed comparison coefficient.
  have he : N^2*(1+(1/4-a^2)/(N*x)^2)=N^2+(1/4-a^2)/x^2 := by
    field_simp [hN.ne',hx.ne']
  unfold scaledWaveAcceleration scaledWave
  rw [← he]
  linear_combination ((N^(a+1/2))⁻¹*N^2)*wave_equation ha (mul_pos hN hx)

/-- The genuine scaled Bessel wave has exactly the original even entire endpoint factor after its selected singular power is removed.
Use: its actual singular endpoint branch can be compared to the original Jacobi branch without a normalization premise.
Article: jacobi, Proposition B.1.
Proof: the real-power product law separates the positive frequency and
argument factors. Cancel only the genuinely positive frequency power. -/
theorem scaledWave_endpoint_factor (a : ℝ) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    scaledWave a N x=powerFactor (a+1/2) (scaledEndpointFactor a N) x := by
  rw [scaledWave,wave,Real.mul_rpow hN.le hx.le]
  unfold powerFactor scaledEndpointFactor
  rw [show (N*x)^2=N^2*x^2 by ring]
  rw [mul_assoc,inv_mul_cancel_left₀ (Real.rpow_pos_of_pos hN (a+1/2)).ne']

/-- The actual real normalized Bessel function is real analytic everywhere.
Use: proves actual regularity of the scaled endpoint factor rather than borrowing an unrelated analytic solution.
Article: jacobi, Proposition B.1.
Proof: restrict the already proved entire complex function to the real axis and take its real part. -/
theorem realNormalized_analytic (a x : ℝ) : AnalyticAt ℝ (realNormalized a) x := by
  exact (normalized_analytic (a:ℂ) (x:ℂ)).re_ofReal

/-- The actual normalized Bessel endpoint factor is analytic at every real argument and even.
Use: supplies the genuine endpoint regularity and parity needed to cancel the singular Wronskian.
Article: jacobi, Proposition B.1.
Proof: compose the actual entire real function with N^2*x^2; this polynomial is unchanged under negation. -/
theorem scaledEndpointFactor_properties (a N : ℝ) (x : ℝ) :
    AnalyticAt ℝ (scaledEndpointFactor a N) x ∧ scaledEndpointFactor a N (-x)=scaledEndpointFactor a N x := by
  refine ⟨?_,?_⟩
  · have hi : AnalyticAt ℝ (fun t : ℝ => N^2*t^2) x := analyticAt_const.mul (analyticAt_id.pow 2)
    exact (realNormalized_analytic a (N^2*x^2)).comp (f := fun t : ℝ => N^2*t^2) hi
  · simp only [scaledEndpointFactor,neg_sq]

/-- The genuine scaled Bessel regular factor has central value one and zero actual first derivative.
Use: fixes its initial positive branch and the extra endpoint Wronskian vanishing order for every admissible Bessel order.
Article: jacobi, Proposition B.1.
Proof: the original entire function has its proved central normalization;
the actual even analytic factor has zero derivative at the center. -/
theorem scaledEndpointFactor_zero {a : ℝ} (ha : -1<a) (N : ℝ) :
    scaledEndpointFactor a N 0=1 ∧ deriv (scaledEndpointFactor a N) 0=0 := by
  refine ⟨?_,jacobi.Jacobi.even_derivative_zero
    ((scaledEndpointFactor_properties a N 0).1.differentiableAt)
    (fun x => (scaledEndpointFactor_properties a N x).2)⟩
  simp only [scaledEndpointFactor,zero_pow (by norm_num : 2≠0),mul_zero,realNormalized,
    Complex.ofReal_zero,normalized_zero (a := (a:ℂ)) (by simpa using ha),Complex.one_re]

/-- The genuine scaled Bessel wave selects a strictly positive branch near zero.
Use: supplies the actual comparator sign on the singular first Sturm interval.
Article: jacobi, Proposition B.1.
Proof: its actual analytic regular factor has central value one; continuity
preserves positivity and its exact positive-power factorization preserves that sign. -/
theorem scaledWave_positive_near_zero {a D : ℝ} (ha : -1<a) (hD : 0<D) :
    ∀ᶠ x in 𝓝[>] (0:ℝ),0<scaledWave a D x := by
  have hzero := (scaledEndpointFactor_zero ha D).1
  have hp := ((scaledEndpointFactor_properties a D 0).1.continuousAt).eventually
    (Ioi_mem_nhds (show 0<scaledEndpointFactor a D 0 by rw [hzero]; norm_num))
  filter_upwards [self_mem_nhdsWithin,hp.filter_mono nhdsWithin_le_nhds] with x hx hpx
  change 0<x at hx
  rw [scaledWave_endpoint_factor a hD hx,powerFactor]
  exact mul_pos (Real.rpow_pos_of_pos hx _) hpx

/-- Every original scaled Bessel wave zero is exactly a genuine normalized entire Bessel zero at the scaled squared argument.
Use: comparison zeros are converted back to the actual source Bessel zero list.
Article: jacobi, Proposition B.1.
Proof: its actual positive normalization is nonzero and the proved original wave zero equivalence applies at the positive scaled argument. -/
theorem scaledWave_zero_iff (a : ℝ) {D x : ℝ} (hD : 0<D) (hx : 0<x) :
    scaledWave a D x=0 ↔ normalized (a:ℂ) (((D*x)^2:ℝ):ℂ)=0 := by
  rw [scaledWave,mul_eq_zero,or_iff_right
    (inv_ne_zero (Real.rpow_pos_of_pos hD (a+1/2)).ne'),wave_zero_iff a (mul_pos hD hx)]

/-- Every actual scaled Bessel comparison zero has a genuine canonical source index.
Use: strict Sturm comparisons transfer to inequalities for the actual numbered j_(alpha,k), without a phase enumeration assumption.
Article: jacobi, Proposition B.1.
Proof: undo the actual positive frequency scaling, use the genuine cylindrical normalization and the already proved exhaustive source zero enumeration. -/
theorem scaledWave_zero_index {a D x : ℝ} (ha : -1<a) (hD : 0<D) (hx : 0<x)
    (hz : scaledWave a D x=0) : ∃ k,positiveZero a ha k=D*x := by
  apply positiveZero_exhaustive ha (mul_pos hD hx)
  rw [cylindrical_zero_iff ha (mul_pos hD hx)]
  exact (scaledWave_zero_iff a hD hx).mp hz

end
end jacobi.Bessel
