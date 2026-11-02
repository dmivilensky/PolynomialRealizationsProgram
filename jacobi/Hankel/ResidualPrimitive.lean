import jacobi.Hankel.PolynomialRay
import jacobi.Hankel.FourierTail
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
Article: jacobi, Lemma E.1.
Its spatial derivatives, absolute integrability and both primitive
endpoint values are proved. This is the exact residual identity
needed to bound the true outgoing amplitude by the local inverse.
Use: polynomial_source_integrable discharges all actual improper integrability premises in the outgoing residual primitive.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every genuine complex reciprocal integer power of order at least two is integrable on the original positive outgoing ray.
Use: polynomial_source_integrable discharges all actual improper integrability premises in the outgoing residual primitive.
Article: jacobi, Lemma E.1.
Proof: use the community real improper-power theorem and the actual real inclusion into the complex plane; the original integer power identities identify its integrand exactly. -/
theorem complex_inversePower_integrable {x : ℝ} (hx : 0<x) (n : ℕ) (hn : 2≤n) :
    IntegrableOn (fun y : ℝ => (y:ℂ)⁻¹^n) (Ioi x) := by
  have he : -(n:ℝ)< -1 := by exact_mod_cast (by omega : -(n:ℤ)< -1)
  have h := (integrableOn_Ioi_rpow_of_lt he hx).ofReal (𝕜 := ℂ)
  convert! h using 1
  funext y
  simp only [Real.rpow_neg_eq_inv_rpow,Real.rpow_natCast,RCLike.ofReal_pow,RCLike.ofReal_inv]
  rfl

/-- The actual spatial Liouville source of the original Hankel polynomial is genuinely integrable on every positive outgoing ray.
Use: polynomial_outgoing_identity applies the true improper FTC to its original Green primitive.
Article: jacobi, Lemma E.1.
Proof: both original spatial derivatives are finite complex linear combinations of inverse powers of orders two, three and four, all genuinely integrable by the proved real-power tail theorem. -/
theorem polynomial_source_integrable (c : ℂ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun y : ℝ => amplitudePolynomialCurvature c y+
      2*Complex.I*amplitudePolynomialSlope c y) (Ioi x) := by
  -- This argument proves convergence of the actual derivative source before taking its improper integral.
  have h2 := complex_inversePower_integrable hx 2 le_rfl
  have h3 := complex_inversePower_integrable hx 3 (by omega)
  have h4 := complex_inversePower_integrable hx 4 (by omega)
  have hs : IntegrableOn (amplitudePolynomialSlope c) (Ioi x) := by
    have he : amplitudePolynomialSlope c=(fun y : ℝ =>
        (Complex.I*c/2)*(y:ℂ)⁻¹^2+(c*(c+2)/4)*(y:ℂ)⁻¹^3) := by
      funext y
      simp only [amplitudePolynomialSlope,div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [he]
    exact (h2.const_mul (Complex.I*c/2)).add (h3.const_mul (c*(c+2)/4))
  have hc : IntegrableOn (amplitudePolynomialCurvature c) (Ioi x) := by
    have he : amplitudePolynomialCurvature c=(fun y : ℝ =>
        (-Complex.I*c)*(y:ℂ)⁻¹^3-(3*c*(c+2)/4)*(y:ℂ)⁻¹^4) := by
      funext y
      simp only [amplitudePolynomialCurvature,div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [he]
    exact (h3.const_mul (-Complex.I*c)).sub (h4.const_mul (3*c*(c+2)/4))
  exact hc.add (hs.const_mul (2*Complex.I))

/-- The original bounded outgoing kernel times the actual Hankel polynomial source is genuinely integrable.
Use: polynomial_outgoing_identity evaluates this same actual improper integral by a proved primitive.
Article: jacobi, Lemma E.1.
Proof: the original causal kernel is continuous and bounded by one; multiply it by the independently proved integrable actual source. -/
theorem polynomial_kernel_source_integrable (c : ℂ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun y : ℝ => outgoingKernel (y-x)*(amplitudePolynomialCurvature c y+
      2*Complex.I*amplitudePolynomialSlope c y)) (Ioi x) :=
  (polynomial_source_integrable c hx).bdd_mul
    ((outgoingKernel_continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall (fun y => outgoingKernel_norm_le (y-x)))

/-- The genuine outgoing Green primitive for the original Hankel polynomial.
Use: polynomialGreenPrimitive_derivative and its actual endpoint values prove the exact improper residual equation.
Article: jacobi, Lemma E.1.
-/
def polynomialGreenPrimitive (c : ℂ) (x y : ℝ) : ℂ :=
  outgoingKernel (y-x)*amplitudePolynomialSlope c y-(amplitudePolynomial c y-1)

/-- The original polynomial Green primitive has exactly the genuine outgoing Liouville integrand as derivative above the original diagonal.
Use: polynomial_outgoing_identity invokes the actual improper FTC with this true derivative.
Article: jacobi, Lemma E.1.
Proof: apply the ordinary product rule to the actual kernel and the proved polynomial derivatives; Euler's exact kernel identity cancels the first-derivative terms. -/
theorem polynomialGreenPrimitive_derivative (c : ℂ) {x y : ℝ} (hx : 0<x) (hy : x<y) :
    HasDerivAt (polynomialGreenPrimitive c x)
      (outgoingKernel (y-x)*(amplitudePolynomialCurvature c y+
        2*Complex.I*amplitudePolynomialSlope c y)) y := by
  -- The genuine causal kernel is differentiated only strictly above its original moving diagonal.
  have hn : y≠0 := (hx.trans hy).ne'
  have hd : HasDerivAt (fun t : ℝ => t-x) 1 y := by
    simpa only [id_eq] using (hasDerivAt_id y).sub_const x
  have hk := (outgoingKernel_hasDerivAt (sub_pos.mpr hy)).scomp y hd
  have he := (eq_div_iff (mul_ne_zero (by norm_num : (2:ℂ)≠0) Complex.I_ne_zero)).mp
    (outgoingKernel_exponential (sub_pos.mpr hy).le)
  convert! (hk.mul (amplitudePolynomialSlope_hasDerivAt c hn)).sub
    ((amplitudePolynomial_hasDerivAt c hn).sub_const 1) using 1
  simp only [one_smul,Function.comp_def]
  linear_combination (amplitudePolynomialSlope c y)*he

/-- The actual original outgoing polynomial Green primitive tends to zero at infinity.
Use: polynomial_outgoing_identity has its upper improper endpoint fully discharged.
Article: jacobi, Lemma E.1.
Proof: the genuine kernel is bounded by one, the proved true polynomial slope tends to zero, and the actual polynomial tends to one. -/
theorem polynomialGreenPrimitive_limit (c : ℂ) (x : ℝ) :
    Tendsto (polynomialGreenPrimitive c x) atTop (𝓝 0) := by
  have hk : IsBoundedUnder (·≤·) atTop (norm ∘ fun y : ℝ => outgoingKernel (y-x)) :=
    isBoundedUnder_of ⟨1,fun y => outgoingKernel_norm_le (y-x)⟩
  convert! (isBoundedUnder_le_mul_tendsto_zero hk
    (amplitudePolynomialSlope_limit c)).sub ((amplitudePolynomial_limit c).sub_const 1) using 1
  simp only [sub_self]

/-- The actual outgoing Hankel polynomial satisfies its exact original improper Green identity on every positive real ray.
Use: its genuine fourth-order Liouville residual is integrated through the same original outgoing operator, giving the cubic error of the actual analytic Jost amplitude via tailInverse_bound.
Article: jacobi, Lemma E.1.
Proof: the actual Green primitive has the proved source derivative, the source is genuinely integrable, and its true upper limit is zero. Its lower value is 1-p(x) because the original kernel vanishes on the diagonal. Apply the community improper FTC. -/
theorem polynomial_outgoing_identity (c : ℂ) {x : ℝ} (hx : 0<x) :
    (∫ y in Ioi x,outgoingKernel (y-x)*(amplitudePolynomialCurvature c y+
      2*Complex.I*amplitudePolynomialSlope c y))=amplitudePolynomial c x-1 := by
  -- No outgoing endpoint or integration-by-parts remainder is assumed: both are values of the proved genuine primitive.
  have hp := amplitudePolynomial_hasDerivAt c hx.ne'
  have hs := amplitudePolynomialSlope_hasDerivAt c hx.ne'
  have hc : ContinuousAt (polynomialGreenPrimitive c x) x :=
    (((outgoingKernel_continuous.comp (continuous_id.sub continuous_const)).continuousAt).mul
      hs.continuousAt).sub (hp.continuousAt.sub continuousAt_const)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt
    (fun y hy => polynomialGreenPrimitive_derivative c hx hy)
    (polynomial_kernel_source_integrable c hx) (polynomialGreenPrimitive_limit c x)
  simpa only [polynomialGreenPrimitive,sub_self,outgoingKernel_zero le_rfl,zero_mul,
    zero_sub,neg_sub] using h

end
end jacobi.Hankel
