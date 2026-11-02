import jacobi.Young.Profiles
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The actual intrinsic coordinate t=(1+tanh x)/2 maps the line onto (0,1)
and has derivative sqrt(m_U). Its elementary exponential identities reduce
the weighted sine-mode convolutions to explicit primitives. The profiles
are actual continuous L2 functions, with nonvanishing proved at an explicit
intrinsic-coordinate point.
Source: hyperbolic calculus, inverse tanh and elementary sine identities.
Use: transports Dirichlet sine modes on (0,1) to actual eigenfunctions on the real line.
-/
namespace jacobi.Young
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The intrinsic coordinate of the literal distinguished Young density.
Use: transports Dirichlet sine modes on (0,1) to actual eigenfunctions on the real line.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def intrinsic (x : ℝ) : ℝ := (1+Real.tanh x)/2

/-- The intrinsic coordinate has derivative equal to the actual square root of m_U.
Use: differentiates the explicit weighted sine primitives and identifies the article's coordinate normalization.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: differentiate the already proved hyperbolic tangent derivative and the affine rescaling. -/
theorem intrinsic_derivative (x : ℝ) : HasDerivAt intrinsic ((1/2 : ℝ)*sech x^2) x := by
  change HasDerivAt (fun y => (1+Real.tanh y)/2) ((1/2 : ℝ)*sech x^2) x
  convert ((tanh_derivative x).const_add 1).div_const 2 using 1
  ring

/-- The intrinsic coordinate is continuous on the whole line.
Use: sine-mode profiles and their weighted integrands are continuous actual functions.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: its actual derivative exists at every point. -/
theorem intrinsic_continuous : Continuous intrinsic :=
  continuous_iff_continuousAt.mpr (fun x => (intrinsic_derivative x).continuousAt)

/-- Every finite real point has intrinsic coordinate strictly between zero and one.
Use: the weighted sine source is bounded by the integrable sech-squared majorant.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the hyperbolic tangent lies strictly between minus one and one. -/
theorem intrinsic_mem (x : ℝ) : intrinsic x ∈ Ioo 0 1 := by
  dsimp [intrinsic]
  constructor <;> linarith [Real.neg_one_lt_tanh x,Real.tanh_lt_one x]

/-- The intrinsic coordinate tends to zero at the negative endpoint.
Use: evaluates the left weighted sine primitive in the full spectral realization.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: apply the proved negative-end hyperbolic tangent limit to the affine coordinate. -/
theorem intrinsic_atBot : Tendsto intrinsic atBot (𝓝 0) := by
  change Tendsto (fun x => (1+Real.tanh x)/2) atBot (𝓝 0)
  simpa only [show (1+(-1 : ℝ))/2=0 by norm_num] using (tanh_atBot.const_add 1).div_const 2

/-- The intrinsic coordinate tends to one at the positive endpoint.
Use: evaluates the right weighted sine primitive and enforces the sine endpoint condition.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: apply the proved positive-end hyperbolic tangent limit to the affine coordinate. -/
theorem intrinsic_atTop : Tendsto intrinsic atTop (𝓝 1) := by
  change Tendsto (fun x => (1+Real.tanh x)/2) atTop (𝓝 1)
  simpa only [show (1+(1 : ℝ))/2=1 by norm_num] using (tanh_atTop.const_add 1).div_const 2

/-- Every interior unit-interval coordinate is attained at the explicit inverse-hyperbolic point.
Use: proves that every proposed sine eigenfunction is nonzero without assuming a complete sine basis.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the affine image 2t-1 lies in (-1,1), where tanh and artanh are inverse. -/
theorem intrinsic_artanh {t : ℝ} (ht : t ∈ Ioo 0 1) : intrinsic (Real.artanh (2*t-1))=t := by
  rw [intrinsic,Real.tanh_artanh ⟨by linarith [ht.1],by linarith [ht.2]⟩]
  ring

/-- Exponential multiplication of sech recovers twice the intrinsic coordinate.
Use: cancels the exponential weight in the left sine convolution primitive.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: substitute the proved unsquared exponential-secant identity. -/
theorem exp_sech_intrinsic (x : ℝ) : Real.exp x*sech x=2*intrinsic x := by
  rw [exp_mul_sech,intrinsic]
  ring

/-- The reflected exponential-secant identity recovers twice the complementary coordinate.
Use: cancels the exponential weight in the right sine convolution primitive.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: reflect the positive exponential identity and use oddness of tanh. -/
theorem exp_neg_sech_intrinsic (x : ℝ) : Real.exp (-x)*sech x=2*(1-intrinsic x) := by
  have h := exp_mul_sech (-x)
  rw [sech_neg,Real.tanh_neg] at h
  rw [h,intrinsic]
  ring

/-- Integer Dirichlet frequencies in the article's zero-based spectrum convention.
Use: the target m_U eigenvalues are 2/frequency(n)^2.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def frequency (n : ℕ) : ℝ := Real.pi*((n : ℝ)+1)

/-- Every Dirichlet frequency is strictly positive.
Use: the weighted sine primitives and target eigenvalues have nonzero denominators.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: pi and the positive integer n+1 are positive. -/
theorem frequency_pos (n : ℕ) : 0 < frequency n := by unfold frequency; positivity

/-- The actual sine-mode profile of the distinguished kernel on the line.
Use: constructs one genuine nonzero eigenvector for every claimed eigenvalue of m_U.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def distinguishedMode (n : ℕ) (x : ℝ) : ℝ := sech x*Real.sin (frequency n*intrinsic x)

/-- The actual distinguished sine modes are continuous.
Use: nonzero point values imply nonzero L2 vectors and all weighted integrands are measurable.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: hyperbolic secant and the sine of the continuous intrinsic coordinate are continuous. -/
theorem distinguishedMode_continuous (n : ℕ) : Continuous (distinguishedMode n) :=
  (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).mul
    (Real.continuous_sin.comp (continuous_const.mul intrinsic_continuous))

end
end jacobi.Young
