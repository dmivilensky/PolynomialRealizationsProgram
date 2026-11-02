import jacobi.Elliptic.EulerEquation
import jacobi.Variational.PositivePartCalculus
import jacobi.Young.H1Scaling

/-!
Article: jacobi, Theorem D.5.
The actual KKT coefficients give the article's exact scale a=27/(16mu),
shift sigma=-lambda/a and state y=(2mu*W_2-lambda)/a. Its genuine classical
equation is -y''+4y=4sigma+6y_+², and the density is (4/9)a²y_+².
Source: exact rescaling of the proved original Green Euler equation.
Use: normalizes the clipped semilinear coefficient to six.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The positive amplitude scale determined by the actual spectral multiplier.
Use: normalizes the clipped semilinear coefficient to six.
Article: jacobi, Theorem D.5.
-/
def eulerScale (μ : ℝ) : ℝ := 27/(16*μ)

/-- The normalized nonpositive mass shift.
Use: is the parameter of the actual optimizer's cubic first integral.
Article: jacobi, Theorem D.5.
-/
def eulerShift (μ l : ℝ) : ℝ := -l/eulerScale μ

/-- The normalized actual optimizing Green state.
Use: its clipped cubic first integral gives the elliptic quadratures.
Article: jacobi, Theorem D.5.
-/
def eulerState (m : Density) (μ l : ℝ) (x : ℝ) : ℝ :=
  (2*μ*potential m x-l)/eulerScale μ

/-- The actual normalized state's classical derivative.
Use: expresses the conserved energy and the quadrature Jacobian without an assumed slope variable.
Article: jacobi, Theorem D.5.
-/
def eulerSlope (m : Density) (μ : ℝ) (x : ℝ) : ℝ :=
  (2*μ/eulerScale μ)*potentialSlope m x

/-- A positive spectral multiplier gives a strictly positive normalization scale.
Use: licenses all divisions and positive-part rescalings in the normalized optimizer ODE.
Article: jacobi, Theorem D.5.
Proof: both numerator and denominator of the printed scale are positive. -/
theorem eulerScale_pos {μ : ℝ} (hμ : 0<μ) : 0<eulerScale μ := by unfold eulerScale; positivity

/-- The positive-part coefficient rescales with the actual positive normalization amplitude.
Use: identifies the original Euler density with (4/9)a²y_+².
Article: jacobi, Theorem D.5.
Proof: reconstruct c=a*y and split according to the sign of y. -/
theorem eulerPositivePart_scale (m : Density) {μ : ℝ} (hμ : 0<μ) (l x : ℝ) :
    max (2*μ*potential m x-l) 0=eulerScale μ*max (eulerState m μ l x) 0 := by
  -- Positivity of a is essential when the clipped state vanishes.
  have ha := eulerScale_pos hμ
  have he : 2*μ*potential m x-l=eulerScale μ*eulerState m μ l x := by
    unfold eulerState
    field_simp
  rw [he]
  by_cases hy : eulerState m μ l x≤0
  · rw [max_eq_right hy,max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha.le hy),mul_zero]
  · have hyp := (lt_of_not_ge hy).le
    rw [max_eq_left hyp,max_eq_left (mul_nonneg ha.le hyp)]

/-- The actual Euler density is exactly the article's normalized positive-part square.
Use: transfers mass, energy and moment normalization to the state y.
Article: jacobi, Theorem D.5.
Proof: substitute the proved positive-part scaling and square the scalar factor. -/
theorem eulerDensity_normalized (m : Density) {μ : ℝ} (hμ : 0<μ) (l x : ℝ) :
    eulerDensity m μ l x=(4/9:ℝ)*(eulerScale μ)^2*(max (eulerState m μ l x) 0)^2 := by
  rw [eulerDensity,eulerPositivePart_scale m hμ,mul_pow]
  ring

/-- The normalized Green state has its declared derivative at every point.
Use: the elliptic first-integral proof differentiates the actual constructed state.
Article: jacobi, Theorem D.5.
Proof: differentiate the affine potential transformation and collect its constant factor. -/
theorem eulerState_hasDerivAt (m : Density) (μ l x : ℝ) :
    HasDerivAt (eulerState m μ l) (eulerSlope m μ x) x := by
  convert (((potential_hasDerivAt m x).const_mul (2*μ)).sub_const l).div_const (eulerScale μ) using 1
  · rfl
  · unfold eulerSlope
    ring

/-- The actual optimizer's normalized state obeys the printed classical clipped semilinear equation.
Use: its zero first integral and turning height determine the elliptic profile and quadratures.
Article: jacobi, Theorem D.5.
Proof: rescale the genuine original Green Euler equation. The exact choice
a=27/(16mu) makes its nonlinear coefficient equal to six. -/
theorem eulerState_equation (m : Density) {μ : ℝ} (hμ : 0<μ) (l : ℝ)
    (he : m.value=ᵐ[volume] eulerDensity m μ l) (x : ℝ) :
    HasDerivAt (eulerSlope m μ)
      (4*(eulerState m μ l x-eulerShift μ l)-6*(max (eulerState m μ l x) 0)^2) x := by
  -- The clipping is rescaled before the numerical normalization is simplified.
  have h := (eulerPotential_classical m μ l he x).const_mul (2*μ/eulerScale μ)
  convert h using 1
  · rfl
  · rw [eulerPositivePart_scale m hμ]
    unfold eulerState eulerShift eulerScale
    field_simp
    ring

/-- The normalized state relative to its limiting shift and its actual slope have finite H1 energy.
Use: integrability forces the constant of the clipped first integral to be zero.
Article: jacobi, Theorem D.5.
Proof: y-sigma and its slope are constant multiples of the actual H1 potential and its derivative. -/
theorem eulerState_integrable (m : Density) (μ l : ℝ) :
    Integrable (fun x => (eulerState m μ l x-eulerShift μ l)^2) ∧
      Integrable (fun x => (eulerSlope m μ x)^2) := by
  have he (x : ℝ) : eulerState m μ l x-eulerShift μ l=(2*μ/eulerScale μ)*potential m x := by
    unfold eulerState eulerShift
    ring
  simp_rw [he,eulerSlope,mul_pow]
  exact ⟨(potential_sobolev m).value_memLp.integrable_sq.const_mul _,
    (potential_sobolev m).derivative_memLp.integrable_sq.const_mul _⟩

end
end jacobi.Elliptic
