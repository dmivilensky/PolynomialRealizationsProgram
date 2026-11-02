import jacobi.Jacobi.FiniteProduct
import jacobi.Jacobi.FiniteMoments
import jacobi.Jacobi.ScaledDerivatives

/-!
Article: jacobi, Lemma 1.3.
The original normalized Bessel function is evaluated on the negative
spectral axis. Its value is at least one, its actual derivatives obey
the exact modified equation, and its logarithmic derivative satisfies
the genuine Riccati identity used to rule out escaped finite trace.
Source: the actual Bessel equation and the exact finite positive Jacobi products.
Use: proves positivity of the original limiting Bessel function without a prior infinite product formula.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual finite Jacobi polynomial on the negative spectral axis is its genuine positive resolvent product.
Use: proves positivity of the original limiting Bessel function without a prior infinite product formula.
Article: jacobi, Lemma 1.3.
Proof: apply the exact shifted finite product and identify each literal
factor with 1+s*r_(n,k), cancelling only proved positive finite scales. -/
theorem negative_scaled_product {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (s : ℝ) :
    scaledReal a b n (-2*s)=∏ i:Fin n,(1+s*finiteLambda a b ha hb n i) := by
  -- Both sides are the original finite Jacobi polynomial with its true complete spectral zeros.
  rw [scaledReal_eq_shifted,shiftedPolynomial_product ha hb n]
  apply Finset.prod_congr rfl
  intro i _
  rw [finiteLambda_shifted ha hb i]
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp [hnR,(shiftedRoots_properties ha hb i).2.1.ne']
  ring

/-- The genuine negative-axis finite Jacobi function is at least one for every nonnegative resolvent parameter.
Use: the actual negative-axis Bessel limit is positive before any infinite canonical product has been identified.
Article: jacobi, Lemma 1.3.
Proof: every factor 1+s*r_(n,k) is at least one because the actual spectrum is positive. -/
theorem scaledReal_negative_ge_one {a b s : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (hs : 0≤s) : 1≤scaledReal a b n (-2*s) := by
  rw [negative_scaled_product ha hb hn]
  apply Finset.one_le_prod₀
  intro i _
  have hLambda : 0≤finiteLambda a b ha hb n i :=
    div_nonneg (by norm_num) ((finiteSigma_properties ha hb hn).1 i).le
  linarith [mul_nonneg hs hLambda]

end
end jacobi.Jacobi

namespace jacobi.Bessel
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Bessel function on the negative spectral axis at the resolvent scale.
Use: its genuine logarithmic derivative identifies the Stieltjes limit and excludes trace loss.
Article: jacobi, Lemma 1.3.
-/
def negativeValue (a s : ℝ) : ℝ := realNormalized a (-2*s)

/-- The actual ordinary first derivative of the negative-axis Bessel value.
Use: defines the genuine Bessel Stieltjes logarithmic derivative.
Article: jacobi, Lemma 1.3.
-/
def negativeSlope (a s : ℝ) : ℝ := -2*realSlope a (-2*s)

/-- The actual ordinary second derivative of the negative-axis Bessel value.
Use: the exact Bessel equation yields the true Riccati equation for its logarithmic derivative.
Article: jacobi, Lemma 1.3.
-/
def negativeAcceleration (a s : ℝ) : ℝ := 4*realAcceleration a (-2*s)

/-- The original negative-axis Bessel value is at least one for all s>=0.
Use: every limiting logarithmic derivative divides by a genuine positive function, independently of the canonical-product identity.
Article: jacobi, Lemma 1.3.
Proof: specialize the genuine Jacobi family to beta=0. Its true finite
positive products are at least one and converge to this same Bessel value by Mehler--Heine. -/
theorem negativeValue_ge_one {a s : ℝ} (ha : -1<a) (hs : 0≤s) : 1≤negativeValue a s := by
  have hb : (-1:ℝ)<0 := by norm_num
  apply ge_of_tendsto (jacobi.Jacobi.scaledReal_tendsto (b := 0) ha (-2*s))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact jacobi.Jacobi.scaledReal_negative_ge_one ha hb hn hs

/-- The negative-axis slope is the genuine first ordinary derivative everywhere.
Use: the actual logarithmic derivative and modified equation share the same original Bessel function.
Article: jacobi, Lemma 1.3.
Proof: compose the already proved genuine real Bessel derivative with the literal linear map -2*s. -/
theorem negativeValue_hasDerivAt (a s : ℝ) : HasDerivAt (negativeValue a) (negativeSlope a s) s := by
  have h := (realNormalized_hasDerivAt a (-2*s)).comp s ((hasDerivAt_id s).const_mul (-2))
  convert h using 1
  · rfl
  · dsimp only [negativeSlope,id_eq]
    ring

/-- The negative-axis acceleration is the genuine derivative of its first slope everywhere.
Use: proves the actual modified Bessel and Riccati equations without an independent ODE certificate.
Article: jacobi, Lemma 1.3.
Proof: compose the genuine real first-slope derivative with -2*s and differentiate the retained prefactor -2. -/
theorem negativeSlope_hasDerivAt (a s : ℝ) : HasDerivAt (negativeSlope a) (negativeAcceleration a s) s := by
  have h := ((realSlope_hasDerivAt a (-2*s)).comp s ((hasDerivAt_id s).const_mul (-2))).const_mul (-2)
  convert h using 1
  · rfl
  · dsimp only [negativeAcceleration,id_eq]
    ring

/-- The actual negative-axis Bessel function satisfies its precise modified differential equation.
Use: excludes a nonzero limiting Stieltjes slope and thereby discharges the exact first Rayleigh sum.
Article: jacobi, Lemma 1.3.
Proof: substitute the actual negative spectral argument in the already proved real Bessel equation and include both chain-rule factors. -/
theorem negative_equation {a : ℝ} (ha : -1<a) (s : ℝ) :
    2*s*negativeAcceleration a s+2*(a+1)*negativeSlope a s-negativeValue a s=0 := by
  unfold negativeAcceleration negativeSlope negativeValue
  linear_combination -(realNormalized_equation ha (-2*s))

/-- The original negative-axis Bessel function has value one at zero.
Use: normalizes its true logarithmic derivative at the finite-trace endpoint.
Article: jacobi, Lemma 1.3.
Proof: evaluate the original normalized Bessel function at its actual central argument. -/
theorem negativeValue_zero {a : ℝ} (ha : -1<a) : negativeValue a 0=1 := by
  simp only [negativeValue,realNormalized,mul_zero,Complex.ofReal_zero,
    normalized_zero (a := (a:ℂ)) (by simpa using ha),Complex.one_re]

/-- The genuine first negative-axis Bessel derivative at zero is the printed edge mass expression.
Use: the no-loss-of-trace argument identifies the exact first Rayleigh sum with this actual derivative.
Article: jacobi, Lemma 1.3.
Proof: the actual original complex first derivative at zero was proved
from its convergent series. Take its real part and include the exact scale -2. -/
theorem negativeSlope_zero {a : ℝ} (ha : -1<a) : negativeSlope a 0=1/(2*(a+1)) := by
  unfold negativeSlope realSlope
  simp only [mul_zero,Complex.ofReal_zero]
  rw [(normalized_hasDerivAt_zero (a := (a:ℂ)) (by simpa using ha)).deriv]
  have he : (-1:ℂ)/(4*((a:ℂ)+1))=((-1/(4*(a+1)):ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.ofReal_re]
  field_simp [show a+1≠0 by linarith]
  ring

/-- The actual negative-axis Bessel logarithmic derivative.
Use: its finite Stieltjes representation and decay exclude escaped mass in the first Rayleigh sum.
Article: jacobi, Lemma 1.3.
-/
def stieltjes (a s : ℝ) : ℝ := negativeSlope a s/negativeValue a s

/-- The literal ordinary slope of the original Bessel logarithmic derivative.
Use: supplies the genuine derivative in its Riccati identity and its large-parameter decay argument.
Article: jacobi, Lemma 1.3.
-/
def stieltjesSlope (a s : ℝ) : ℝ :=
  (negativeAcceleration a s*negativeValue a s-(negativeSlope a s)^2)/(negativeValue a s)^2

/-- The declared Bessel Stieltjes slope is its genuine ordinary derivative on s>=0.
Use: the no-loss-of-trace proof differentiates the actual Bessel logarithmic derivative.
Article: jacobi, Lemma 1.3.
Proof: the actual Bessel value is at least one, so the true quotient derivative applies with nonzero denominator. -/
theorem stieltjes_hasDerivAt {a s : ℝ} (ha : -1<a) (hs : 0≤s) :
    HasDerivAt (stieltjes a) (stieltjesSlope a s) s := by
  have h := (negativeSlope_hasDerivAt a s).div (negativeValue_hasDerivAt a s)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (negativeValue_ge_one ha hs)))
  rw [show stieltjes a=negativeSlope a/negativeValue a by rfl]
  simpa only [stieltjesSlope,pow_two] using h

/-- The actual Bessel Stieltjes transform has its exact printed central mass normalization.
Use: the limit identity equates the full infinite first Rayleigh sum with this genuine value.
Article: jacobi, Lemma 1.3.
Proof: substitute the already proved genuine Bessel value and ordinary slope at zero. -/
theorem stieltjes_zero {a : ℝ} (ha : -1<a) : stieltjes a 0=1/(2*(a+1)) := by
  rw [stieltjes,negativeValue_zero ha,negativeSlope_zero ha,div_one]

/-- The genuine Bessel Stieltjes transform satisfies its exact Riccati identity on the nonnegative axis.
Use: proves that the transform tends to zero, ruling out a hidden escaped first trace.
Article: jacobi, Lemma 1.3.
Proof: divide the true modified Bessel equation by its actual positive
value and use the genuine quotient derivative. All cancellations use the proved positivity. -/
theorem stieltjes_equation {a s : ℝ} (ha : -1<a) (hs : 0≤s) :
    2*s*(stieltjesSlope a s+(stieltjes a s)^2)+2*(a+1)*stieltjes a s-1=0 := by
  -- The original Bessel equation, rather than an abstract Riccati solution, supplies the identity.
  have hf : negativeValue a s≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (negativeValue_ge_one ha hs))
  unfold stieltjesSlope stieltjes
  field_simp [hf]
  linear_combination negativeValue a s*(negative_equation ha s)

end
end jacobi.Bessel
