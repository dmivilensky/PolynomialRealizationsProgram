import jacobi.Oscillation.PerturbedInvariant
import jacobi.Oscillation.PhasePerturbation

/-!
Article: jacobi, Proposition B.1.
The exact corrected Bessel phase derivative is uniformly Lipschitz in
its phase coordinate with an integrable fourth-order coefficient. This
allows the genuinely proved linear finite-phase perturbation estimate
to control the difference of the two actual invariant derivatives.
Use: bounds the exact oscillatory products in the actual corrected phase derivative.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- A product of two unit-bounded coordinates has the sum of their two Lipschitz constants.
Use: bounds the exact oscillatory products in the actual corrected phase derivative.
Article: jacobi, Proposition B.1.
Proof: split the product difference at the mixed product and apply the triangle inequality. -/
theorem unit_product_difference {a b c d K L : ℝ} (ha : |a|≤1) (hd : |d|≤1)
    (hbc : |b-d|≤K) (hac : |a-c|≤L) (hL : 0≤L) :
    |a*b-c*d|≤K+L := by
  rw [show a*b-c*d=a*(b-d)+(a-c)*d by ring]
  calc
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ ≤ 1*K+L*1 := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul ha hbc (abs_nonneg _) (by norm_num))
        (mul_le_mul hac hd (abs_nonneg _) hL)
    _ = _ := by ring

/-- Double-angle sine and cosine have their actual uniform two-Lipschitz bounds.
Use: compares the original phase invariants without assuming small pointwise oscillatory errors.
Article: jacobi, Proposition B.1.
Proof: apply the community one-Lipschitz estimates to the doubled actual arguments. -/
theorem double_angle_lipschitz (u v : ℝ) :
    |cos (2*u)-cos (2*v)|≤2*|u-v| ∧ |sin (2*u)-sin (2*v)|≤2*|u-v| := by
  have he : |2*u-2*v|=2*|u-v| := by rw [← mul_sub,abs_mul]; norm_num
  exact ⟨(Real.abs_cos_sub_cos_le _ _).trans_eq he,(Real.abs_sin_sub_sin_le _ _).trans_eq he⟩

/-- Both actual trigonometric products in the corrected phase derivative have a global four-Lipschitz bound.
Use: the difference of the true Bessel and finite invariant derivatives gains the already proved small actual phase difference.
Article: jacobi, Proposition B.1.
Proof: each double-angle coordinate is unit bounded and two-Lipschitz;
the genuine sine square is unit bounded and two-Lipschitz. Apply the
proved elementary product-difference bound. -/
theorem phase_products_lipschitz (u v : ℝ) :
    |cos (2*u)*sin u^2-cos (2*v)*sin v^2|≤4*|u-v| ∧
      |sin (2*u)*sin u^2-sin (2*v)*sin v^2|≤4*|u-v| := by
  -- The two bounded factors have separate true two-Lipschitz estimates, which add under the exact mixed-product decomposition.
  have hs : |sin v^2|≤1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq v,sq_nonneg (cos v)]
  have hD := double_angle_lipschitz u v
  constructor
  · have hh := unit_product_difference (Real.abs_cos_le_one _) hs (abs_sin_sq_sub_le u v) hD.1
      (by positivity : 0≤2*|u-v|)
    linarith
  · have hh := unit_product_difference (Real.abs_sin_le_one _) hs (abs_sin_sq_sub_le u v) hD.2
      (by positivity : 0≤2*|u-v|)
    linarith

/-- The genuine corrected-phase derivative is globally Lipschitz in its phase with an explicit integrable fourth-order constant.
Use: combines the actual linear phase perturbation bound with the true averaged-invariant derivative to obtain the full uniform finite phase correction.
Article: jacobi, Proposition B.1.
Proof: split the literal derivative difference into its three original
oscillatory products. Their proved Lipschitz constants give two fourth-
and fifth-order terms and one fourth-order cosine term. For x>=1 compare
the fifth-order denominator with the fourth-order one and enlarge the
remaining scalar coefficients. -/
theorem phaseInvariantSlope_lipschitz (c : ℝ) (f g : ℝ → ℝ) {x : ℝ} (hx : 1≤x) :
    |phaseInvariantSlope c f x-phaseInvariantSlope c g x|≤
      (4*c^2+2*|c|)*|f x-g x|/x^4 := by
  -- The comparison is pointwise in the actual original phase values, with no assumed cancellation or asymptotic averaging.
  have hxp : 0<x := by linarith
  let D := |f x-g x|
  have hD : 0≤D := abs_nonneg _
  have hp := phase_products_lipschitz (f x) (g x)
  have hd := (double_angle_lipschitz (f x) (g x)).1
  have he : phaseInvariantSlope c f x-phaseInvariantSlope c g x=
      c^2/(2*x^4)*(cos (2*f x)*sin (f x)^2-cos (2*g x)*sin (g x)^2)+
      c^2/(2*x^5)*(sin (2*f x)*sin (f x)^2-sin (2*g x)*sin (g x)^2)+
      (3*c/(4*x^4))*(cos (2*f x)-cos (2*g x)) := by
    unfold phaseInvariantSlope
    ring
  have h1 : |c^2/(2*x^4)*(cos (2*f x)*sin (f x)^2-cos (2*g x)*sin (g x)^2)|≤c^2/(2*x^4)*(4*D) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤c^2/(2*x^4))]
    exact mul_le_mul_of_nonneg_left hp.1 (by positivity)
  have h2 : |c^2/(2*x^5)*(sin (2*f x)*sin (f x)^2-sin (2*g x)*sin (g x)^2)|≤c^2/(2*x^5)*(4*D) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤c^2/(2*x^5))]
    exact mul_le_mul_of_nonneg_left hp.2 (by positivity)
  have h3 : |(3*c/(4*x^4))*(cos (2*f x)-cos (2*g x))|≤(3*|c|/(4*x^4))*(2*D) := by
    rw [abs_mul,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_of_pos (by positivity : 0<4*x^4)]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have hxpow : x^4≤x^5 := by nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤x^4 by positivity)]
  have hden : c^2/(2*x^5)≤c^2/(2*x^4) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have hcoef : (3*|c|/(4*x^4))*(2*D)≤(2*|c|/x^4)*D := by
    have hm : 0≤ |c| *D/x^4 := by positivity
    have heq : (2*|c|/x^4)*D-(3*|c|/(4*x^4))*(2*D)=(1/2)*(|c| *D/x^4) := by ring
    linarith
  rw [he]
  calc
    _ ≤ |c^2/(2*x^4)*(cos (2*f x)*sin (f x)^2-cos (2*g x)*sin (g x)^2)|+
        |c^2/(2*x^5)*(sin (2*f x)*sin (f x)^2-sin (2*g x)*sin (g x)^2)|+
        |(3*c/(4*x^4))*(cos (2*f x)-cos (2*g x))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ c^2/(2*x^4)*(4*D)+c^2/(2*x^5)*(4*D)+(3*|c|/(4*x^4))*(2*D) := add_le_add (add_le_add h1 h2) h3
    _ ≤ c^2/(2*x^4)*(4*D)+c^2/(2*x^4)*(4*D)+(2*|c|/x^4)*D :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hden (by positivity))) hcoef
    _ = _ := by ring

end
end jacobi.Oscillation
