import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: jacobi, Theorem D.5.
These are the actual polynomial weights of the elliptic and Fredholm quadratures.
The estimates include the degenerate parameter endpoints and the derivative
certificate is an exact polynomial identity, not a numerical sign test.
The integral mean estimate in part (b) is a separate analytic obligation.
Use: bounds the normalized density and its parameter derivatives.
-/
namespace jacobi.Elliptic
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false

/-- Linear numerator common to the elliptic and Fredholm quadratures.
Use: bounds the normalized density and its parameter derivatives.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
-/
def L (t v : ℝ) : ℝ := 1-t+t*v

/-- Quadratic factor of the elliptic energy polynomial.
Use: defines the second-moment quadratures before adding the Fredholm parameter.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
-/
def q (t v : ℝ) : ℝ := v^2+(1-t^2)*v+(1-t)^2

/-- Cubic factor of the common two-parameter energy polynomial.
Use: one weight proof serves the elliptic and Fredholm calibrations.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
-/
def r (t c v : ℝ) : ℝ := q t v+c*t*v^3

/-- Full energy polynomial, retaining its simple zero at v=1.
Use: the square-root denominator in all calibration quadratures.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
-/
def P (t c v : ℝ) : ℝ := (1-v)*r t c v

/-- Numerator of the logarithmic parameter derivative of the weight.
Use: proves positivity and strict decrease of that derivative in the integration variable.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
-/
def N (t c v : ℝ) : ℝ := 2*L t v-c*v^3

/-- Logarithmic derivative of P^(-1/2) with respect to the shape parameter.
Use: controls derivatives of the elliptic ratio and the Fredholm quadratures.
Article: jacobi, Theorem D.5.
-/
def psi (t c v : ℝ) : ℝ := N t c v/(2*r t c v)

/-- The linear factor lies between v and one throughout the closed parameter box.
Use: proves the square-weight bounds and the monotonicity estimate for the elliptic ratio.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: L-v=(1-τ)(1-v) and 1-L=τ(1-v) are nonnegative. -/
theorem L_bounds {t v : ℝ} (ht : t ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    v ≤ L t v ∧ L t v ≤ 1 := by
  dsimp [L]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hv.2),
    mul_nonneg ht.1 (sub_nonneg.mpr hv.2)]

/-- All polynomial bounds of the article's common weight lemma.
Use: supplies positive denominators and parameter-independent integral majorants.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: explicit nonnegative polynomial differences prove each link of the chain. -/
theorem weights_bounds {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Icc 0 1) :
    v^2 ≤ L t v^2 ∧ L t v^2 ≤ q t v ∧ q t v ≤ r t c v ∧
      r t c v ≤ 1+v+v^2 ∧ 1+v+v^2 ≤ 3 := by
  -- Each difference is a sum of products known to be nonnegative on the closed box.
  have ht0 := ht.1
  have ht1 := ht.2
  have hc0 := hc.1
  have hc1 := hc.2
  have hv0 := hv.1
  have hv1 := hv.2
  have hL := (L_bounds ht hv).1
  have ht2 : 0 ≤ 1-t^2 := by nlinarith [sq_nonneg (1-t)]
  have hv2 : v^2 ≤ 1 := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hv3 : v^3 ≤ 1 := pow_le_one₀ hv.1 hv.2
  refine ⟨pow_le_pow_left₀ hv.1 hL 2, ?_, ?_, ?_, by linarith⟩
  · have he : q t v-L t v^2 = (1-t^2)*v^2+(1-t)^2*v := by dsimp [q, L]; ring
    nlinarith [mul_nonneg ht2 (sq_nonneg v), mul_nonneg (sq_nonneg (1-t)) hv.1]
  · dsimp [r]
    exact le_add_of_nonneg_right (by positivity)
  · have he : 1+v+v^2-r t c v =
        t*((1-t)*(1-v)+(1-c)*v^3+(1-v^3)+v) := by dsimp [r, q]; ring
    have hd : 0 ≤ (1-t)*(1-v)+(1-c)*v^3+(1-v^3)+v := by positivity
    nlinarith [mul_nonneg ht.1 hd]

/-- The full energy polynomial has the uniform two-sided bounds of the article.
Use: integrability and dominated differentiation of the calibration quadratures.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: multiply the bounds on r by the nonnegative factor 1-v. -/
theorem P_bounds {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Icc 0 1) : (1-v)*v^2 ≤ P t c v ∧ P t c v ≤ 3*(1-v) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := weights_bounds ht hc hv
  exact ⟨mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) (sub_nonneg.mpr hv.2),
    (mul_le_mul_of_nonneg_left (h4.trans h5) (sub_nonneg.mpr hv.2)).trans_eq (mul_comm _ _)⟩

/-- The denominator factor stays strictly positive away from v=0.
Use: division and differentiation of ψ on the whole interval (0,1].
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: r≥v²>0, including both closed parameter endpoints. -/
theorem r_pos {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Ioc 0 1) : 0 < r t c v := by
  obtain ⟨h1,h2,h3,_,_⟩ := weights_bounds ht hc ⟨hv.1.le,hv.2⟩
  exact (sq_pos_of_pos hv.1).trans_le (h1.trans (h2.trans h3))

/-- The energy polynomial is strictly positive in the open integration interval.
Use: licenses square roots and their derivatives under the quadrature integral.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: both factors 1-v and r are strictly positive. -/
theorem P_pos {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Ioo 0 1) : 0 < P t c v :=
  mul_pos (sub_pos.mpr hv.2) (r_pos ht hc ⟨hv.1,hv.2.le⟩)

/-- The logarithmic derivative weight is positive throughout the relevant interval.
Use: establishes the positive denominator derivatives in the monotonicity arguments.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: N_1≥2v-v³≥v>0 and the denominator is positive. -/
theorem psi_pos {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Ioc 0 1) : 0 < psi t c v := by
  -- The numerator is bounded below by the positive coordinate v.
  have hc0 := hc.1
  have hc1 := hc.2
  have hv0 := hv.1
  have hv1 := hv.2
  have hL := (L_bounds ht ⟨hv.1.le,hv.2⟩).1
  have hv2 : v^2 ≤ 1 := pow_le_one₀ hv.1.le hv.2
  have hn : 0 < N t c v := by
    dsimp [N]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (pow_nonneg hv.1.le 3),
      mul_nonneg hv.1.le (sub_nonneg.mpr hv2)]
  exact div_pos hn (mul_pos (by norm_num) (r_pos ht hc hv))

/-- Exact positive-polynomial certificate for the derivative numerator.
Use: reduces strict decrease of ψ to elementary signs instead of numerical sampling.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: expand both definitions in the polynomial ring. -/
theorem derivative_certificate (t c v : ℝ) :
    N t c v*(2*v+(1-t^2)+3*c*t*v^2)-(2*t-3*c*v^2)*r t c v =
      c*v^2*(v^2+2*(1+t^2)*v+3*(1-t^2))+
        2*(1-t)^2+4*(1-t)*v+2*t*v^2 := by
  dsimp [N, L, r, q]
  ring

/-- The derivative certificate is strictly positive for positive shape parameters.
Use: proves the strict, rather than weak, monotonicity required for unique calibration roots.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: every displayed term is nonnegative and 2τv² is strictly positive. -/
theorem derivative_certificate_pos {t c v : ℝ} (ht : t ∈ Ioc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Ioc 0 1) :
    0 < N t c v*(2*v+(1-t^2)+3*c*t*v^2)-(2*t-3*c*v^2)*r t c v := by
  -- Keep the strictly positive final term; every other certificate term has a fixed sign.
  have ht0 := ht.1
  have ht1 := ht.2
  have hc0 := hc.1
  have hc1 := hc.2
  have hv0 := hv.1
  have hv1 := hv.2
  rw [derivative_certificate]
  have ht2 : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hterm : 0 ≤ c*v^2*(v^2+2*(1+t^2)*v+3*(1-t^2)) := by positivity
  have hlast : 0 < 2*t*v^2 := by positivity
  have hmiddle : 0 ≤ 4*(1-t)*v := by positivity
  linarith [sq_nonneg (1-t)]

/-- Actual derivative of the logarithmic weight with respect to v.
Use: the analytic strict-decrease theorem for ψ, not just its polynomial sign surrogate.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: differentiate the explicit polynomial quotient and simplify the factor of two. -/
theorem psi_hasDerivAt (t c v : ℝ) (hr : r t c v ≠ 0) :
    HasDerivAt (psi t c)
      (-(N t c v*(2*v+(1-t^2)+3*c*t*v^2)-(2*t-3*c*v^2)*r t c v)/
        (2*r t c v^2)) v := by
  -- The quotient rule is applied only after proving that its actual denominator is nonzero.
  have hn : HasDerivAt (N t c) (2*t-3*c*v^2) v := by
    convert (((hasDerivAt_id v).const_mul t).const_add (1-t)).const_mul 2 |>.sub
      (((hasDerivAt_id v).pow 3).const_mul c) using 1 <;> (try funext x) <;> (dsimp [N,L]; try ring)
  have hd : HasDerivAt (r t c) (2*v+(1-t^2)+3*c*t*v^2) v := by
    convert ((((hasDerivAt_id v).pow 2).add
      ((hasDerivAt_id v).const_mul (1-t^2))).add_const ((1-t)^2)).add
      (((hasDerivAt_id v).pow 3).const_mul (c*t)) using 1 <;> (try funext x) <;> (dsimp [r,q]; try ring)
  convert hn.div (hd.const_mul 2) (mul_ne_zero (by norm_num) hr) using 1
  · rfl
  · field_simp
    ring

/-- Strict decrease of the actual weight on the full half-open integration interval.
Use: uniqueness and covariance signs in the elliptic and Fredholm calibrations.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: the quotient is continuous and its genuine derivative is negative by Π>0. -/
theorem psi_strictAntiOn {t c : ℝ} (ht : t ∈ Ioc 0 1) (hc : c ∈ Icc 0 1) :
    StrictAntiOn (psi t c) (Ioc 0 1) := by
  -- A negative derivative on the interior gives strict order also at the endpoint v=1.
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · intro v hv
    exact (psi_hasDerivAt t c v (r_pos ⟨ht.1.le,ht.2⟩ hc hv).ne').continuousAt.continuousWithinAt
  · intro v hv
    have hv' : v ∈ Ioc (0 : ℝ) 1 := interior_subset hv
    rw [(psi_hasDerivAt t c v (r_pos ⟨ht.1.le,ht.2⟩ hc hv').ne').deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (derivative_certificate_pos ht hc hv'))
      (mul_pos (by norm_num) (sq_pos_of_pos (r_pos ⟨ht.1.le,ht.2⟩ hc hv')))

/-- Exact derivative of the energy polynomial in its shape parameter.
Use: differentiates the actual square-root quadrature weight in the next theorem.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: differentiate the polynomial in τ and expand its coefficients. -/
theorem P_shape_hasDerivAt (t c v : ℝ) :
    HasDerivAt (fun u => P u c v) (-(1-v)*N t c v) t := by
  -- No positivity assumption is needed for this polynomial derivative identity.
  convert (((((hasDerivAt_id t).pow 2).const_sub 1).mul_const v).const_add (v^2) |>.add
    (((hasDerivAt_id t).const_sub 1).pow 2) |>.add
    ((hasDerivAt_id t).const_mul (c*v^3))).const_mul (1-v) using 1 <;>
    (try funext u) <;> (dsimp [P,r,q,N,L]; try ring)

/-- Exact derivative of the energy polynomial in the Fredholm parameter.
Use: supplies the other parameter derivative of the shared quadrature weight.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: only the term χτv³ depends on χ. -/
theorem P_fredholm_hasDerivAt (t c v : ℝ) :
    HasDerivAt (fun u => P t u v) (t*v^3*(1-v)) c := by
  convert (((hasDerivAt_id c).const_mul (t*v^3)).const_add (q t v)).const_mul (1-v)
    using 1
  · funext u
    dsimp [P,r]
    ring
  · ring

/-- The shape derivative of the literal inverse square-root denominator.
Use: differentiation under the integrals defining i_k, κ and the Fredholm calibration.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: the square-root and inverse chain rules apply because P>0; use P=(1-v)r. -/
theorem inverse_sqrt_shape_hasDerivAt {t c v : ℝ} (ht : t ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun u => (sqrt (P u c v))⁻¹)
      (psi t c v*(sqrt (P t c v))⁻¹) t := by
  -- Positivity discharges every square-root and division side condition explicitly.
  have hp := P_pos ht hc hv
  have hr := (r_pos ht hc ⟨hv.1,hv.2.le⟩).ne'
  have hs := (sqrt_pos.mpr hp).ne'
  convert ((P_shape_hasDerivAt t c v).sqrt hp.ne').inv hs using 1
  dsimp [psi]
  field_simp
  rw [sq_sqrt hp.le,P]
  ring

/-- The Fredholm derivative of the literal inverse square-root denominator.
Use: parameter differentiation of the common two-parameter calibration quadratures.
Article: jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proof: differentiate P, then the square root and inverse, and cancel the factor 1-v. -/
theorem inverse_sqrt_fredholm_hasDerivAt {t c v : ℝ} (ht : t ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun u => (sqrt (P t u v))⁻¹)
      (-(t/2)*(v^3/r t c v)*(sqrt (P t c v))⁻¹) c := by
  -- The same positive denominator is used in both the derivative and its normalized formula.
  have hp := P_pos ht hc hv
  have hr := (r_pos ht hc ⟨hv.1,hv.2.le⟩).ne'
  have hs := (sqrt_pos.mpr hp).ne'
  convert ((P_fredholm_hasDerivAt t c v).sqrt hp.ne').inv hs using 1
  field_simp
  rw [sq_sqrt hp.le,P]
  ring

end
end jacobi.Elliptic
