import jacobi.RootMass.Quadratures
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
Article: jacobi, Appendix D.5 (regularized state quadratures).
The actual inverse-coordinate curve is a continuous strictly decreasing
bijection of the printed integration interval. Its derivative and the
exact radicand square are proved from the genuine inverse equation, giving
a real nonsingular Jacobian rather than assuming a quadrature substitution.
Source: the actual inverse function and the one-variable chain rule.
Use: both the actual optimizing spatial Jacobian and the inverse-coordinate quadratures use this same polynomial.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal first-integral radicand of the compact root-mass profile.
Use: both the actual optimizing spatial Jacobian and the inverse-coordinate quadratures use this same polynomial.
Article: jacobi, Appendix D.5 (regularized state quadratures).
-/
def radicand (a y n : ℝ) : ℝ := (p a n)^2-n^3*(n^2-1)/y

/-- The actual inverse-coordinate curve starts at the true upper turning level.
Use: fixes the upper integration endpoint n_0(y).
Article: jacobi, Theorem D.8.
Proof: substitute u=0 in the literal inverse-coordinate definition. -/
theorem node_zero (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : node a ha y 0=inverse a ha y := by simp [node]

/-- The actual inverse-coordinate curve ends at the true cutoff level one.
Use: identifies the compact profile's boundary in every state quadrature.
Article: jacobi, Theorem D.8.
Proof: substitute u=1 and use the proved inverse endpoint equation. -/
theorem node_one (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : node a ha y 1=1 := by simp [node,inverse_zero]

/-- The actual upper turning level lies strictly above one for every positive parameter.
Use: all optimizing half-cores and singular state integration intervals are nonempty.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: compare the actual inverse at y with its endpoint value at zero. -/
theorem inverse_gt_one {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) : 1< inverse a ha y := by
  have hh := inverse_strictMono ha (show (0:ℝ)∈Ici 0 by simp) hy.le hy
  rwa [inverse_zero] at hh

/-- The true fixed-interval inverse-coordinate state is strictly decreasing on the full closed unit interval.
Use: provides genuine injectivity and the exact image in the Lebesgue substitution theorem.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: 1-u² strictly decreases at nonnegative u; multiplication by y>0
preserves that strict order, and the actual inverse is strictly increasing. -/
theorem node_strictAnti {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    StrictAntiOn (node a ha y) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hru : 0≤1-u^2 := by nlinarith [hu.1,hu.2]
  have hrv : 0≤1-v^2 := by nlinarith [hv.1,hv.2]
  exact inverse_strictMono ha (mul_nonneg hy.le hrv) (mul_nonneg hy.le hru)
    (mul_lt_mul_of_pos_left (by nlinarith [hu.1,hv.1]) hy)

/-- The actual inverse-coordinate curve maps precisely onto the full open turning interval.
Use: discharges surjectivity of the true change of variables for every continuous state observable.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: apply the continuous strictly decreasing interval-image theorem and substitute the proved actual endpoint values. -/
theorem node_image {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    node a ha y '' Ioo (0:ℝ) 1=Ioo (1:ℝ) (inverse a ha y) := by
  have hc : Continuous (node a ha y) := (node_continuous a ha).comp (continuous_const.prodMk continuous_id)
  have hh := hc.continuousOn.image_Ioo_of_strictAntiOn (by norm_num : (0:ℝ)≤1) (node_strictAnti ha hy)
  rwa [node_one,node_zero] at hh

/-- The actual fixed-interval state has its exact nonsingular classical derivative on the open unit interval.
Use: supplies the genuine inverse-coordinate Jacobian, including its negative orientation.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: the inverse argument is positive in the open interval. Compose its
proved actual inverse derivative with the polynomial y*(1-u²). -/
theorem node_hasDerivAt {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Ioo (0:ℝ) 1) :
    HasDerivAt (node a ha y) (-2*y*u/psiSlope a (node a ha y u)) u := by
  have hr : 0<1-u^2 := by nlinarith [hu.1,hu.2,sq_nonneg (1-u)]
  convert (inverse_hasDerivAt ha (mul_pos hy hr)).comp u
    ((((hasDerivAt_id u).pow 2).const_sub 1).const_mul y) using 1
  · rfl
  · dsimp only [id_eq,Pi.pow_apply,node]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring

/-- The literal radicand along the actual inverse-coordinate state is an exact positive polynomial square.
Use: removes the apparent upper-endpoint singularity in the true substitution Jacobian.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: the actual inverse equation is psi(n_u)=y*(1-u²); clear its proved positive denominator and the positive y. -/
theorem radicand_node {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Icc (0:ℝ) 1) :
    radicand a y (node a ha y u)=(p a (node a ha y u))^2*u^2 := by
  -- Clear only the proved nonzero actual inverse-branch denominators.
  have hr : 0≤1-u^2 := by nlinarith [hu.1,hu.2]
  have hn := inverse_ge_one a ha (y*(1-u^2))
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  have hp' : p a (node a ha y u)≠0 := hp.ne'
  have he : psi a (node a ha y u)=y*(1-u^2) := psi_inverse ha (mul_nonneg hy.le hr)
  unfold psi at he
  unfold radicand
  field_simp [hp',hy.ne'] at he ⊢
  nlinarith

end
end jacobi.RootMass
