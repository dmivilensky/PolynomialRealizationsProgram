import jacobi.RootMass.Inverse
import jacobi.RootMass.Monotonicity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Article: jacobi, Theorem D.8.
Every argument is the actual inverse of psi, constructed from its proved
bijection. All four printed state integrals are genuine convergent integrals
of continuous functions on [0,1]. Their parameter continuity includes y=0.
Source: nonnegative rational weights, compact integration and the actual inverse coordinate.
Use: all four root-mass quadratures refer to exactly this same genuine inverse.
-/
namespace jacobi.RootMass
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse-coordinate state at the fixed integration parameter.
Use: all four root-mass quadratures refer to exactly this same genuine inverse.
Article: jacobi, Theorem D.8.
-/
def node (a : ℝ) (ha : -2*sqrt 3<a) (y u : ℝ) : ℝ := inverse a ha (y*(1-u^2))

/-- The root-mass fixed-interval power weight before the factor 2*y.
Use: k=1,2,3 give root mass, ordinary mass and energy, respectively.
Article: jacobi, Theorem D.8.
-/
def W (k : ℕ) (a n : ℝ) : ℝ := n^k*(p a n)^2/(n^3*q a n)

/-- The positive moment weight in the original nonsingular constraint quadrature.
Use: Ghat(y)=4*y²*integral K(n_u).
Article: jacobi, Theorem D.8.
-/
def K (a n : ℝ) : ℝ := (p a n)^3/(n^2*q a n)

/-- The actual root-mass power quadrature.
Use: gives all three state normalizations from the same optimizing parameter.
Article: jacobi, Theorem D.8.
-/
def hat (k : ℕ) (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : ℝ :=
  2*y*∫ u in (0:ℝ)..1,W k a (node a ha y u)

/-- The literal spectral constraint quadrature of the root-mass theorem.
Use: its proved bijection selects the unique y for every positive threshold T/b⁴.
Article: jacobi, Theorem D.8.
-/
def Ghat (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : ℝ :=
  4*y^2*∫ u in (0:ℝ)..1,K a (node a ha y u)

/-- The inverse-coordinate state depends continuously on both actual integration and moment parameters.
Use: compact integration gives true convergence and continuity of every quadrature.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the inverse already proved continuous is composed with the literal polynomial target. -/
theorem node_continuous (a : ℝ) (ha : -2*sqrt 3<a) : Continuous (fun z : ℝ × ℝ => node a ha z.1 z.2) :=
  (inverse_continuous a ha).comp (by fun_prop)

/-- Every power-weight integrand is jointly continuous, including both integration endpoints.
Use: its actual interval integral is finite and depends continuously on y.
Article: jacobi, Theorem D.8.
Proof: the inverse state is always at least one, so the actual rational denominator never vanishes. -/
theorem W_node_continuous (k : ℕ) (a : ℝ) (ha : -2*sqrt 3<a) :
    Continuous (fun z : ℝ × ℝ => W k a (node a ha z.1 z.2)) := by
  have hn := node_continuous a ha
  have hp : Continuous (fun z : ℝ × ℝ => p a (node a ha z.1 z.2)) := by unfold p; fun_prop
  have hq : Continuous (fun z : ℝ × ℝ => q a (node a ha z.1 z.2)) := by unfold q; fun_prop
  exact ((hn.pow k).mul (hp.pow 2)).div ((hn.pow 3).mul hq) (fun z =>
    mul_ne_zero (pow_ne_zero 3 (zero_lt_one.trans_le (inverse_ge_one a ha _)).ne')
      (q_pos ha (inverse_ge_one a ha _)).ne')

/-- The literal constraint weight is jointly continuous also at its apparent singular endpoint.
Use: the original Ghat integral provides a nonsingular representation for all limit and derivative arguments.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: n_u>=1 and q(n_u)>0 make the actual denominator uniformly nonzero at every point. -/
theorem K_node_continuous (a : ℝ) (ha : -2*sqrt 3<a) :
    Continuous (fun z : ℝ × ℝ => K a (node a ha z.1 z.2)) := by
  have hn := node_continuous a ha
  have hp : Continuous (fun z : ℝ × ℝ => p a (node a ha z.1 z.2)) := by unfold p; fun_prop
  have hq : Continuous (fun z : ℝ × ℝ => q a (node a ha z.1 z.2)) := by unfold q; fun_prop
  exact (hp.pow 3).div ((hn.pow 2).mul hq) (fun _ =>
    mul_ne_zero (sq_pos_of_pos (zero_lt_one.trans_le (inverse_ge_one a ha _))).ne'
      (q_pos ha (inverse_ge_one a ha _)).ne')

/-- Every printed state quadrature is a genuinely convergent finite interval integral.
Use: subsequent evaluations and weak duality never manipulate undefined real integrals.
Article: jacobi, Theorem D.8.
Proof: the proved joint continuity restricts to continuity on the fixed compact integration interval. -/
theorem hat_integrable (k : ℕ) (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) :
    IntervalIntegrable (fun u => W k a (node a ha y u)) volume 0 1 :=
  ((W_node_continuous k a ha).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- The actual nonsingular moment quadrature is a genuine finite interval integral.
Use: validates all comparisons and endpoint limits in the defining parameter equation.
Article: jacobi, Theorem D.8.
Proof: the actual positive-denominator integrand is continuous on the compact interval. -/
theorem Ghat_integrable (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) :
    IntervalIntegrable (fun u => K a (node a ha y u)) volume 0 1 :=
  ((K_node_continuous a ha).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- All three actual state quadratures depend continuously on their full real parameter extension.
Use: includes every positive parameter and the y=0 limiting endpoint.
Article: jacobi, Theorem D.8.
Proof: integrate the jointly continuous actual power weight on the fixed compact interval and multiply by 2*y. -/
theorem hat_continuous (k : ℕ) (a : ℝ) (ha : -2*sqrt 3<a) : Continuous (hat k a ha) :=
  (continuous_const.mul continuous_id).mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (W_node_continuous k a ha) 0 1)

/-- The actual spectral constraint quadrature is continuous, including its zero endpoint.
Use: the unique parameter is obtained by genuine intermediate values over the full range.
Article: jacobi, Theorem D.8.
Proof: integrate the nonsingular jointly continuous rational representation and multiply by 4*y². -/
theorem Ghat_continuous (a : ℝ) (ha : -2*sqrt 3<a) : Continuous (Ghat a ha) :=
  (continuous_const.mul (continuous_id.pow 2)).mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (K_node_continuous a ha) 0 1)

/-- The moment quadrature vanishes exactly at its zero-parameter endpoint value.
Use: gives the actual y=0 limit in the constraint's range proof.
Article: jacobi, Theorem D.8.
Proof: the nonsingular defining formula has the factor 4*y². -/
theorem Ghat_zero (a : ℝ) (ha : -2*sqrt 3<a) : Ghat a ha 0=0 := by simp [Ghat]

/-- The rational Q representation of the actual constraint integrand holds at every interior integration point.
Use: strict monotonicity follows by comparing the same certified Q at strictly increasing inverse states.
Article: jacobi, Theorem D.8.
Proof: the actual inverse equation identifies psi(n_u)=y*(1-u²),
and the literal rational identity Q=psi²*k cancels the nonzero interior factor. -/
theorem constraint_integrand_identity {a y u : ℝ} (ha : -2*sqrt 3<a)
    (hy : 0≤y) (hu : u∈Ioo (0:ℝ) 1) :
    y^2*K a (node a ha y u)=Q a (node a ha y u)/(1-u^2)^2 := by
  -- This identity is proved on the actual inverse branch, with every denominator nonzero.
  have hu2 : 0<1-u^2 := by nlinarith [hu.1,hu.2,sq_nonneg (1-u)]
  have hn := inverse_ge_one a ha (y*(1-u^2))
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  have hq := q_pos ha hn
  have he : psi a (node a ha y u)=y*(1-u^2) := psi_inverse ha (mul_nonneg hy hu2.le)
  have hid : Q a (node a ha y u)=(psi a (node a ha y u))^2*K a (node a ha y u) := by
    unfold Q psi K
    field_simp
  rw [hid,he]
  field_simp

end
end jacobi.RootMass
