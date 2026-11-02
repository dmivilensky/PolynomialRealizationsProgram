import jacobi.Young.Hyperbolic
import chebyshev2.Sobolev.Hilbert
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The primitive of r sqrt(1-r/a) is constructed by an ordinary interval integral.
Its exact height 4a²/15 and Lipschitz bound on [0,a] justify composition with
the actual absolutely continuous H1 representative, including at a maximum.
Source: the fundamental theorem of calculus and the elementary Bogomolny argument
given in the article; no smoothness at a square-root zero is assumed.
Use: gives a differentiable primitive with continuous derivative even at the maximum.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized primitive for the square-completion argument.
Use: gives a differentiable primitive with continuous derivative even at the maximum.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def normalizedPrimitive (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, t*sqrt (1-t)

/-- The primitive at the zero endpoint vanishes exactly.
Use: evaluates the two infinite endpoints of the Sobolev representative.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: an interval integral with identical endpoints is zero. -/
theorem normalizedPrimitive_zero : normalizedPrimitive 0=0 := by simp [normalizedPrimitive]

/-- The normalized primitive has its actual continuous square-root derivative everywhere.
Use: the chain rule for the Sobolev representative needs no derivative of sqrt at zero.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the integrand is continuous on the full real line, so apply the ordinary FTC. -/
theorem normalizedPrimitive_hasDerivAt (z : ℝ) :
    HasDerivAt normalizedPrimitive (z*sqrt (1-z)) z := by
  have hc : Continuous (fun t : ℝ => t*sqrt (1-t)) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 z)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter (hc.continuousAt)

/-- The exact normalized primitive height, with no numerical quadrature.
Use: supplies the sharp factor 32/15 after taking both halves and completing the square.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: differentiate -(2/15)(1-z)^(3/2)(2+3z) on [0,1], including z=1,
and evaluate its endpoints by the interval fundamental theorem. -/
theorem normalizedPrimitive_one : normalizedPrimitive 1=4/15 := by
  -- The 3/2 power is differentiable at zero, so the endpoint is included legitimately.
  let H (z : ℝ) := -(2/15 : ℝ)*(1-z)^(3/2 : ℝ)*(2+3*z)
  have hd (z : ℝ) (hz : z ∈ uIcc (0 : ℝ) 1) : HasDerivAt H (z*sqrt (1-z)) z := by
    have hz' : z ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hz
    have hp : (1-z)^(3/2 : ℝ)=(1-z)*sqrt (1-z) := by
      rw [sqrt_eq_rpow,show (3/2 : ℝ)=1/2+1 by norm_num,
        Real.rpow_add' (sub_nonneg.mpr hz'.2) (by norm_num : (1/2 : ℝ)+1 ≠ 0),Real.rpow_one]
      ring
    convert ((((hasDerivAt_id z).const_sub 1).rpow_const (Or.inr (by norm_num : (1 : ℝ) ≤ 3/2))).const_mul
      (-(2/15 : ℝ))).mul (((hasDerivAt_id z).const_mul 3).const_add 2) using 1
    · funext t
      dsimp [H]
    · norm_num only [id_eq,show (3/2 : ℝ)-1=1/2 by norm_num]
      rw [← sqrt_eq_rpow,hp]
      ring
  have hi : IntervalIntegrable (fun t : ℝ => t*sqrt (1-t)) volume 0 1 :=
    (show Continuous (fun t : ℝ => t*sqrt (1-t)) by fun_prop).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  norm_num [H,normalizedPrimitive] at h ⊢
  exact h

/-- The spatially rescaled primitive for any positive maximum height.
Use: the two-sided variation estimate for a Sobolev function with maximum a.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def wellPrimitive (a z : ℝ) : ℝ := a^2*normalizedPrimitive (z/a)

/-- The rescaled primitive vanishes at zero.
Use: both spatial endpoints vanish in the Bogomolny variation estimate.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: substitute the zero endpoint into the normalized primitive. -/
theorem wellPrimitive_zero (a : ℝ) : wellPrimitive a 0=0 := by
  simp only [wellPrimitive,zero_div,normalizedPrimitive_zero,mul_zero]

/-- Exact height of the rescaled primitive.
Use: the sharp total-variation bound is twice this value.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: a/a=1 and the normalized height is 4/15. -/
theorem wellPrimitive_self {a : ℝ} (ha : 0 < a) : wellPrimitive a a=(4/15 : ℝ)*a^2 := by
  rw [wellPrimitive,div_self ha.ne',normalizedPrimitive_one,mul_comm]

/-- Actual derivative of the rescaled primitive at every real argument.
Use: chain rule with an a.e. Sobolev derivative, including at the peak.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the FTC derivative is composed with division by a; its scalar factors cancel. -/
theorem wellPrimitive_hasDerivAt {a : ℝ} (ha : 0 < a) (z : ℝ) :
    HasDerivAt (wellPrimitive a) (z*sqrt (1-z/a)) z := by
  convert ((normalizedPrimitive_hasDerivAt (z/a)).comp z
    ((hasDerivAt_id z).div_const a)).const_mul (a^2) using 1
  · rfl
  · field_simp

/-- The rescaled primitive is a-Lipschitz on the actual range [0,a].
Use: composition with a locally absolutely continuous Sobolev representative is legitimate.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: its continuous derivative z sqrt(1-z/a) is between zero and a on [0,a]. -/
theorem wellPrimitive_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨a,ha.le⟩ (wellPrimitive a) (Icc 0 a) := by
  -- The range restriction bounds the derivative despite its square-root endpoint.
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 a)
    (fun z _ => (wellPrimitive_hasDerivAt ha z).hasDerivWithinAt)
  intro z hz
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ a := hz.2
  have hr : sqrt (1-z/a) ≤ 1 := sqrt_le_one.mpr (by linarith [div_nonneg hz0 ha.le])
  have hb : ‖z*sqrt (1-z/a)‖ ≤ a := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right hz0 hr).trans hz1
  exact_mod_cast hb

end
end jacobi.Young
