import jacobi.Applications.EndpointLimit

/-!
Exact constants for descent from the standard Jacobi realization.
The identities choose the flow time and quantify the gain obtained from
the second derivative estimate. Their signs include the logarithmic
parameter zero without a separate limiting definition.
Use: StandardDescent combines these identities with the actual flow's
Taylor estimate and the standard realization's energy and derivative limits.
Article: jacobi, Theorem 5.6.
Article role: the explicit descent time, positive improvement gap and controlled Taylor
cancellation.
-/
namespace jacobi.Applications
noncomputable section

/-- Energy of the one-sided limit kernel. Used as the initial limiting
energy in the strict-improvement estimate.
Article: jacobi, Theorem 5.6.
-/
def standardEnergy (a : ℝ) : ℝ := 8/(3*(2*a+3)*(4*a+3))

/-- Scaled resolvent trace, constant along the isospectral flow.
Article: jacobi, Theorem 5.6.
-/
def standardMass (a : ℝ) : ℝ := 1/(2*(a+1))

/-- Limiting initial energy derivative along the resolvent flow. Its sign
determines the direction of descent away from the symmetric parameter.
Article: jacobi, Theorem 5.6.
-/
def standardSlope (a : ℝ) : ℝ :=
  32*(2*a-1)/(5*(a+1)*(2*a+3)*(4*a+3)*(2*a+5)*(4*a+5)*(6*a+5))

/-- The explicit time at which the Taylor bound guarantees improvement.
Article: jacobi, Theorem 5.6.
-/
def descentTime (a : ℝ) : ℝ :=
  (a+1)*(1-2*a)/(5*(2*a+5)*(4*a+5)*(6*a+5))

/-- The positive reduction in limiting energy, vanishing exactly at one half.
Article: jacobi, Theorem 5.6.
-/
def descentGap (a : ℝ) : ℝ :=
  16*(2*a-1)^2/(25*(2*a+3)*(4*a+3)*(2*a+5)^2*(4*a+5)^2*(6*a+5)^2)

/-- The one-sided energy is positive on the entire Nesterov parameter range.
This justifies division by the original endpoint gain in the final comparison.
Article: jacobi, Theorem 5.6.
-/
theorem standardEnergy_pos {a : ℝ} (ha : -(1/2:ℝ)<a) : 0<standardEnergy a := by
  unfold standardEnergy
  exact div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith))

/-- The conserved scaled trace is positive, so the optimizing time has a
nonzero quadratic Taylor coefficient.
Article: jacobi, Theorem 5.6.
-/
theorem standardMass_pos {a : ℝ} (ha : -(1/2:ℝ)<a) : 0<standardMass a := by
  unfold standardMass
  exact div_pos zero_lt_one (by linarith)

/-- The improvement is strictly positive at every nonsymmetric parameter.
Article: jacobi, Theorem 5.6.
-/
theorem descentGap_pos {a : ℝ} (ha : -(1/2:ℝ)<a) (hne : a≠1/2) :
    0<descentGap a := by
  have hn : 2*a-1≠0 := by intro h; apply hne; linarith
  have h2 : 0<2*a+3 := by linarith
  have h3 : 0<4*a+3 := by linarith
  have h4 : 0<2*a+5 := by linarith
  have h5 : 0<4*a+5 := by linarith
  have h6 : 0<6*a+5 := by linarith
  unfold descentGap
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hn))
    (by positivity)

/-- The initial slope vanishes exactly at the symmetric parameter. Used
to turn its limiting value into eventual finite-dimensional noncriticality.
Article: jacobi, Theorem 5.6.
-/
theorem standardSlope_eq_zero_iff {a : ℝ} (ha : -(1/2:ℝ)<a) :
    standardSlope a=0 ↔ a=1/2 := by
  have h1 : a+1≠0 := by linarith
  have h2 : 2*a+3≠0 := by linarith
  have h3 : 4*a+3≠0 := by linarith
  have h4 : 2*a+5≠0 := by linarith
  have h5 : 4*a+5≠0 := by linarith
  have h6 : 6*a+5≠0 := by linarith
  simp only [standardSlope,div_eq_zero_iff,mul_eq_zero,show (32:ℝ)≠0 by norm_num,
    h1,h2,h3,h4,h5,h6,show (5:ℝ)≠0 by norm_num,or_false,false_or]
  constructor <;> intro h <;> linarith

/-- The chosen time is the explicit quadratic descent step. No numerical
approximation enters the cancellation used by the strict-improvement bound.
Article: jacobi, Theorem 5.6.
-/
theorem descentTime_identity {a : ℝ} (ha : -(1/2:ℝ)<a) :
    descentTime a = -standardSlope a/(48*(standardMass a)^2*standardEnergy a) := by
  have h1 : a+1≠0 := by linarith
  have h2 : 2*a+3≠0 := by linarith
  have h3 : 4*a+3≠0 := by linarith
  have h4 : 2*a+5≠0 := by linarith
  have h5 : 4*a+5≠0 := by linarith
  have h6 : 6*a+5≠0 := by linarith
  unfold descentTime standardSlope standardMass standardEnergy
  field_simp (disch := first | positivity | linarith)
  ring

/-- Substituting the chosen time into the relaxed Taylor quadratic gives
exactly the stated gap. Used after bounding the exponential remainder by two.
Article: jacobi, Theorem 5.6.
-/
theorem descentGap_identity {a : ℝ} (ha : -(1/2:ℝ)<a) :
    descentTime a*standardSlope a+
      24*(standardMass a)^2*standardEnergy a*(descentTime a)^2 = -descentGap a := by
  have h1 : a+1≠0 := by linarith
  have h2 : 2*a+3≠0 := by linarith
  have h3 : 4*a+3≠0 := by linarith
  have h4 : 2*a+5≠0 := by linarith
  have h5 : 4*a+5≠0 := by linarith
  have h6 : 6*a+5≠0 := by linarith
  unfold descentTime standardSlope standardMass standardEnergy descentGap
  field_simp (disch := first | positivity | linarith)
  ring

/-- The energy normalization agrees with the already verified original
Nesterov endpoint constant at the actual momentum parameter.
Article: jacobi, Theorem 5.6.
-/
theorem standardEnergy_endpoint_limit {b : ℝ} (hb : -1<b) :
    Filter.Tendsto (fun k : ℕ => ((nesterovMethod b).kernelNorm k 0 0)^2/(k:ℝ)^3)
      Filter.atTop (nhds (standardEnergy (b/2)/4)) := by
  convert endpoint_gain_limit hb using 1
  simp only [standardEnergy]
  ring

/-- The gap in energy becomes the printed deficit from two in the
squared-gain ratio, with the original Nesterov parameter rather than its half.
Article: jacobi, Theorem 5.6.
-/
theorem descentGap_ratio {b : ℝ} (hb : -1<b) :
    2*descentGap (b/2)/standardEnergy (b/2)=
      12*(b-1)^2/(25*(b+5)^2*(2*b+5)^2*(3*b+5)^2) := by
  have h1 : b+3≠0 := by linarith
  have h2 : 2*b+3≠0 := by linarith
  have h3 : b+5≠0 := by linarith
  have h4 : 2*b+5≠0 := by linarith
  have h5 : 3*b+5≠0 := by linarith
  unfold descentGap standardEnergy
  have h1' : 2*(b/2)+3≠0 := by linarith
  have h2' : 4*(b/2)+3≠0 := by linarith
  have h3' : 2*(b/2)+5≠0 := by linarith
  have h4' : 4*(b/2)+5≠0 := by linarith
  have h5' : 6*(b/2)+5≠0 := by linarith
  field_simp (disch := first | positivity | linarith)
  ring

/-- The explicit descent time keeps the exponential Taylor factor in a
uniformly small interval throughout the admissible parameter range.
Article: jacobi, Theorem 5.6.
-/
theorem descentTime_scaled_bound {a : ℝ} (ha : -(1/2:ℝ)<a) :
    4*standardMass a*|descentTime a|≤1/15 := by
  have h1 : 0<a+1 := by linarith
  have h2 : 0<2*a+5 := by linarith
  have h3 : 0<4*a+5 := by linarith
  have h4 : 0<6*a+5 := by linarith
  have hden : 0<5*(2*a+5)*(4*a+5)*(6*a+5) := by positivity
  have he : 4*standardMass a*|descentTime a|=
      2*|1-2*a|/(5*(2*a+5)*(4*a+5)*(6*a+5)) := by
    unfold standardMass descentTime
    rw [abs_div,abs_mul,abs_of_pos h1,abs_of_pos hden]
    field_simp (disch := first | positivity | linarith)
    ring
  rw [he]
  apply (div_le_iff₀ hden).mpr
  have hab : |1-2*a|≤2*a+5 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hp : 6≤(4*a+5)*(6*a+5) := by
    nlinarith [mul_nonneg (show 0≤4*a+2 by linarith) (show 0≤6*a+3 by linarith)]
  nlinarith [mul_nonneg h2.le (sub_nonneg.mpr hp)]

/-- The full exponential remainder factor is strictly below two. The
proof uses the elementary exponential bound on [0,1), not decimal evaluation.
Article: jacobi, Theorem 5.6.
-/
theorem descentTime_exp_lt_two {a : ℝ} (ha : -(1/2:ℝ)<a) :
    Real.exp (4*standardMass a*|descentTime a|)<2 := by
  calc
    _≤Real.exp (1/15:ℝ) := Real.exp_le_exp.mpr (descentTime_scaled_bound ha)
    _≤1/(1-(1/15:ℝ)) :=
      Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _<2 := by norm_num

/-- The actual Taylor expression at the explicit time is bounded by the
initial energy minus the stated positive gap. This scalar calculation is
the final step after the flow and standard-kernel limits are established.
Article: jacobi, Theorem 5.6.
-/
theorem descentTime_taylor_bound {a : ℝ} (ha : -(1/2:ℝ)<a) :
    standardEnergy a+descentTime a*standardSlope a+
      12*(standardMass a)^2*Real.exp (4*standardMass a*|descentTime a|)*
        (descentTime a)^2*standardEnergy a ≤ standardEnergy a-descentGap a := by
  have hc := standardEnergy_pos ha
  have he := (descentTime_exp_lt_two ha).le
  have hm := mul_le_mul_of_nonneg_right he
    (show 0≤12*(standardMass a)^2*(descentTime a)^2*standardEnergy a by positivity)
  have hid := descentGap_identity ha
  nlinarith

/-- Away from one half the certified Taylor value is strictly smaller
than the one-sided energy.
Article: jacobi, Theorem 5.6.
-/
theorem descentEnergy_lt {a : ℝ} (ha : -(1/2:ℝ)<a) (hne : a≠1/2) :
    standardEnergy a-descentGap a<standardEnergy a := by
  linarith [descentGap_pos ha hne]

end
end jacobi.Applications
