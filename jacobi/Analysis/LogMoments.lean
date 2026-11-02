import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
Exact logarithmic monomial integrals from a continuous primitive.
Writing x*log(x) as one factor makes every finite moment continuous at
zero. Integration of the derivative of x^(m+1)*(x*log(x))^(k+1) gives
the exact recurrence, and induction evaluates all moments by factorials.
Use: the logarithmic standard kernel and initial descent integral use
these analytic identities without quadrature or limiting certificates.
Article: jacobi, Theorem 5.4 and Theorem 5.6.
Article role: the exact logarithmic energy and initial-slope integrals at alpha zero.
Source: the fundamental theorem of calculus and integration by parts for power-log moments.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- A logarithmic moment with its continuous zero-endpoint extension.
It is x^(m+k)*log(x)^k on the positive integration interval.
Article: jacobi, Theorem 5.4 and Theorem 5.6.
Source: the fundamental theorem of calculus and integration by parts for power-log moments.
-/
def logMoment (m k : ℕ) : ℝ := ∫ x in (0:ℝ)..1,x^m*(x*log x)^k

/-- The true continuous moments satisfy the exact integration recurrence.
The endpoint values of the explicit primitive are both zero.
Article: jacobi, Theorem 5.4 and Theorem 5.6.
Source: the fundamental theorem of calculus and integration by parts for power-log moments.
-/
theorem logMoment_recurrence (m k : ℕ) :
    logMoment m (k+1)= -((k:ℝ)+1)/((m:ℝ)+k+2)*logMoment (m+1) k := by
  let F : ℝ → ℝ := fun x => x^(m+1)*(x*log x)^(k+1)
  have hc : Continuous F := (continuous_id.pow (m+1)).mul (continuous_mul_log.pow (k+1))
  have hd (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : HasDerivAt F
      (((m:ℝ)+k+2)*(x^m*(x*log x)^(k+1))+((k:ℝ)+1)*(x^(m+1)*(x*log x)^k)) x := by
    have h := ((hasDerivAt_id x).pow (m+1)).mul ((hasDerivAt_mul_log hx.1.ne').pow (k+1))
    convert h using 1
    · rfl
    · simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Pi.pow_apply,id_eq,pow_succ]
      ring
  have hI1 : IntervalIntegrable (fun x : ℝ => x^m*(x*log x)^(k+1)) volume 0 1 :=
    ((continuous_id.pow m).mul (continuous_mul_log.pow (k+1))).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x : ℝ => x^(m+1)*(x*log x)^k) volume 0 1 :=
    ((continuous_id.pow (m+1)).mul (continuous_mul_log.pow k)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ)≤1) hc.continuousOn hd
    ((hI1.const_mul ((m:ℝ)+k+2)).add (hI2.const_mul ((k:ℝ)+1)))
  rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  have hz : F 1-F 0=0 := by simp [F]
  rw [hz] at h
  change ((m:ℝ)+k+2)*logMoment m (k+1)+((k:ℝ)+1)*logMoment (m+1) k=0 at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (show (m:ℝ)+k+2≠0 by positivity)).mpr
  linear_combination h

/-- All genuine logarithmic moments have their exact factorial value.
The induction uses only the proved continuous-primitive recurrence and
the elementary polynomial integral at logarithmic degree zero.
Article: jacobi, Theorem 5.4 and Theorem 5.6.
Source: the fundamental theorem of calculus and integration by parts for power-log moments.
-/
theorem logMoment_formula (m k : ℕ) :
    logMoment m k=(-1:ℝ)^k*(k.factorial:ℝ)/((m:ℝ)+k+1)^(k+1) := by
  induction k generalizing m with
  | zero => simp [logMoment,integral_pow]
  | succ k ih =>
    rw [logMoment_recurrence,ih]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hden : (m:ℝ)+k+2≠0 := by positivity
    have he : (m:ℝ)+1+k+1=(m:ℝ)+k+2 := by ring
    rw [he]
    field_simp [hden]
    ring

end
end jacobi.Analysis
