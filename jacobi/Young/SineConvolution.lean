import jacobi.Young.SinePrimitives
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The two genuine improper integrals of the intrinsic sine source are evaluated
and recombined into the actual exponential Green convolution. This proves
the pointwise integral equation behind every claimed eigenfunction.
Source: improper fundamental theorem of calculus and the exponential Green kernel.
Use: removes the boundary term in the right weighted improper integral.
-/
namespace jacobi.Young
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Dirichlet frequencies satisfy the right endpoint condition exactly.
Use: removes the boundary term in the right weighted improper integral.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: rewrite the frequency as an integer multiple of pi. -/
theorem sin_frequency (n : ℕ) : Real.sin (frequency n)=0 := by
  simpa only [frequency,Nat.cast_add,Nat.cast_one,mul_comm] using Real.sin_nat_mul_pi (n+1)

/-- The left primitive has the actual zero boundary value at minus infinity.
Use: evaluates the left half of the sine-mode Green convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: continuity of sine and cosine transports the limit t to zero. -/
theorem sineLeftPrimitive_atBot (w : ℝ) : Tendsto (sineLeftPrimitive w) atBot (𝓝 0) := by
  change Tendsto (fun x => 2*(Real.sin (w*intrinsic x)/w^2-
    intrinsic x*Real.cos (w*intrinsic x)/w)) atBot (𝓝 0)
  have ht := intrinsic_atBot
  have hs := Real.continuous_sin.continuousAt.tendsto.comp (ht.const_mul w)
  have hc := Real.continuous_cos.continuousAt.tendsto.comp (ht.const_mul w)
  simpa only [Function.comp_def,mul_zero,Real.sin_zero,zero_div,Real.cos_zero,zero_mul,sub_self] using
    ((hs.div_const (w^2)).sub ((ht.mul hc).div_const w)).const_mul 2

/-- Integer sine modes give the actual zero right boundary value at infinity.
Use: evaluates the right half of the sine-mode Green convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: t tends to one, and sine of the integer Dirichlet frequency is zero. -/
theorem sineRightPrimitive_atTop (n : ℕ) :
    Tendsto (sineRightPrimitive (frequency n)) atTop (𝓝 0) := by
  change Tendsto (fun x => 2*((intrinsic x-1)*Real.cos (frequency n*intrinsic x)/frequency n-
    Real.sin (frequency n*intrinsic x)/frequency n^2)) atTop (𝓝 0)
  have ht := intrinsic_atTop
  have hs := Real.continuous_sin.continuousAt.tendsto.comp (ht.const_mul (frequency n))
  have hc := Real.continuous_cos.continuousAt.tendsto.comp (ht.const_mul (frequency n))
  simpa only [Function.comp_def,mul_one,sub_self,zero_mul,zero_div,sin_frequency,mul_zero] using
    ((((ht.sub_const 1).mul hc).div_const (frequency n)).sub
      (hs.div_const (frequency n^2))).const_mul 2

/-- The actual weighted source integrates to its explicit left primitive.
Use: the left half of the distinguished sine eigenvalue equation.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: apply the improper fundamental theorem with the proved global
integrability, derivative and zero boundary value. -/
theorem sineSource_left_integral (n : ℕ) (x : ℝ) :
    (∫ y in Iic x, Real.exp y*sineSource (frequency n) y)=sineLeftPrimitive (frequency n) x := by
  simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun y _ => sineLeftPrimitive_derivative (frequency_pos n).ne' y)
    (sineSource_weighted_integrable (frequency n)).1.integrableOn
    (sineLeftPrimitive_atBot (frequency n))

/-- The actual complementary weighted source integrates to minus its right primitive.
Use: the right half of the distinguished sine eigenvalue equation.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: apply the improper fundamental theorem with the proved zero value at infinity. -/
theorem sineSource_right_integral (n : ℕ) (x : ℝ) :
    (∫ y in Ioi x, Real.exp (-y)*sineSource (frequency n) y)= -sineRightPrimitive (frequency n) x := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y _ => sineRightPrimitive_derivative (frequency_pos n).ne' y)
    (sineSource_weighted_integrable (frequency n)).2.integrableOn
    (sineRightPrimitive_atTop n)

/-- The actual sine source is integrable even without its exponential weights.
Use: the whole-line convolution may be split at any finite point.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the nonnegative sum of exp(x) and exp(-x) is at least one,
so the sum of the two proved weighted absolute values dominates the source. -/
theorem sineSource_integrable (w : ℝ) : Integrable (sineSource w) := by
  -- No separate decay estimate is needed after both weighted integrals are known.
  obtain ⟨hl,hr⟩ := sineSource_weighted_integrable w
  refine (hl.norm.add hr.norm).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (sineSource_continuous w).aestronglyMeasurable
  · change |sineSource w x| ≤ |Real.exp x*sineSource w x|+|Real.exp (-x)*sineSource w x|
    simp only [abs_mul,abs_of_pos (Real.exp_pos _)]
    have he : 1 ≤ Real.exp x+Real.exp (-x) := by
      rw [show Real.exp x+Real.exp (-x)=2*Real.cosh x by rw [Real.cosh_eq]; ring]
      linarith [Real.one_le_cosh x]
    nlinarith [abs_nonneg (sineSource w x)]

/-- The genuine exponential convolution has the claimed sine-mode value.
Use: proves the actual integral-kernel eigenvector equation for every mode of m_U.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: split into two integrable half-lines, use the explicit weighted
primitives, and cancel their cosine terms using the coordinate identities. -/
theorem sineSource_convolution (n : ℕ) (x : ℝ) :
    Real.sqrt (distinguished x)*(∫ y, Real.exp (-|x-y|)*sineSource (frequency n) y)=
      (2/frequency n^2)*distinguishedMode n x := by
  -- The bounded exponential kernel preserves absolute integrability of the source.
  have hi : Integrable (fun y => Real.exp (-|x-y|)*sineSource (frequency n) y) := by
    refine (sineSource_integrable (frequency n)).norm.mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((continuous_exp.comp ((continuous_const.sub continuous_id).abs.neg)).mul
        (sineSource_continuous (frequency n))).aestronglyMeasurable
    · rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))
  have hl : (∫ y in Iic x, Real.exp (-|x-y|)*sineSource (frequency n) y)=
      Real.exp (-x)*sineLeftPrimitive (frequency n) x := by
    rw [← sineSource_left_integral,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hy),← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hr : (∫ y in Ioi x, Real.exp (-|x-y|)*sineSource (frequency n) y)=
      -Real.exp x*sineRightPrimitive (frequency n) x := by
    rw [show -Real.exp x*sineRightPrimitive (frequency n) x=
      Real.exp x*(-sineRightPrimitive (frequency n) x) by ring,
      ← sineSource_right_integral,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hy.le),← mul_assoc,← Real.exp_add]
    congr 2
    ring
  -- The exponential factors are eliminated before the final scalar cancellation.
  rw [← integral_add_compl measurableSet_Iic hi,compl_Iic,hl,hr,distinguished_sqrt]
  have hs : sech x ≠ 0 := (sech_pos x).ne'
  have hp := (eq_div_iff hs).mpr (exp_sech_intrinsic x)
  have hm := (eq_div_iff hs).mpr (exp_neg_sech_intrinsic x)
  rw [hp,hm,sineLeftPrimitive,sineRightPrimitive,distinguishedMode]
  field_simp [hs,(frequency_pos n).ne']
  ring

end
end jacobi.Young
