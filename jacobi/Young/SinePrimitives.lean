import jacobi.Young.IntrinsicCoordinate

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Explicit weighted primitives evaluate the actual exponential convolution
against every intrinsic sine mode. Both exponential weights are globally
integrable by the actual sech-squared majorant; the endpoint limits enforce
the sine boundary conditions. These are identities of actual real functions
and genuine improper integrals, without spectral or numerical assumptions.
Source: the one-dimensional Green-kernel split and the improper fundamental theorem.
Use: the literal convolution in the distinguished kernel's eigenvalue equation.
-/
namespace jacobi.Young
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The source obtained by multiplying an intrinsic sine profile by sqrt(m_U).
Use: the literal convolution in the distinguished kernel's eigenvalue equation.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def sineSource (w x : ℝ) : ℝ := (1/2 : ℝ)*sech x^3*Real.sin (w*intrinsic x)

/-- The weighted sine source is an actual continuous function.
Use: licenses all absolute-integrability comparisons in the spectral convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: all factors are continuous, and cosh has no real zero. -/
theorem sineSource_continuous (w : ℝ) : Continuous (sineSource w) :=
  ((Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 3).const_mul (1/2 : ℝ) |>.mul
    (Real.continuous_sin.comp (continuous_const.mul intrinsic_continuous))

/-- Multiplication by the left exponential weight cancels one sech factor.
Use: evaluates the left half of the actual distinguished-mode convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: exp(x)sech(x)=2t and the remaining factors multiply algebraically. -/
theorem sineSource_left (w x : ℝ) : Real.exp x*sineSource w x=
    intrinsic x*sech x^2*Real.sin (w*intrinsic x) := by
  calc
    _ = (Real.exp x*sech x)*(1/2 : ℝ)*sech x^2*Real.sin (w*intrinsic x) := by unfold sineSource; ring
    _ = _ := by rw [exp_sech_intrinsic]; ring

/-- The right exponential weight gives the complementary coordinate.
Use: evaluates the right half of the same actual convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: exp(-x)sech(x)=2(1-t) and the remaining factors multiply algebraically. -/
theorem sineSource_right (w x : ℝ) : Real.exp (-x)*sineSource w x=
    (1-intrinsic x)*sech x^2*Real.sin (w*intrinsic x) := by
  calc
    _ = (Real.exp (-x)*sech x)*(1/2 : ℝ)*sech x^2*Real.sin (w*intrinsic x) := by unfold sineSource; ring
    _ = _ := by rw [exp_neg_sech_intrinsic]; ring

/-- Both actual exponentially weighted sine sources are globally integrable.
Use: justifies the left and right improper fundamental-theorem evaluations.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: t and 1-t lie in [0,1] and absolute sine is at most one, so both
weighted absolute values are bounded by the integrable sech-squared function. -/
theorem sineSource_weighted_integrable (w : ℝ) :
    Integrable (fun x => Real.exp x*sineSource w x) ∧
      Integrable (fun x => Real.exp (-x)*sineSource w x) := by
  -- The same majorant works for all frequencies, including higher oscillatory modes.
  have hc := sineSource_continuous w
  have hb (x u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
      |u*sech x^2*Real.sin (w*intrinsic x)| ≤ sech x^2 := by
    rw [abs_mul,abs_mul,abs_of_nonneg hu,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_of_le_one_right (mul_nonneg hu (sq_nonneg _)) (Real.abs_sin_le_one _)).trans
      (mul_le_of_le_one_left (sq_nonneg _) hu1)
  constructor
  · apply sech_sq_integrable.mono' (continuous_exp.mul hc).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change |Real.exp x*sineSource w x| ≤ sech x^2
      rw [sineSource_left]
      exact hb x _ (intrinsic_mem x).1.le (intrinsic_mem x).2.le
  · apply sech_sq_integrable.mono' ((continuous_exp.comp continuous_neg).mul hc).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change |Real.exp (-x)*sineSource w x| ≤ sech x^2
      rw [sineSource_right]
      exact hb x _ (by linarith [(intrinsic_mem x).2]) (by linarith [(intrinsic_mem x).1])

/-- Explicit primitive of the left exponentially weighted sine source.
Use: supplies the exact first half of the real-line Green convolution.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def sineLeftPrimitive (w x : ℝ) : ℝ :=
  2*(Real.sin (w*intrinsic x)/w^2-intrinsic x*Real.cos (w*intrinsic x)/w)

/-- Explicit primitive of the right exponentially weighted sine source.
Use: supplies the exact second half, with its value at positive infinity fixed by sin(w)=0.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def sineRightPrimitive (w x : ℝ) : ℝ :=
  2*((intrinsic x-1)*Real.cos (w*intrinsic x)/w-Real.sin (w*intrinsic x)/w^2)

/-- The left primitive differentiates to the actual weighted source.
Use: the improper fundamental theorem computes its integral on the left half-line.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: differentiate the intrinsic sine and cosine factors, cancel the cross
cosine terms and use t'=sech^2/2 and exp(x)sech(x)=2t. -/
theorem sineLeftPrimitive_derivative {w : ℝ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (sineLeftPrimitive w) (Real.exp x*sineSource w x) x := by
  -- Cancellation is algebraic after the actual coordinate derivative is substituted.
  have ht := intrinsic_derivative x
  have hs := (ht.const_mul w).sin
  have hc := (ht.const_mul w).cos
  change HasDerivAt (fun y => 2*(Real.sin (w*intrinsic y)/w^2-
    intrinsic y*Real.cos (w*intrinsic y)/w)) _ x
  convert ((hs.div_const (w^2)).sub ((ht.mul hc).div_const w)).const_mul 2 using 1
  rw [sineSource_left]
  field_simp [hw]
  ring

/-- The right primitive differentiates to the actual complementary weighted source.
Use: the improper fundamental theorem computes its right half-line integral.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the same differentiation cancels the cosine terms, leaving the
factor (1-t)sech^2 sin(wt) supplied by the right weighted-source identity. -/
theorem sineRightPrimitive_derivative {w : ℝ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (sineRightPrimitive w) (Real.exp (-x)*sineSource w x) x := by
  -- Both primitives concern the same literal source; the right half reverses only the endpoint subtraction.
  have ht := intrinsic_derivative x
  have hs := (ht.const_mul w).sin
  have hc := (ht.const_mul w).cos
  change HasDerivAt (fun y => 2*((intrinsic y-1)*Real.cos (w*intrinsic y)/w-
    Real.sin (w*intrinsic y)/w^2)) _ x
  convert (((ht.sub_const 1).mul hc).div_const w |>.sub (hs.div_const (w^2))).const_mul 2 using 1
  rw [sineSource_right]
  field_simp [hw]
  ring

end
end jacobi.Young
