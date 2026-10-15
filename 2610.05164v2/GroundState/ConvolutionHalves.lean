import «2610.05164v2».GroundState.Convolution
import «2610.05164v2».GroundState.ExponentialPrimitive

/-!
Article: 2610.05164v2, Theorem 3.1.
Convolution Halves.
Use: `«2610.05164v2».GroundState.rightGreen_derivative_ae` feeds
`«2610.05164v2».GroundState.convolution_second_derivative_ae` (convolution second derivative ae).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `leftGreen` of type `ℝ` by `exp (-x)*∫ t in Iic x, exp t*j t`.

Use: `«2610.05164v2».GroundState.convolution_halves` rewrites with this definition to establish
exact identity `H1.rep (convolution j) x=leftGreen j x+rightGreen j x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def leftGreen (j : ℝ → ℝ) (x : ℝ) : ℝ := exp (-x)*∫ t in Iic x, exp t*j t
/--
Defines `rightGreen` of type `ℝ` by `exp x*∫ t in Ioi x, exp (-t)*j t`.

Use: `«2610.05164v2».GroundState.convolution_halves` rewrites with this definition to establish
exact identity `H1.rep (convolution j) x=leftGreen j x+rightGreen j x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def rightGreen (j : ℝ → ℝ) (x : ℝ) : ℝ := exp x*∫ t in Ioi x, exp (-t)*j t

/--
Integrability on the stated domain: `IntegrableOn (fun t => exp t*j t) (Iic x)`.

Use: `«2610.05164v2».GroundState.leftGreen_primitive` uses this integrability result to
establish exact identity `leftGreen j=exponentialPrimitive (-1) j (∫ t in Iic (0:ℝ), exp t*j
t)`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem leftForcing_integrable {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    IntegrableOn (fun t => exp t*j t) (Iic x) := by
  apply (hj.norm.mul_const (exp x)).integrableOn.mono'
  · exact (continuous_exp.aestronglyMeasurable.mul hj.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (exp_le_exp.mpr ht) (norm_nonneg (j t))

/--
Integrability on the stated domain: `IntegrableOn (fun t => exp (-t)*j t) (Ioi x)`.

Use: `«2610.05164v2».GroundState.rightGreen_primitive` uses this integrability result to
establish exact identity `rightGreen j=exponentialPrimitive 1 (fun t => -j t) (∫ t in Ioi
(0:ℝ), exp (-t)*j t)`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem rightForcing_integrable {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    IntegrableOn (fun t => exp (-t)*j t) (Ioi x) := by
  apply (hj.norm.mul_const (exp (-x))).integrableOn.mono'
  · exact ((continuous_exp.comp continuous_neg).aestronglyMeasurable.mul hj.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (exp_le_exp.mpr (neg_le_neg ht.le)) (norm_nonneg (j t))

/--
Exact identity `H1.rep (convolution j) x=leftGreen j x+rightGreen j x`.

Use: `«2610.05164v2».GroundState.convolutionSlope_abs_le` rewrites with this identity to
establish the stated quantitative bound `|convolutionSlope j x| ≤ H1.rep (convolution j) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.convolution_rep`,
`«2610.05164v2».GroundState.convolution_kernel_integrable` with the arguments shown in the
proof.
-/
theorem convolution_halves {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    H1.rep (convolution j) x=leftGreen j x+rightGreen j x := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.convolution_rep`,
  -- `«2610.05164v2».GroundState.convolution_kernel_integrable` with the arguments shown in the
  -- proof.
  rw [convolution_rep hj,← intervalIntegral.integral_Iic_add_Ioi
    (convolution_kernel_integrable hj x).integrableOn
    (convolution_kernel_integrable hj x).integrableOn (b := x)]
  congr 1
  · rw [leftGreen,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    change exp (-|x-t|)*j t=exp (-x)*(exp t*j t)
    rw [abs_of_nonneg (sub_nonneg.mpr (show t ≤ x from ht)),show -(x-t)=-x+t by ring,exp_add]
    ring
  · rw [rightGreen,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change exp (-|x-t|)*j t=exp x*(exp (-t)*j t)
    rw [abs_of_nonpos (sub_nonpos.mpr ht.le),show -(-(x-t))=x+(-t) by ring,exp_add]
    ring

/--
Exact identity `leftGreen j=exponentialPrimitive (-1) j (∫ t in Iic (0:ℝ), exp t*j t)`.

Use: `«2610.05164v2».GroundState.leftGreen_derivative_ae` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(leftGreen j) (-leftGreen j x+j x) x`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem leftGreen_primitive {j : ℝ → ℝ} (hj : Integrable j) :
    leftGreen j=exponentialPrimitive (-1) j (∫ t in Iic (0:ℝ), exp t*j t) := by
  funext x
  have he := intervalIntegral.integral_Iic_sub_Iic (leftForcing_integrable hj 0) (leftForcing_integrable hj x)
  dsimp [leftGreen,exponentialPrimitive]
  simp only [neg_one_mul,neg_neg,one_mul]
  congr 1
  linarith

/--
Exact identity `rightGreen j=exponentialPrimitive 1 (fun t => -j t) (∫ t in Ioi (0:ℝ), exp
(-t)*j t)`.

Use: `«2610.05164v2».GroundState.rightGreen_derivative_ae` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(rightGreen j) (rightGreen j x-j x) x`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightGreen_primitive {j : ℝ → ℝ} (hj : Integrable j) :
    rightGreen j=exponentialPrimitive 1 (fun t => -j t) (∫ t in Ioi (0:ℝ), exp (-t)*j t) := by
  funext x
  have he := intervalIntegral.integral_Ioi_sub_Ioi' (rightForcing_integrable hj 0) (rightForcing_integrable hj x)
  dsimp [rightGreen,exponentialPrimitive]
  simp only [one_mul,neg_one_mul,mul_neg,intervalIntegral.integral_neg]
  congr 1
  linarith

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (leftGreen j) a
b`.

Use: `«2610.05164v2».GroundState.convolutionSlope_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(convolutionSlope j) a b`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.leftGreen_primitive`,
`«2610.05164v2».GroundState.exponentialPrimitive_locallyAC` with the arguments shown in the
proof.
-/
theorem leftGreen_locallyAC {j : ℝ → ℝ} (hj : Integrable j) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (leftGreen j) a b := by
  rw [leftGreen_primitive hj]
  exact exponentialPrimitive_locallyAC hj.locallyIntegrable _ _ _ _

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (rightGreen j) a
b`.

Use: `«2610.05164v2».GroundState.convolutionSlope_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(convolutionSlope j) a b`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.rightGreen_primitive`,
`«2610.05164v2».GroundState.exponentialPrimitive_locallyAC` with the arguments shown in the
proof.
-/
theorem rightGreen_locallyAC {j : ℝ → ℝ} (hj : Integrable j) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (rightGreen j) a b := by
  rw [rightGreen_primitive hj]
  exact exponentialPrimitive_locallyAC hj.neg.locallyIntegrable _ _ _ _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (leftGreen j)
(-leftGreen j x+j x) x`.

Use: `«2610.05164v2».GroundState.convolution_derivative_ae` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (H1.rep
(convolution j)) (convolutionSlope j x) x`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.leftGreen_primitive`,
`«2610.05164v2».GroundState.exponentialPrimitive_derivative_ae` with the arguments shown in the
proof.
-/
theorem leftGreen_derivative_ae {j : ℝ → ℝ} (hj : Integrable j) :
    ∀ᵐ x, HasDerivAt (leftGreen j) (-leftGreen j x+j x) x := by
  rw [leftGreen_primitive hj]
  simpa only [neg_one_mul] using exponentialPrimitive_derivative_ae hj.locallyIntegrable (-1) _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (rightGreen j)
(rightGreen j x-j x) x`.

Use: `«2610.05164v2».GroundState.convolution_derivative_ae` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (H1.rep
(convolution j)) (convolutionSlope j x) x`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.rightGreen_primitive`,
`«2610.05164v2».GroundState.exponentialPrimitive_derivative_ae` with the arguments shown in the
proof.
-/
theorem rightGreen_derivative_ae {j : ℝ → ℝ} (hj : Integrable j) :
    ∀ᵐ x, HasDerivAt (rightGreen j) (rightGreen j x-j x) x := by
  rw [rightGreen_primitive hj]
  simpa only [one_mul,sub_eq_add_neg] using
    exponentialPrimitive_derivative_ae (j := fun t => -j t) hj.neg.locallyIntegrable 1 _

end
end «2610.05164v2».GroundState
