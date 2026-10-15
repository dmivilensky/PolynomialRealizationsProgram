import «2610.05164v2».GroundState.ExponentialPrimitive
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: 2610.05164v2, Theorem 3.4.
General L1 causal exponential filters.
Use: `«2610.05164v2».Filters.causal_le_mass` feeds
`«2610.05164v2».Comparison.density_mul_rightCausal_integrable` (density mul right Causal
integrable).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `causal` of type `ℝ` by `exp (-c*x) * ∫ t in Iic x, exp (c*t)*j t`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_bounds` uses this definition to establish
membership in the specified domain/enclosure: `C.leftLinear hκ q ∈ Icc (0:ℝ) q`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.
-/
def causal (c : ℝ) (j : ℝ → ℝ) (x : ℝ) : ℝ :=
  exp (-c*x) * ∫ t in Iic x, exp (c*t)*j t

/--
Integrability on the stated domain: `IntegrableOn (fun t => exp (c*t)*j t) (Iic x)`.

Use: `«2610.05164v2».Filters.causal_primitive` uses this integrability result to establish
exact identity `causal c j = GroundState.exponentialPrimitive (-c) j (∫ t in Iic (0:ℝ), exp
(c*t)*j t)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem forcing_integrable {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ}
    (hj : Integrable j) (x : ℝ) : IntegrableOn (fun t => exp (c*t)*j t) (Iic x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (hj.norm.mul_const (exp (c*x))).integrableOn.mono'
  · exact ((by fun_prop : Continuous (fun t : ℝ => exp (c*t))).aestronglyMeasurable.mul
      hj.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hc)) (norm_nonneg (j t))

/--
Exact identity `causal c j = GroundState.exponentialPrimitive (-c) j (∫ t in Iic (0:ℝ), exp
(c*t)*j t)`.

Use: `«2610.05164v2».Filters.causal_derivative_ae` rewrites with this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (causal c j)
(j x-c*causal c j x) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem causal_primitive {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j) :
    causal c j = GroundState.exponentialPrimitive (-c) j
      (∫ t in Iic (0:ℝ), exp (c*t)*j t) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  funext x
  have he := intervalIntegral.integral_Iic_sub_Iic
    (forcing_integrable hc hj 0) (forcing_integrable hc hj x)
  dsimp [causal,GroundState.exponentialPrimitive]
  simp only [neg_neg]
  congr 1
  linarith

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (causal c j) a
b`.

Use: `«2610.05164v2».Filters.causal_continuous` uses this assertion to establish continuity of
the displayed function: `Continuous (causal c j)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_primitive`,
`«2610.05164v2».GroundState.exponentialPrimitive_locallyAC` with the arguments shown in the
proof.
-/
theorem causal_locallyAC {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (causal c j) a b := by
  rw [causal_primitive hc hj]
  exact GroundState.exponentialPrimitive_locallyAC hj.locallyIntegrable _ _ _ _

/--
Continuity of the displayed function: `Continuous (causal c j)`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.locallyAC_continuous`,
`«2610.05164v2».Filters.causal_locallyAC` with the arguments shown in the proof.
-/
theorem causal_continuous {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j) :
    Continuous (causal c j) := GroundState.locallyAC_continuous (causal_locallyAC hc hj)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (causal c j)
(j x-c*causal c j x) x`.

Use: `«2610.05164v2».Filters.causal_hasDerivAt` uses this assertion to establish the actual
derivative at the stated point: `HasDerivAt (causal c m) (m x-c*causal c m x) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem causal_derivative_ae {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j) :
    ∀ᵐ x, HasDerivAt (causal c j) (j x-c*causal c j x) x := by
  rw [causal_primitive hc hj]
  filter_upwards [GroundState.exponentialPrimitive_derivative_ae hj.locallyIntegrable (-c)
    (∫ t in Iic (0:ℝ), exp (c*t)*j t)] with x hx
  convert hx using 1
  ring

/--
Defines `kernel` of type `ℝ → ℝ` by `(Iic x).indicator (fun t => exp (-c*(x-t)))`.

Use: `«2610.05164v2».Filters.causal_integral` rewrites with this definition to establish exact
identity `causal c j x = ∫ t, kernel c x t*j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.
-/
def kernel (c x : ℝ) : ℝ → ℝ := (Iic x).indicator (fun t => exp (-c*(x-t)))

/--
The stated quantitative bound `0 ≤ kernel c x t`.

Use: `«2610.05164v2».Filters.causal_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ causal c j x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem kernel_nonneg (c x t : ℝ) : 0 ≤ kernel c x t := by
  by_cases h : t ≤ x
  · simp only [kernel,indicator_of_mem (show t ∈ Iic x from h)]
    exact (exp_pos _).le
  · simp [kernel,h]

/--
The stated quantitative bound `kernel c x t ≤ 1`.

Use: `«2610.05164v2».Filters.causal_le_mass` uses this bound to establish the stated
quantitative bound `causal c j x ≤ ∫ t, j t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem kernel_le_one {c : ℝ} (hc : 0 ≤ c) (x t : ℝ) : kernel c x t ≤ 1 := by
  by_cases h : t ≤ x
  · simp only [kernel,indicator_of_mem (show t ∈ Iic x from h)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sub_nonneg.mpr h))
  · simp [kernel,h]

/--
Measurability of the displayed map: `Measurable (kernel c x)`.

Use: `«2610.05164v2».Filters.kernel_mul_integrable` uses this measurability result to establish
integrability of the displayed function: `Integrable (fun t => kernel c x t*j t)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem kernel_measurable (c x : ℝ) : Measurable (kernel c x) :=
  (by fun_prop : Measurable (fun t : ℝ => exp (-c*(x-t)))).indicator measurableSet_Iic

/--
Integrability of the displayed function: `Integrable (fun t => kernel c x t*j t)`.

Use: `«2610.05164v2».Filters.causal_le_mass` uses this integrability result to establish the
stated quantitative bound `causal c j x ≤ ∫ t, j t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.kernel_measurable`,
`«2610.05164v2».Filters.kernel_nonneg`, `«2610.05164v2».Filters.kernel_le_one` with the
arguments shown in the proof.
-/
theorem kernel_mul_integrable {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ}
    (hj : Integrable j) (x : ℝ) : Integrable (fun t => kernel c x t*j t) := by
  apply hj.norm.mono' ((kernel_measurable c x).aestronglyMeasurable.mul hj.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => by
    change ‖kernel c x t*j t‖ ≤ ‖j t‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg c x t)]
    exact mul_le_of_le_one_left (norm_nonneg _) (kernel_le_one hc x t))

/--
Exact identity `causal c j x = ∫ t, kernel c x t*j t`.

Use: `«2610.05164v2».Filters.causal_le_mass` rewrites with this identity to establish the
stated quantitative bound `causal c j x ≤ ∫ t, j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem causal_integral {c : ℝ} {j : ℝ → ℝ} (x : ℝ) :
    causal c j x = ∫ t, kernel c x t*j t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [causal,← integral_const_mul]
  have he : (fun t => kernel c x t*j t)=
      (Iic x).indicator (fun t => exp (-c*x)*(exp (c*t)*j t)) := by
    funext t
    by_cases ht : t ≤ x
    · simp only [kernel,indicator_of_mem (show t ∈ Iic x from ht)]
      rw [show -c*(x-t)=-c*x+c*t by ring,exp_add]
      ring
    · simp [kernel,ht]
  rw [he,integral_indicator measurableSet_Iic]

/--
The stated quantitative bound `0 ≤ causal c j x`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_bounds` uses this bound to establish
membership in the specified domain/enclosure: `C.leftLinear hκ q ∈ Icc (0:ℝ) q`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integral`,
`«2610.05164v2».Filters.kernel_nonneg` with the arguments shown in the proof.
-/
theorem causal_nonneg {c : ℝ} {j : ℝ → ℝ} (hn : ∀ᵐ t, 0 ≤ j t) (x : ℝ) :
    0 ≤ causal c j x := by
  rw [causal_integral]
  exact integral_nonneg_of_ae (hn.mono (fun t ht => mul_nonneg (kernel_nonneg c x t) ht))

/--
The stated quantitative bound `causal c j x ≤ ∫ t, j t`.

Use: `«2610.05164v2».Comparison.density_mul_causal_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => m x*causal 2 m x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integral`,
`«2610.05164v2».Filters.kernel_mul_integrable`, `«2610.05164v2».Filters.kernel_le_one` with the
arguments shown in the proof.
-/
theorem causal_le_mass {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ}
    (hj : Integrable j) (hn : ∀ᵐ t, 0 ≤ j t) (x : ℝ) : causal c j x ≤ ∫ t, j t := by
  rw [causal_integral]
  apply integral_mono_ae (kernel_mul_integrable hc hj x) hj
  exact hn.mono (fun t ht => mul_le_of_le_one_left ht (kernel_le_one hc x t))

end
end «2610.05164v2».Filters
