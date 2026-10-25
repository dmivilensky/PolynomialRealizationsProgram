import chebyshev2.Filters.JostFunction
import chebyshev2.Filters.ContinuousDensity
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: chebyshev2, Theorem 6.1.
Lemma 26's actual two-sided Jost Green kernel for an even continuous L1 density: constant positive
Wronskian, symmetry, continuity and exponential bound.
Use: `chebyshev2.LocalObstruction.greenKernel_continuous` feeds
`chebyshev2.LocalObstruction.greenColumn_integrable` (green Column integrable).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Filters chebyshev2.GroundState
set_option backward.isDefEq.respectTransparency false

/--
Defines `wronskian` of type `ℝ` by `jostFunctionSlope s m x*jostFunction s m (-x)+ jostFunction
s m x*jostFunctionSlope s m (-x)`.

Use: `chebyshev2.LocalObstruction.greenKernel` uses this definition in the displayed
construction of `greenKernel`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def wronskian (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  jostFunctionSlope s m x*jostFunction s m (-x)+
    jostFunction s m x*jostFunctionSlope s m (-x)

/--
Defines `greenKernel` of type `ℝ` by `jostFunction s m (min x y)*jostFunction s m (-max x
y)/wronskian s m 0`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` uses this definition to establish
the stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def greenKernel (s : ℝ) (m : ℝ → ℝ) (x y : ℝ) : ℝ :=
  jostFunction s m (min x y)*jostFunction s m (-max x y)/wronskian s m 0

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hc : Continuous m) {s : ℝ} (hs : 0 ≤ s)
include hm hn hc hs

/--
The actual derivative at the stated point: `HasDerivAt (jostFunctionSlope s m) ((1+s*m
x)*jostFunction s m x) x`.

Use: `chebyshev2.LocalObstruction.wronskian_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (wronskian s m) 0 x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_continuous`,
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.Filters.jostFunctionSlope_locallyAC` with the arguments shown in the proof.
-/
theorem jostFunctionSlope_derivative (x : ℝ) :
    HasDerivAt (jostFunctionSlope s m) ((1+s*m x)*jostFunction s m x) x := by
  have hu : Continuous (jostFunction s m) := continuous_exp.mul (jost_continuous hm hn hs)
  exact locallyAC_hasDerivAt_of_continuous (jostFunctionSlope_locallyAC hm hn hs)
    (jostFunction_ode hm hn hs)
    ((continuous_const.add (continuous_const.mul hc)).mul hu) x

/--
The actual derivative at the stated point: `HasDerivAt (wronskian s m) 0 x`.

Use: `chebyshev2.LocalObstruction.wronskian_constant` uses this derivative formula to
establish exact identity `wronskian s m x=wronskian s m 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jostFunction_hasDerivAt`,
`chebyshev2.LocalObstruction.jostFunctionSlope_derivative` with the arguments shown in the
proof.
-/
theorem wronskian_derivative (he : ∀ x, m (-x)=m x) (x : ℝ) :
    HasDerivAt (wronskian s m) 0 x := by
  -- Use the identities/estimates `chebyshev2.Filters.jostFunction_hasDerivAt`,
  -- `chebyshev2.LocalObstruction.jostFunctionSlope_derivative` with the arguments shown in
  -- the proof.
  have hl := jostFunction_hasDerivAt hm hn hs x
  have hl' := jostFunctionSlope_derivative hm hn hc hs x
  have hr := (jostFunction_hasDerivAt hm hn hs (-x)).comp x (hasDerivAt_neg x)
  have hr' := (jostFunctionSlope_derivative hm hn hc hs (-x)).comp x (hasDerivAt_neg x)
  convert! (hl'.mul hr).add (hl.mul hr') using 1
  rw [he]
  simp only [Function.comp_apply,mul_neg_one]
  ring

/--
Exact identity `wronskian s m x=wronskian s m 0`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` rewrites with this identity to
establish the stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.wronskian_derivative` with
the arguments shown in the proof.
-/
theorem wronskian_constant (he : ∀ x, m (-x)=m x) (x : ℝ) :
    wronskian s m x=wronskian s m 0 :=
  is_const_of_deriv_eq_zero (fun x => (wronskian_derivative hm hn hc hs he x).differentiableAt)
    (fun x => (wronskian_derivative hm hn hc hs he x).deriv) x 0

omit hc in
/--
The stated quantitative bound `0<jostFunction s m x`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` uses this bound to establish the
stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_positive` with the arguments
shown in the proof.
-/
theorem jostFunction_positive (x : ℝ) : 0<jostFunction s m x :=
  mul_pos (exp_pos _) (jost_positive hm hn hs x)

omit hc in
/--
The stated quantitative bound `jostFunction s m x≤jostFunctionSlope s m x`.

Use: `chebyshev2.LocalObstruction.wronskian_ge` uses this bound to establish the stated
quantitative bound `2*jostFunction s m x*jostFunction s m (-x)≤wronskian s m x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jostSlope_nonneg` with the
arguments shown in the proof.
-/
theorem jostFunctionSlope_ge (x : ℝ) : jostFunction s m x≤jostFunctionSlope s m x := by
  have h := jostSlope_nonneg hm hn hs x
  unfold jostFunction jostFunctionSlope
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h) (exp_pos _).le

omit hc in
/--
The stated quantitative bound `2*jostFunction s m x*jostFunction s m (-x)≤wronskian s m x`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` uses this bound to establish the
stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.jostFunctionSlope_ge`,
`chebyshev2.LocalObstruction.jostFunction_positive` with the arguments shown in the proof.
-/
theorem wronskian_ge (x : ℝ) :
    2*jostFunction s m x*jostFunction s m (-x)≤wronskian s m x := by
  have h₀ := mul_le_mul_of_nonneg_right (jostFunctionSlope_ge hm hn hs x)
    (jostFunction_positive hm hn hs (-x)).le
  have h₁ := mul_le_mul_of_nonneg_left (jostFunctionSlope_ge hm hn hs (-x))
    (jostFunction_positive hm hn hs x).le
  unfold wronskian
  nlinarith

omit hc in
/--
The stated quantitative bound `0<wronskian s m x`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` uses this bound to establish the
stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.jostFunction_positive`,
`chebyshev2.LocalObstruction.wronskian_ge` with the arguments shown in the proof.
-/
theorem wronskian_positive (x : ℝ) : 0<wronskian s m x :=
  (mul_pos (mul_pos (by norm_num) (jostFunction_positive hm hn hs x))
    (jostFunction_positive hm hn hs (-x))).trans_le (wronskian_ge hm hn hs x)

omit hm hn hc hs in
/--
Exact identity `greenKernel s m x y=greenKernel s m y x`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound` rewrites with this identity to
establish the stated quantitative bound `greenKernel s m x y≤exp (-|x-y|)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenKernel_symmetric (s : ℝ) (m : ℝ → ℝ) (x y : ℝ) :
    greenKernel s m x y=greenKernel s m y x := by simp only [greenKernel,min_comm,max_comm]

omit hc in
/--
The stated quantitative bound `0<greenKernel s m x y`.

Use: `chebyshev2.LocalObstruction.greenColumn_integrable` rewrites with this bound to
establish integrability of the displayed function: `Integrable (fun y => m y*greenKernel s m x
y)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.jostFunction_positive`,
`chebyshev2.LocalObstruction.wronskian_positive` with the arguments shown in the proof.
-/
theorem greenKernel_positive (x y : ℝ) : 0<greenKernel s m x y :=
  div_pos (mul_pos (jostFunction_positive hm hn hs _) (jostFunction_positive hm hn hs _))
    (wronskian_positive hm hn hs 0)

omit hc in
/--
The stated quantitative bound `jostFunction s m x≤exp (x-y)*jostFunction s m y`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound_left` uses this bound to establish the
stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_monotone` with the arguments
shown in the proof.
-/
theorem jostFunction_growth {x y : ℝ} (hxy : x≤y) :
    jostFunction s m x≤exp (x-y)*jostFunction s m y := by
  have h := mul_le_mul_of_nonneg_left (jost_monotone hm hn hs hxy) (exp_pos x).le
  convert! h using 1
  unfold jostFunction
  rw [← mul_assoc,← exp_add]
  congr 2
  ring

/--
The stated quantitative bound `greenKernel s m x y≤exp (x-y)/2`.

Use: `chebyshev2.LocalObstruction.greenKernel_bound` uses this bound to establish the
stated quantitative bound `greenKernel s m x y≤exp (-|x-y|)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.wronskian_positive`,
`chebyshev2.LocalObstruction.jostFunction_growth`,
`chebyshev2.LocalObstruction.jostFunction_positive` with the arguments shown in the proof.
-/
theorem greenKernel_bound_left (he : ∀ x, m (-x)=m x) {x y : ℝ} (hxy : x≤y) :
    greenKernel s m x y≤exp (x-y)/2 := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.wronskian_positive`,
  -- `chebyshev2.LocalObstruction.jostFunction_growth`,
  -- `chebyshev2.LocalObstruction.jostFunction_positive` with the arguments shown in the
  -- proof.
  unfold greenKernel
  rw [min_eq_left hxy,max_eq_right hxy]
  apply (div_le_iff₀ (wronskian_positive hm hn hs 0)).2
  have h₀ := mul_le_mul_of_nonneg_right (jostFunction_growth hm hn hs hxy)
    (jostFunction_positive hm hn hs (-y)).le
  have h₁ := mul_le_mul_of_nonneg_left (wronskian_ge hm hn hs y)
    (div_nonneg (exp_pos (x-y)).le (by norm_num : (0:ℝ)≤2))
  rw [wronskian_constant hm hn hc hs he y] at h₁
  nlinarith

/--
The stated quantitative bound `greenKernel s m x y≤exp (-|x-y|)/2`.

Use: `chebyshev2.LocalObstruction.greenColumn_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun y => m y*greenKernel s m x y)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.greenKernel_bound_left`,
`chebyshev2.LocalObstruction.greenKernel_symmetric` with the arguments shown in the proof.
-/
theorem greenKernel_bound (he : ∀ x, m (-x)=m x) (x y : ℝ) :
    greenKernel s m x y≤exp (-|x-y|)/2 := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),neg_neg]
    exact greenKernel_bound_left hm hn hc hs he h
  · rw [greenKernel_symmetric,abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr h),neg_neg]
    exact greenKernel_bound_left hm hn hc hs he h

omit hc in
/--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => greenKernel s m p.1 p.2)`.

Use: `chebyshev2.LocalObstruction.greenColumn_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun y => m y*greenKernel s m x
y)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_continuous` with the arguments
shown in the proof.
-/
theorem greenKernel_continuous : Continuous (fun p : ℝ × ℝ => greenKernel s m p.1 p.2) := by
  have hu : Continuous (jostFunction s m) := continuous_exp.mul (jost_continuous hm hn hs)
  exact ((hu.comp (continuous_fst.min continuous_snd)).mul
    (hu.comp (continuous_fst.max continuous_snd).neg)).div_const _

end
end chebyshev2.LocalObstruction
