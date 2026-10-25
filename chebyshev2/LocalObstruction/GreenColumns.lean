import chebyshev2.LocalObstruction.GreenIdentities
import chebyshev2.HalfLine.GreenCancellation

/-!
Article: chebyshev2, Theorem 6.1.
Exact half-line profiles and response integrals of the two-sided Jost Green column.
Use: `chebyshev2.LocalObstruction.greenColumn_right_boundary_integral` feeds
`chebyshev2.LocalObstruction.greenColumn_boundary_convolution` (green Column boundary
convolution).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Filters chebyshev2.HalfLine chebyshev2.GroundState
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x)

 /--
Exact identity `greenKernel s m (-x) (-y)=greenKernel s m x y`.

Use: `chebyshev2.LocalObstruction.greenColumn_right_boundary_integral` rewrites with this
identity to establish `s*(∫ y in Ioi x,exp (x-y)*(m y*greenKernel s m
x y))= greenKernel s m x x*nonlinear s m (-x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenKernel_reflect (x y : ℝ) : greenKernel s m (-x) (-y)=greenKernel s m x y := by
  unfold greenKernel
  rw [min_neg_neg,max_neg_neg,neg_neg]
  ring

include hm hn hs

 /--
Exact identity `greenKernel s m x t=greenKernel s m x x*jostProfile s m x t`.

Use: `chebyshev2.LocalObstruction.greenColumn_left_boundary_integral` rewrites with this
identity to establish `s*(∫ y in Iio x,exp (y-x)*(m y*greenKernel s m
x y))= greenKernel s m x x*nonlinear s m x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem greenKernel_left_profile {x t : ℝ} (ht : t≤x) :
    greenKernel s m x t=greenKernel s m x x*jostProfile s m x t := by
  unfold greenKernel jostProfile jostFunction
  rw [min_eq_right ht,max_eq_left ht,min_self,max_self]
  have hex : exp x*exp (t-x)=exp t := by rw [← exp_add];congr 1;ring
  field_simp [(jost_positive hm hn hs x).ne',(wronskian_positive hm hn hs 0).ne']
  rw [← hex]
  ring

include hc he in
 /--
Integrability of the displayed function: `Integrable (fun y => m y*greenKernel s m x y)`.

Use: `chebyshev2.LocalObstruction.fullResolvent_feature_green` uses this integrability
result to establish the identity `inner ℝ (feature y) (fullResolvent m s (feature
x))=2*greenKernel s m x y`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.greenKernel_continuous`,
`chebyshev2.LocalObstruction.greenKernel_positive`,
`chebyshev2.LocalObstruction.greenKernel_bound` with the arguments shown in the proof.
-/
theorem greenColumn_integrable (x : ℝ) : Integrable (fun y => m y*greenKernel s m x y) := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.greenKernel_continuous`,
  -- `chebyshev2.LocalObstruction.greenKernel_positive`,
  -- `chebyshev2.LocalObstruction.greenKernel_bound` with the arguments shown in the proof.
  apply hm.mul_bdd (c := (1/2:ℝ))
  · exact (greenKernel_continuous hm hn hs).comp (continuous_const.prodMk continuous_id)
      |>.aestronglyMeasurable
  · apply Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs,abs_of_pos (greenKernel_positive hm hn hs x y)]
    exact (greenKernel_bound hm hn hc hs he x y).trans
      (by have := exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg (x-y)));linarith)

 /--
Exact identity `s*(∫ y in Iio x,exp (y-x)*(m y*jostProfile s m x y))=nonlinear s m x`.

Use: `chebyshev2.LocalObstruction.greenColumn_left_boundary_integral` uses this identity to
establish the precise assertion is `s*(∫ y in Iio x,exp (y-x)*(m y*greenKernel s m x y))=
greenKernel s m x x*nonlinear s m x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem jost_response_integral (x : ℝ) :
    s*(∫ y in Iio x,exp (y-x)*(m y*jostProfile s m x y))=nonlinear s m x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp : (fun y => exp (y-x)*(m y*jostProfile s m x y))=
      fun y => exp (-2*x)*(exp (2*y)*(m y*jost s m y))/jost s m x := by
    funext y
    unfold jostProfile
    have hex : exp (y-x)*exp (y-x)=exp (-2*x)*exp (2*y) := by
      rw [← exp_add,← exp_add];congr 1;ring
    field_simp [(jost_positive hm hn hs x).ne']
    rw [show -(x*2)=-2*x by ring,show y*2=2*y by ring]
    linear_combination m y*jost s m y*hex
  rw [hp,integral_div,integral_const_mul,← integral_Iic_eq_integral_Iio]
  unfold nonlinear jostSlope causal
  ring

 /--
The stated quantitative bound `greenKernel s m x t+s*greenSolution x (fun y => leftDensity m x
y*greenKernel s m x y) t= greenKernel s m x x*exp (t-x)`.

Use: `chebyshev2.LocalObstruction.greenColumn_left_convolution` uses this identity to
establish the stated quantitative bound `greenKernel s m x t+s/2*H1.rep (convolution (fun y =>
m y*greenKernel s m x y)) t= exp (t-x)/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenColumn_left_equation {x t : ℝ} (ht : t<x) :
    greenKernel s m x t+s*greenSolution x
      (fun y => leftDensity m x y*greenKernel s m x y) t=
      greenKernel s m x x*exp (t-x) := by
  -- Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hforce : (fun y => leftDensity m x y*greenKernel s m x y)=
      fun y => (leftDensity m x y*jostProfile s m x y)*greenKernel s m x x := by
    funext y
    by_cases hy : y<x
    · rw [greenKernel_left_profile hm hn hs hy.le]
      ring
    · simp [leftDensity,hy]
  have hi := weighted_forcing_integrable hm hn x
    (jostProfile_continuous hm hn hs x).aestronglyMeasurable
    (fun _ hy => jostProfile_bound hm hn hs hy)
  rw [greenKernel_left_profile hm hn hs ht.le,hforce,greenSolution_mul_const hi]
  linear_combination greenKernel s m x x*jost_green_equation hm hn hs ht

 /--
The precise assertion is `s*(∫ y in Iio x,exp (y-x)*(m y*greenKernel s m x y))= greenKernel s m
x x*nonlinear s m x`.

Use: `chebyshev2.LocalObstruction.greenColumn_right_boundary_integral` uses this identity
to establish `s*(∫ y in Ioi x,exp (x-y)*(m y*greenKernel s m x y))=
greenKernel s m x x*nonlinear s m (-x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.greenKernel_left_profile`,
`chebyshev2.LocalObstruction.jost_response_integral` with the arguments shown in the proof.
-/
theorem greenColumn_left_boundary_integral (x : ℝ) :
    s*(∫ y in Iio x,exp (y-x)*(m y*greenKernel s m x y))=
      greenKernel s m x x*nonlinear s m x := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.greenKernel_left_profile`,
  -- `chebyshev2.LocalObstruction.jost_response_integral` with the arguments shown in the
  -- proof.
  have hi : (∫ y in Iio x,exp (y-x)*(m y*greenKernel s m x y))=
      greenKernel s m x x*(∫ y in Iio x,exp (y-x)*(m y*jostProfile s m x y)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    dsimp only
    rw [greenKernel_left_profile hm hn hs hy.le]
    ring
  rw [hi]
  linear_combination greenKernel s m x x*jost_response_integral hm hn hs x

include he in
 /--
The precise assertion is `s*(∫ y in Ioi x,exp (x-y)*(m y*greenKernel s m x y))= greenKernel s m
x x*nonlinear s m (-x)`.

Use: `chebyshev2.LocalObstruction.greenColumn_boundary_convolution` uses this identity to
establish exact identity `greenKernel s m x x+s/2*H1.rep (convolution (fun y => m y*greenKernel
s m x y)) x=1/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenColumn_right_boundary_integral (x : ℝ) :
    s*(∫ y in Ioi x,exp (x-y)*(m y*greenKernel s m x y))=
      greenKernel s m x x*nonlinear s m (-x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h := greenColumn_left_boundary_integral hm hn hs (-x)
  have hreflect : (fun y => exp (y-(-x))*(m y*greenKernel s m (-x) y))=
      (fun y => exp (x-y)*(m y*greenKernel s m x y)) ∘ Neg.neg := by
    funext y
    dsimp only [Function.comp_apply]
    rw [he,← greenKernel_reflect (s := s) (m := m) x (-y),neg_neg]
    congr 2
    ring
  rw [hreflect,← integral_Iic_eq_integral_Iio] at h
  simp only [Function.comp_def] at h
  rw [integral_comp_neg_Iic (-x) (fun y => exp (x-y)*(m y*greenKernel s m x y)),neg_neg,greenKernel_reflect] at h
  exact h

end
end chebyshev2.LocalObstruction
