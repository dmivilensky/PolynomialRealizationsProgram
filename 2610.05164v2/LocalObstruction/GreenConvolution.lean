import «2610.05164v2».LocalObstruction.GreenColumns
import «2610.05164v2».HalfLine.GreenL1Data

/-!
Article: 2610.05164v2, Theorem 6.1.
The two-sided Jost Green column satisfies the full free-kernel integral identity, obtained by gluing
the proved half-line identities.
Use: `«2610.05164v2».LocalObstruction.greenColumn_fredholm` feeds
`«2610.05164v2».LocalObstruction.fullResolvent_feature_green` (full Resolvent feature green).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».HalfLine «2610.05164v2».GroundState «2610.05164v2».Sobolev
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x)
include hm hn hc hs he

 /--
Exact identity `greenKernel s m x x+s/2*H1.rep (convolution (fun y => m y*greenKernel s m x y))
x=1/2`.

Use: `«2610.05164v2».LocalObstruction.greenColumn_fredholm` uses this identity to establish the
precise assertion is `greenKernel s m x t+s/2*(∫ y,exp (-|t-y|)*(m y*greenKernel s m x y))= exp
(-|x-t|)/2`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.greenColumn_integrable`,
`«2610.05164v2».GroundState.convolution_kernel_integrable`,
`«2610.05164v2».LocalObstruction.greenColumn_left_boundary_integral` with the arguments shown
in the proof.
-/
theorem greenColumn_boundary_convolution (x : ℝ) :
    greenKernel s m x x+s/2*H1.rep (convolution (fun y => m y*greenKernel s m x y)) x=1/2 := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.greenColumn_integrable`,
  -- `«2610.05164v2».GroundState.convolution_kernel_integrable`,
  -- `«2610.05164v2».LocalObstruction.greenColumn_left_boundary_integral` with the arguments
  -- shown in the proof.
  let j := fun y => m y*greenKernel s m x y
  have hj := greenColumn_integrable hm hn hc hs he x
  have hi := intervalIntegral.integral_Iic_add_Ioi
    (convolution_kernel_integrable hj x).integrableOn (convolution_kernel_integrable hj x).integrableOn (b := x)
  have hleft : (∫ y in Iic x,exp (-|x-y|)*j y)=∫ y in Iio x,exp (y-x)*(m y*greenKernel s m x y) := by
    rw [← integral_Iic_eq_integral_Iio]
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    dsimp only [j]
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    congr 2
    ring
  have hright : (∫ y in Ioi x,exp (-|x-y|)*j y)=∫ y in Ioi x,exp (x-y)*(m y*greenKernel s m x y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only [j]
    rw [abs_of_nonpos (sub_nonpos.mpr hy.le),neg_neg]
  have hL := greenColumn_left_boundary_integral hm hn hs x
  have hR := greenColumn_right_boundary_integral hm hn hs he x
  have hG := greenKernel_diagonal hm hn hc hs he x
  have hden : 0<2+nonlinear s m x+nonlinear s m (-x) := by
    linarith [(nonlinear_bounds hm hn hs x).1,(nonlinear_bounds hm hn hs (-x)).1]
  have hmul := (eq_div_iff hden.ne').mp hG
  rw [hleft,hright] at hi
  rw [convolution_rep hj,← hi]
  linear_combination hL/2+hR/2+hmul/2

 /--
The stated quantitative bound `greenKernel s m x t+s/2*H1.rep (convolution (fun y => m
y*greenKernel s m x y)) t= exp (t-x)/2`.

Use: `«2610.05164v2».LocalObstruction.greenColumn_fredholm` uses this identity to establish the
precise assertion is `greenKernel s m x t+s/2*(∫ y,exp (-|t-y|)*(m y*greenKernel s m x y))= exp
(-|x-t|)/2`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenColumn_left_convolution {x t : ℝ} (ht : t<x) :
    greenKernel s m x t+s/2*H1.rep (convolution (fun y => m y*greenKernel s m x y)) t=
      exp (t-x)/2 := by
  -- Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hj := greenColumn_integrable hm hn hc hs he x
  have hhalf := greenColumn_left_equation hm hn hs ht
  have hforce : (fun y => leftDensity m x y*greenKernel s m x y)=
      leftDensity (fun y => m y*greenKernel s m x y) x := by
    funext y
    by_cases hy : y<x <;> simp [leftDensity,hy]
  rw [hforce] at hhalf
  have hgreen := greenSolution_full_convolution hj ht.le
  have hboundary := greenColumn_boundary_convolution hm hn hc hs he x
  have heq : greenSolution x (leftDensity (fun y => m y*greenKernel s m x y) x) t=
      greenSolution x (fun y => m y*greenKernel s m x y) t := by
    unfold greenSolution
    simp only [leftDensity_idempotent]
  rw [heq,hgreen] at hhalf
  linear_combination hhalf+exp (t-x)*hboundary

 /--
The stated quantitative bound `H1.rep (convolution (fun y => m y*greenKernel s m (-x) y)) (-t)=
H1.rep (convolution (fun y => m y*greenKernel s m x y)) t`.

Use: `«2610.05164v2».LocalObstruction.greenColumn_fredholm` rewrites with this identity to
establish the precise assertion is `greenKernel s m x t+s/2*(∫ y,exp (-|t-y|)*(m y*greenKernel
s m x y))= exp (-|x-t|)/2`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem greenColumn_convolution_reflect (x t : ℝ) :
    H1.rep (convolution (fun y => m y*greenKernel s m (-x) y)) (-t)=
      H1.rep (convolution (fun y => m y*greenKernel s m x y)) t := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [convolution_rep (greenColumn_integrable hm hn hc hs he (-x)),
    convolution_rep (greenColumn_integrable hm hn hc hs he x)]
  have hi := integral_neg_eq_self (fun y => exp (-|t-y|)*(m y*greenKernel s m x y))
  rw [← hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [← he y,← greenKernel_reflect (s := s) (m := m) x (-y),neg_neg]
    have habs : |-t-y|=|t- -y| := by rw [show -t-y=-(t- -y) by ring,abs_neg]
    rw [habs])

 /--
The precise assertion is `greenKernel s m x t+s/2*(∫ y,exp (-|t-y|)*(m y*greenKernel s m x y))=
exp (-|x-t|)/2`.

Use: `«2610.05164v2».LocalObstruction.fullResolvent_feature_green` uses this identity to
establish exact identity `inner ℝ (feature y) (fullResolvent m s (feature x))=2*greenKernel s m
x y`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.convolution_rep`,
`«2610.05164v2».LocalObstruction.greenColumn_integrable`,
`«2610.05164v2».LocalObstruction.greenColumn_left_convolution` with the arguments shown in the
proof.
-/
theorem greenColumn_fredholm (x t : ℝ) :
    greenKernel s m x t+s/2*(∫ y,exp (-|t-y|)*(m y*greenKernel s m x y))=
      exp (-|x-t|)/2 := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.convolution_rep`,
  -- `«2610.05164v2».LocalObstruction.greenColumn_integrable`,
  -- `«2610.05164v2».LocalObstruction.greenColumn_left_convolution` with the arguments shown in
  -- the proof.
  rw [← convolution_rep (greenColumn_integrable hm hn hc hs he x)]
  rcases lt_trichotomy t x with hlt | rfl | hgt
  · have h := greenColumn_left_convolution hm hn hc hs he hlt
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    convert! h using 1
    congr 2
    ring
  · simpa using greenColumn_boundary_convolution hm hn hc hs he t
  · have h := greenColumn_left_convolution hm hn hc hs he (neg_lt_neg hgt)
    rw [greenKernel_reflect,greenColumn_convolution_reflect hm hn hc hs he x t] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hgt.le),neg_neg]
    convert! h using 1
    congr 2
    ring

end
end «2610.05164v2».LocalObstruction
