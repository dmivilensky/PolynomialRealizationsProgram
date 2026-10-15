import «2610.05164v2».LocalObstruction.GreenKernel
import «2610.05164v2».Comparison.SymmetricObservation

/-!
Article: 2610.05164v2, Theorem 6.1.
Identify H's raw Jost Wronskian with the proved spectral transmission and express the actual Green
diagonal through causal filters.
Use: `«2610.05164v2».LocalObstruction.greenKernel_diagonal_jost` feeds
`«2610.05164v2».LocalObstruction.singleH_density_derivative` (single H density derivative).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set Real MeasureTheory «2610.05164v2».Filters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
  (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x, m (-x)=m x)

include hm hn hs he in
 /--
Exact identity `wronskian s m x=jostWronskian s m x`.

Use: `«2610.05164v2».LocalObstruction.greenKernel_diagonal` rewrites with this identity to
establish exact identity `greenKernel s m x x=1/(2+nonlinear s m x+nonlinear s m (-x))`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem wronskian_eq_jostWronskian (x : ℝ) :
    wronskian s m x=jostWronskian s m x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hmr : reflected m=m := funext he
  unfold wronskian jostFunctionSlope jostFunction jostWronskian
  rw [hmr]
  unfold nonlinear
  rw [exp_neg]
  field_simp [(exp_pos x).ne',(jost_positive hm hn hs x).ne',
    (jost_positive hm hn hs (-x)).ne']
  ring

include hm hn hc hs he in
 /--
Exact identity `wronskian s m x=2*transmission s m`.

Use: `«2610.05164v2».LocalObstruction.greenKernel_diagonal_jost` rewrites with this identity to
establish exact identity `greenKernel s m x x=jost s m x*jost s m (-x)/(2*transmission s m)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.wronskian_eq_jostWronskian`,
`«2610.05164v2».Comparison.jostWronskian_value` with the arguments shown in the proof.
-/
theorem wronskian_eq_transmission (x : ℝ) :
    wronskian s m x=2*transmission s m := by
  rw [wronskian_eq_jostWronskian hm hn hs he]
  exact «2610.05164v2».Comparison.jostWronskian_value hm hn hc hs x

include hm hn hc hs he in
 /--
Exact identity `greenKernel s m x x=1/(2+nonlinear s m x+nonlinear s m (-x))`.

Use: `«2610.05164v2».LocalObstruction.greenColumn_boundary_convolution` uses this identity to
establish exact identity `greenKernel s m x x+s/2*H1.rep (convolution (fun y => m y*greenKernel
s m x y)) x=1/2`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenKernel_diagonal (x : ℝ) :
    greenKernel s m x x=1/(2+nonlinear s m x+nonlinear s m (-x)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hmr : reflected m=m := funext he
  have hd : 2+nonlinear s m x+nonlinear s m (-x)≠0 :=
    ne_of_gt (by linarith [(nonlinear_bounds hm hn hs x).1,(nonlinear_bounds hm hn hs (-x)).1])
  unfold greenKernel
  rw [min_self,max_self,← wronskian_constant hm hn hc hs he x,
    wronskian_eq_jostWronskian hm hn hs he x]
  unfold jostWronskian jostFunction
  rw [hmr,exp_neg]
  field_simp [(exp_pos x).ne',(jost_positive hm hn hs x).ne',
    (jost_positive hm hn hs (-x)).ne',hd]

include hm hn hc hs he in
 /--
Exact identity `greenKernel s m x x=jost s m x*jost s m (-x)/(2*transmission s m)`.

Use: `«2610.05164v2».LocalObstruction.sine_green_diagonal_tail` rewrites with this identity to
establish the stated quantitative bound `(fun x => greenKernel s m x x-1/2-
(sineJostCoefficient s/(2*transmission s m))*exp (-2*x)) =o[atTop] n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem greenKernel_diagonal_jost (x : ℝ) :
    greenKernel s m x x=jost s m x*jost s m (-x)/(2*transmission s m) := by
  unfold greenKernel
  rw [min_self,max_self,wronskian_eq_transmission hm hn hc hs he]
  unfold jostFunction
  congr 1
  rw [exp_neg]
  field_simp

end
end «2610.05164v2».LocalObstruction
