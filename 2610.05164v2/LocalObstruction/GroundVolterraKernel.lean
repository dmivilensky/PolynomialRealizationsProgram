import «2610.05164v2».LocalObstruction.VolterraDuality
import «2610.05164v2».LocalObstruction.GroundTail

/-!
Article: 2610.05164v2, Theorem 6.1.
The free Green kernel becomes the causal Volterra kernel after removing its left exponential
asymptote.
Use: `«2610.05164v2».LocalObstruction.ground_left_exponential_bound` feeds
`«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` (ground Left Amplitude positive).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».HalfLine «2610.05164v2».GroundState «2610.05164v2».Sobolev «2610.05164v2».Continuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Exact identity `exp (-x)*exp (-|x-y|)-exp (-y)=-volterraKernel x y*exp (-y)`.

Use: `«2610.05164v2».LocalObstruction.groundLeft_equation` rewrites with this identity to
establish the precise assertion is `groundLeft G hM x-groundLeftAmplitude G= volterra
(-groundParameter hm hn) m (groundLeft G hM) x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem ground_volterra_kernel (x y : ℝ) :
    exp (-x)*exp (-|x-y|)-exp (-y)=-volterraKernel x y*exp (-y) := by
  -- Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hy : y<x
  · rw [abs_of_nonneg (sub_nonneg.mpr hy.le)]
    have he : exp (-x)*exp (-(x-y))=exp (-2*(x-y))*exp (-y) := by
      rw [← exp_add,← exp_add]
      congr 1
      ring
    rw [he]
    simp only [volterraKernel,indicator_of_mem (show y∈Iio x from hy)]
    ring
  · have hxy : x≤y := le_of_not_gt hy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    simp only [volterraKernel,indicator_of_notMem (show y∉Iio x from hy),neg_zero,zero_mul]
    rw [← exp_add,show -x+ -(-(x-y))= -y by ring,sub_self]

 /--
The stated quantitative bound `exp (-x)*exp (-|x-y|)≤exp (-y)`.

Use: `«2610.05164v2».LocalObstruction.ground_left_exponential_bound` uses this bound to
establish the stated quantitative bound `exp (-x)*H1.rep G.u x≤∫ y,exp (-y)*groundSource G y`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem ground_left_kernel_bound (x y : ℝ) : exp (-x)*exp (-|x-y|)≤exp (-y) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  linarith [le_abs_self (y-x),abs_sub_comm x y]

 /--
Defines `groundSource` of type `ℝ` by `groundParameter hm hn/2*m y*H1.rep G.u y`.

Use: `«2610.05164v2».LocalObstruction.groundSource_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (groundSource G)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def groundSource {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (y : ℝ) : ℝ := groundParameter hm hn/2*m y*H1.rep G.u y

 /--
Integrability of the displayed function: `Integrable (groundSource G)`.

Use: `«2610.05164v2».LocalObstruction.ground_left_exponential_bound` rewrites with this
integrability result to prove the bound `exp (-x)*H1.rep G.u x≤∫ y,exp
(-y)*groundSource G y`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundSource_integrable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) : Integrable (groundSource G) := by
  have hi := hm.mul_bdd (H1.continuous_rep G.u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => H1.evaluation_bound G.u y))
  convert! hi.const_mul (groundParameter hm hn/2) using 1
  funext y
  dsimp only [groundSource]
  ring

 /--
Integrability of the displayed function: `Integrable (fun y => exp (-y)*groundSource G y)`.

Use: `«2610.05164v2».LocalObstruction.ground_left_exponential_bound` uses this integrability
result to prove the bound `exp (-x)*H1.rep G.u x≤∫ y,exp
(-y)*groundSource G y`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundSource_weighted_integrable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    Integrable (fun y => exp (-y)*groundSource G y) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hi := hM.mul_bdd (H1.continuous_rep G.u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => H1.evaluation_bound G.u y))
  convert! hi.const_mul (groundParameter hm hn/2) using 1
  funext y
  dsimp only [groundSource]
  ring

 /--
The stated quantitative bound `exp (-x)*H1.rep G.u x≤∫ y,exp (-y)*groundSource G y`.

Use: `«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` uses this bound to
establish the stated quantitative bound `0<groundLeftAmplitude G`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.ground_source_rep`,
`«2610.05164v2».GroundState.convolution_rep`,
`«2610.05164v2».LocalObstruction.groundSource_integrable` with the arguments shown in the
proof.
-/
theorem ground_left_exponential_bound {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) (x : ℝ) :
    exp (-x)*H1.rep G.u x≤∫ y,exp (-y)*groundSource G y := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.ground_source_rep`,
  -- `«2610.05164v2».GroundState.convolution_rep`,
  -- `«2610.05164v2».LocalObstruction.groundSource_integrable` with the arguments shown in the
  -- proof.
  rw [ground_source_rep G x]
  change exp (-x)*H1.rep (convolution (groundSource G)) x≤_
  rw [convolution_rep (groundSource_integrable G),← integral_const_mul]
  apply integral_mono_ae ((convolution_kernel_integrable (groundSource_integrable G) x).const_mul _)
    (groundSource_weighted_integrable G hM)
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (ground_left_kernel_bound x y)
      (mul_nonneg (mul_nonneg (div_nonneg G.coupling_positive.le (by norm_num)) (hn y)) (G.positive y).le))

end
end «2610.05164v2».LocalObstruction
