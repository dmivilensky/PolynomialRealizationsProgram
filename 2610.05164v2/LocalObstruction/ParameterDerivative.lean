import «2610.05164v2».LocalObstruction.MixedPartial

/-!
Article: 2610.05164v2, Theorem 6.1.
C1 regularity of the actual scale derivative in a C2 parameter family.
Use: `«2610.05164v2».LocalObstruction.parameter_derivative_c1` feeds
`«2610.05164v2».LocalObstruction.observationS_finite_joint_c1` (observation S finite joint c1).
Proof chain: `«2610.05164v2».LocalObstruction.observationS_finite_joint_c1` — 2610.05164v2, Theorem
6.1; No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 /--
Exact identity `deriv (fun t : ℝ => F (p.1,t)) p.2=fderiv ℝ F p (0,1)`.

Use: `«2610.05164v2».LocalObstruction.parameter_derivative_c1` uses this identity to establish
smoothness to the stated order: `ContDiffAt ℝ 1 (fun z : E × ℝ => deriv (fun t : ℝ => F
(z.1,t)) z.2) p`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationS_finite_joint_c1`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem parameter_derivative_eq {F : E × ℝ → ℝ} {p : E × ℝ}
    (hF : DifferentiableAt ℝ F p) :
    deriv (fun t : ℝ => F (p.1,t)) p.2=fderiv ℝ F p (0,1) := by
  have ht := hF.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have ht' : HasDerivAt (fun t : ℝ => F (p.1,t)) (fderiv ℝ F p (0,1)) p.2 := by
    convert! ht using 1
  exact ht'.deriv

 /--
Smoothness to the stated order: `ContDiffAt ℝ 1 (fun z : E × ℝ => deriv (fun t : ℝ => F
(z.1,t)) z.2) p`.

Use: `«2610.05164v2».LocalObstruction.observationS_finite_joint_c1` uses this identity to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS
(perturb m v p.1) p.2) (0,s)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationS_finite_joint_c1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem parameter_derivative_c1 {F : E × ℝ → ℝ} {p : E × ℝ}
    (hF : ContDiffAt ℝ 2 F p) :
    ContDiffAt ℝ 1 (fun z : E × ℝ => deriv (fun t : ℝ => F (z.1,t)) z.2) p := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hD := hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)
  have hEval : ContDiffAt ℝ 1 (fun z : E × ℝ => fderiv ℝ F z (0,1)) p :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0,1):E × ℝ)).contDiff.contDiffAt).comp p hD
  apply hEval.congr_of_eventuallyEq
  filter_upwards [hF.eventually (by norm_num : (2:ℕ∞ω)≠∞)] with z hz
  exact parameter_derivative_eq (hz.differentiableAt (by norm_num : (2:ℕ∞ω)≠0))

end
end «2610.05164v2».LocalObstruction
