import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
Article: chebyshev2, Theorem 6.1.
The mixed derivative needed for H-prime is an instance of the proved symmetry of the second Frechet
derivative.
Use: `chebyshev2.LocalObstruction.mixed_partial_derivative` feeds
`chebyshev2.LocalObstruction.singleHPrime_density_derivative` (single HPrime density
derivative).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => fderiv ℝ F (ε,s) (0,1))
(deriv (fun t : ℝ => fderiv ℝ F (0,t) (1,0)) s) 0`.

Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (singleHPrime hm hv
s) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem mixed_partial_derivative {F : ℝ × ℝ → ℝ} {s : ℝ}
    (hF : ContDiffAt ℝ 2 F (0,s)) :
    HasDerivAt (fun ε : ℝ => fderiv ℝ F (ε,s) (0,1))
      (deriv (fun t : ℝ => fderiv ℝ F (0,t) (1,0)) s) 0 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hD : DifferentiableAt ℝ (fderiv ℝ F) (0,s) :=
    (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num : (1:ℕ∞ω)≠0)
  have hS := ((ContinuousLinearMap.apply ℝ ℝ ((0,1):ℝ × ℝ)).hasFDerivAt.comp
    (0,s) hD.hasFDerivAt).comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) s))
  have hV := ((ContinuousLinearMap.apply ℝ ℝ ((1,0):ℝ × ℝ)).hasFDerivAt.comp
    (0,s) hD.hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_const s (0:ℝ)).prodMk (hasDerivAt_id s))
  have hV' : HasDerivAt (fun t : ℝ => fderiv ℝ F (0,t) (1,0))
      (fderiv ℝ (fderiv ℝ F) (0,s) (0,1) (1,0)) s := by convert! hV using 1
  have hsym := hF.isSymmSndFDerivAt (by simp)
  rw [hV'.deriv]
  convert! hS using 1
  exact hsym (0,1) (1,0)

end
end chebyshev2.LocalObstruction
