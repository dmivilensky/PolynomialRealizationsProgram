import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Banach

/-!
Article: 2610.05164v2, Theorem 6.1.
A reusable derivative of a Banach-space inverse applied to a fixed vector.
Use: `«2610.05164v2».LocalObstruction.inverse_affine_derivative` feeds
`«2610.05164v2».LocalObstruction.signedJost_scale_derivative` (signed Jost scale derivative).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => Ring.inverse (A+ε • B) w)
(-(Ring.inverse A (B (Ring.inverse A w)))) 0`.

Use: `«2610.05164v2».LocalObstruction.signedJost_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
signedJost (hm.add (hv.smul ε)) s) (signedJostVariation hm hv s) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem inverse_affine_derivative (A B : E →L[ℝ] E) (hu : IsUnit A) (w : E) :
    HasDerivAt (fun ε : ℝ => Ring.inverse (A+ε • B) w)
      (-(Ring.inverse A (B (Ring.inverse A w)))) 0 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hp : HasDerivAt (fun ε : ℝ => A+ε • B) B 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const B).const_add A
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := E →L[ℝ] E) hu.unit
  rw [IsUnit.unit_spec] at hi
  have hpoint : A+(0:ℝ) • B=A := by simp
  have hi' := hi
  conv at hi' => arg 3;rw [← hpoint]
  have hR := hi'.comp_hasDerivAt (0:ℝ) hp
  have hd := ((ContinuousLinearMap.apply ℝ E w).hasFDerivAt).comp_hasDerivAt (0:ℝ) hR
  convert! hd using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    Ring.inverse_of_isUnit hu]
  rfl

end
end «2610.05164v2».LocalObstruction
