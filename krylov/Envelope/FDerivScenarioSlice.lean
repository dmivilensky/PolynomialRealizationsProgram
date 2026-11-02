import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, actual reference-preserving scenario derivatives.
Use: identify the genuine joint reference/scenario derivative along a real
scenario direction with the actual fixed-reference scenario derivative.
Source: mathlib Frechet product and chain rules, applied to the true affine scenario slice.
-/

namespace krylov.Envelope
noncomputable section
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The true joint Frechet derivative in a reference-preserving scenario direction equals the genuine fixed-reference slice derivative.
Use: The true joint Frechet derivative in a reference-preserving scenario direction equals the genuine fixed-reference slice derivative.
Article: main_krylov, thm:E and s3:cor:qn, actual reference-preserving scenario derivatives.
Proof: The actual affine slice has the real product-inclusion derivative; apply the genuine Frechet chain rule and evaluate the resulting actual continuous linear maps. -/
theorem fderiv_scenario_slice (F : X × Y → Z) (x : X)
    (hF : DifferentiableAt ℝ F (x,0)) (v : Y) :
    fderiv ℝ F (x,0) (0,v)=fderiv ℝ (fun y => F (x,y)) 0 v := by
  have hs : HasFDerivAt (fun y : Y => (x,y)) (ContinuousLinearMap.inr ℝ X Y) 0 := by
    simpa only [ContinuousLinearMap.inr,id_eq] using (hasFDerivAt_const x (0 : Y)).prodMk (hasFDerivAt_id (0 : Y))
  have hc := (hF.hasFDerivAt.comp 0 hs).fderiv
  exact (congrArg (fun L => L v) hc).symm
end
end krylov.Envelope
