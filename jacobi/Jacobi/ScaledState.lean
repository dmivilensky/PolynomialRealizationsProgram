import jacobi.Jacobi.RestoringState
import jacobi.Oscillation.Rescale

/-!
Article: jacobi, Proposition B.1.
The original finite Jacobi wave is genuinely rescaled by N. Its true
ordinary phase solves precisely the inverse-square Bessel phase equation
with the smooth bounded source perturbation r(x/N)/N^2.
Use: constructs the actual finite phase used in Proposition B.1, rather than a phase satisfying assumed comparison estimates.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set jacobi.Oscillation
set_option backward.isDefEq.respectTransparency false

/-- The true Bessel-scaled Jacobi restoring state, with all hypotheses inherited from the original finite polynomial.
Use: constructs the actual finite phase used in Proposition B.1, rather than a phase satisfying assumed comparison estimates.
Article: jacobi, Proposition B.1.
-/
def scaledState (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (hN : 0<frequency a b n) :=
  (restoringState a b ha hb n).rescale (frequency a b n) hN

/-- The scaled original potential is exactly its Bessel inverse-square coefficient plus the genuine small regular Jacobi remainder.
Use: every input to the uniform quantitative phase-perturbation theorem is the original finite Jacobi potential.
Article: jacobi, Proposition B.1.
Proof: substitute the actual unscaled potential, cancel the nonzero frequency, and collect the inverse-square terms. -/
theorem scaledState_potential {a b x : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (hN : 0<frequency a b n) (hx : 0<x) :
    (scaledState a b ha hb n hN).potential x=
      1+endpointCorrection a/x^2+regularPotential a b (x/frequency a b n)/(frequency a b n)^2 := by
  dsimp [scaledState,RestoringSolution.rescale,restoringState]
  field_simp [hN.ne',hx.ne']

end
end jacobi.Jacobi
