import jacobi.Jacobi.RegularPrimitiveBounds
import jacobi.Jacobi.ScaledPhase

/-!
Article: jacobi, Proposition B.1.
The true regular potential, its ordinary derivative and its exact
primitive are rescaled at the original Jacobi frequency. Their actual
ordinary derivatives and uniform positive-interval bounds discharge all
potential-data inputs of the phase-averaging theorem.
Use: the literal perturbation in the genuine finite ordinary phase equation.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual small scaled regular Jacobi potential.
Use: the literal perturbation in the genuine finite ordinary phase equation.
Article: jacobi, Proposition B.1.
-/
def scaledRemainder (a b N x : ℝ) : ℝ := regularPotential a b (x/N)/N^2

/-- The actual ordinary derivative of the small scaled potential.
Use: controls the true derivative remainder in uniform finite phase averaging.
Article: jacobi, Proposition B.1.
-/
def scaledRemainderSlope (a b N x : ℝ) : ℝ := deriv (regularPotential a b) (x/N)/N^3

/-- The true scaled primitive of the original small phase perturbation.
Use: its half is exactly the averaged source correction in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
-/
def scaledPrimitive (a b N x : ℝ) : ℝ := regularPrimitive a b (x/N)/N

/-- The literal scaled potential has precisely the actual displayed ordinary derivative.
Use: discharges the C1 perturbation input of the true finite phase-averaging theorem.
Article: jacobi, Proposition B.1.
Proof: differentiate the true analytic potential and compose with x/N, then divide by N^2. -/
theorem scaledRemainder_hasDerivAt (a b : ℝ) {N x : ℝ}
    (hx : x/N∈Icc 0 (3*Real.pi/4)) :
    HasDerivAt (scaledRemainder a b N) (scaledRemainderSlope a b N x) x := by
  have hr := (regularPotential_analytic (t := x/N) a b ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_pos]⟩).1.differentiableAt.hasDerivAt
  convert ((hr.comp x ((hasDerivAt_id x).div_const N)).div_const (N^2)) using 1
  · rfl
  · dsimp [scaledRemainderSlope]
    ring

/-- The literal scaled primitive has exactly the original scaled potential as its ordinary derivative.
Use: identifies the true average-phase correction with the printed regular primitive, without an assumed integral identity.
Article: jacobi, Proposition B.1.
Proof: compose the actual original derivative R'=r with x/N and divide by N. -/
theorem scaledPrimitive_hasDerivAt (a b : ℝ) {N x : ℝ}
    (hx : x/N∈Icc 0 (3*Real.pi/4)) :
    HasDerivAt (scaledPrimitive a b N) (scaledRemainder a b N x) x := by
  convert (((regularPrimitive_derivative a b hx).comp x ((hasDerivAt_id x).div_const N)).div_const N) using 1
  · rfl
  · dsimp [scaledRemainder]
    ring

end
end jacobi.Jacobi
