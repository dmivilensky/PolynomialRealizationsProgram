import krylov.XR.LocalFloorSource

/-!
Article: main_krylov, prop:floor, fixed prior class upper bound.
Use: the literal computed ModelStep floor has exactly the printed fixed
constants ell = lambdaMin/(2*(2*(1-armijo)-eta0)) and Lambda = L.
The actual raw-data Radau estimate and all inverse domains are derived
from the primitive secant and gain conditions; both value flags apply.
Source: the proved uniform physical Radau completion specialized to L.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.Convergence krylov.Reference
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A fixed prior upper class bound gives the exact printed floor
constants, without replacing L by a running envelope. -/
theorem algorithmComputedCurvature_fixed_prior_floor_radius
    (P : Parameters) (hP : P.Valid n)
    (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (lambdaMin b L sigma : ℝ)
    (hmin : 0 < lambdaMin) (hband : lambdaMin ≤ b) (hb : 0 < b) (hmargin : b < L)
    (hsigma : 0 < sigma) (hsigma₁ : sigma ≤ 1)
    (hHlo : (base-lambdaMin • 1).PosSemidef) (hHhi : (b • 1-base).PosSemidef)
    (hpositive : ∀ v : EuclideanSpace ℝ (Fin n), lambdaMin*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hnorm : ‖cgOperator base‖ ≤ b) :
    ∃ radius > 0, ∀ (S : State (EuclideanSpace ℝ (Fin n))) (lower : ℝ),
      (algorithmModel P S).bounds = some (lower,L) →
      (∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0) →
      (∀ w : Fin (algorithmModel P S).pairs.length → ℝ,
        sigma^2*‖WithLp.toLp 2 w‖^2 ≤
          ‖combine (unitWindow (storedSteps (algorithmModel P S).pairs)) w‖^2) →
      (∀ i, ‖storedImages (algorithmModel P S).pairs i -
        cgOperator base (storedSteps (algorithmModel P S).pairs i)‖ ≤
          radius*‖storedSteps (algorithmModel P S).pairs i‖) →
      algorithmSelectedDirection P S ≠ 0 →
      let d := algorithmSelectedDirection P S
      (lambdaMin/(2*(2*(1-P.armijo)-P.adequacyMargin)))*‖d‖^2 ≤ algorithmComputedCurvature P S ∧
        algorithmComputedCurvature P S ≤ L*‖d‖^2 ∧
        inner ℝ (cgOperator base d) d ≤
          (2*(1-P.armijo)-P.adequacyMargin/2)*algorithmComputedCurvature P S := by
  obtain ⟨radius, hr, h⟩ := algorithmComputedCurvature_uniform_floor_radius P hP base hbase
    lambdaMin b L L sigma hmin hband hb hmargin hsigma hsigma₁ hHlo hHhi hpositive hnorm
  refine ⟨radius, hr, ?_⟩
  intro S lower hbounds hs hgain hy hd
  exact h S (lower,L) hbounds le_rfl le_rfl hs hgain hy hd

end
end krylov.XR
