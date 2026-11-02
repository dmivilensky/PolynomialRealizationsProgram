import krylov.Envelope.TargetedGradientRegularity
import krylov.Envelope.ScenarioCoordinates
import krylov.Envelope.ScenarioVariation

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual targeted output on finite source scenarios.
Use: derive genuine joint C-two dependence of the real reference-targeted output on every true finite increment and correction scenario.
Source: actual source primitive operator coordinates, genuine active CG nonstagnation and the proved real target-method output calculus.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuinely executed targeted final gradient is C-two in the full actual finite canonical source scenario.
Use: The genuinely executed targeted final gradient is C-two in the full actual finite canonical source scenario.
Article: main_krylov, apB:prop:consist, actual targeted output on finite source scenarios.
Proof: Use true smooth finite source operators and derive all actual target-output inverse and curvature domains from the genuine active reference. -/
theorem targeted_scenarioGradient_regular (target : EuclideanSpace ℝ (Fin n))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) :
    ContDiffAt ℝ 2 (scenarioGradient (targetedFinalMethod (k+1) target) base g (k+1)) 0 := by
  exact targeted_gradient_regular target (scenarioProbe base) (scenarioCorrection base) g 0 k
    (fun i _ => (scenarioPrimitive_regular base hb i 2).1)
    (fun i _ => (scenarioPrimitive_regular base hb i 2).2)
    (cgOperator base) (scenarioProbe_zero base) (scenarioCorrection_zero base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))
end
end krylov.Envelope
