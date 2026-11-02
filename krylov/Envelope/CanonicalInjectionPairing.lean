import krylov.Envelope.CanonicalPolynomialFlags
import krylov.Envelope.TiltLastIncrement

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), genuine canonical frozen-injection tilt pairings.
Use: identify each actual physical reference-gradient frozen injection
pairing with the true canonical polynomial tilt vector and genuine
canonical increment action on an actual computed CG step.
Source: actual primitive canonical segment derivatives, genuine symmetric
polynomial actions, real metric pairing and true root/reference commutation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual propagated physical injection pairing equals its genuine canonical polynomial-gradient and source-increment pairing on the real computed step.
Use: Every actual propagated physical injection pairing equals its genuine canonical polynomial-gradient and source-increment pairing on the real computed step.
Article: main_krylov, apB:lem:mu(b), genuine canonical frozen-injection tilt pairings.
Proof: Differentiate the true canonical segment, move the actual symmetric polynomial across the genuine physical inner product, apply true metric congruence and commute the actual positive root through the real polynomial. -/
theorem canonical_injection_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N j : ℕ) (p : ℝ[X]) :
    inner ℝ (CG.gradient (cgOperator base) g N)
      ((aeval (cgOperator base).toLinearMap p) (referenceInjection (cgOperator base) g (canonicalFCPath base E) (j+1)))=
    inner ℝ ((aeval (cgOperator base).toLinearMap p) (cgOperator base (cgCanonicalError base g N)))
      (cgOperator (∑ l∈Finset.range j,E l) (canonicalCGStep base g j)) := by
  -- Differentiate the genuine canonical source segment before transporting its actual physical frozen pairing through the true metric root.
  rw [referenceInjection_canonical]
  have hs := polynomial_action_symmetric (cgOperator base).toLinearMap (cgOperator_positive base hb).1 p
  have hp := hs (CG.gradient (cgOperator base) g N)
    (cumulativeDrift base E j (referenceStep (cgOperator base) g j))
  change inner ℝ ((aeval (cgOperator base).toLinearMap p) (CG.gradient (cgOperator base) g N))
    (cumulativeDrift base E j (referenceStep (cgOperator base) g j))=
      inner ℝ (CG.gradient (cgOperator base) g N) ((aeval (cgOperator base).toLinearMap p)
        (cumulativeDrift base E j (referenceStep (cgOperator base) g j))) at hp
  rw [← hp]
  change inner ℝ ((aeval (cgOperator base).toLinearMap p) (CG.gradient (cgOperator base) g N))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base*(∑ l∈Finset.range j,E l)*metricRoot base)
      (referenceStep (cgOperator base) g j))=_
  rw [metric_drift_pairing]
  change inner ℝ (cgOperator (metricRoot base) ((aeval (cgOperator base).toLinearMap p)
    (CG.gradient (cgOperator base) g N))) (cgOperator (∑ l∈Finset.range j,E l) (canonicalCGStep base g j))=_
  rw [root_polynomial_action base hb p]
  have hd : cgOperator base (cgCanonicalError base g N)=cgOperator (metricRoot base) (CG.gradient (cgOperator base) g N) :=
    canonical_base_dual base hb _
  rw [hd]
end
end krylov.Envelope
