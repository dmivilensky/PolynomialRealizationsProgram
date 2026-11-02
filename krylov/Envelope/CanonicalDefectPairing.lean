import krylov.Envelope.ZeroOperatorPairJet
import krylov.Envelope.CanonicalInjectionPairing

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), genuine canonical old-step defect pairing.
Use: convert true physical CG step/matrix-mismatch pairings into the
actual normalized canonical step and genuine square-root energy coordinates.
Source: true metric-root symmetry, actual physical congruence and the
proved genuine canonical CG step energy normalization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical reference-step defect pairing equals precisely the true two square-root energies times its genuine canonical unit-step matrix pairing.
Use: The actual physical reference-step defect pairing equals precisely the true two square-root energies times its genuine canonical unit-step matrix pairing.
Article: main_krylov, apB:lem:mu(d), genuine canonical old-step defect pairing.
Proof: Move the real symmetric positive metric root to the actual tested step, distribute the genuine matrix/operator congruence and normalize both true canonical steps. -/
theorem canonical_step_defect_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (D : Matrix (Fin n) (Fin n) ℝ) (i k : ℕ) :
    inner ℝ (referenceStep (cgOperator base) g i)
      (cgOperator (metricRoot base*D*metricRoot base) (referenceStep (cgOperator base) g k))=
    Real.sqrt (cgEnergy base g i)*Real.sqrt (cgEnergy base g k)*
      inner ℝ (canonicalCGUnitStep base g i) (cgOperator D (canonicalCGUnitStep base g k)) := by
  -- Reuse the proved genuine metric drift pairing, then normalize the actual canonical CG steps.
  have he := metric_drift_pairing base D (referenceStep (cgOperator base) g i) (referenceStep (cgOperator base) g k)
  change inner ℝ (referenceStep (cgOperator base) g i)
    (cgOperator (metricRoot base*D*metricRoot base) (referenceStep (cgOperator base) g k))=
      inner ℝ (cgOperator (metricRoot base) (referenceStep (cgOperator base) g i))
        (cgOperator D (cgOperator (metricRoot base) (referenceStep (cgOperator base) g k))) at he
  rw [he]
  have hs (j : ℕ) : cgOperator (metricRoot base) (referenceStep (cgOperator base) g j)=
      Real.sqrt (cgEnergy base g j) • canonicalCGUnitStep base g j := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  rw [hs i,hs k,map_smul,real_inner_smul_left,real_inner_smul_right]
  ring
end
end krylov.Envelope
