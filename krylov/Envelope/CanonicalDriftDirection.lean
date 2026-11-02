import krylov.Envelope.FinalErrorImage
import krylov.Envelope.CanonicalInjections

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual canonical direction drift action.
Use: convert canonical increment actions on genuine normalized CG steps into actual physical probe defects.
Source: real positive-root congruence and the proved genuine active CG direction energy normalization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A true physical drift on an active CG direction has the exact canonical unit-step normalization.
Use: A true physical drift on an active CG direction has the exact canonical unit-step normalization.
Article: main_krylov, apB:lem:mu(d), actual canonical direction drift action.
Proof: Distribute the genuine root congruence and substitute the actual direction-energy identity. -/
theorem canonical_drift_direction_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    cgOperator (metricRoot base*D*metricRoot base) (CG.direction (cgOperator base) g k)=
      (‖CG.gradient (cgOperator base) g k‖^2/Real.sqrt (cgEnergy base g k)) •
        cgOperator (metricRoot base) (cgOperator D (canonicalCGUnitStep base g k)) := by
  have he : cgOperator (metricRoot base*D*metricRoot base)=
      cgOperator (metricRoot base) ∘L cgOperator D ∘L cgOperator (metricRoot base) := by
    simp only [cgOperator,map_mul]
    rfl
  rw [he]
  change cgOperator (metricRoot base) (cgOperator D
    (cgOperator (metricRoot base) (CG.direction (cgOperator base) g k)))=_
  rw [canonicalCG_direction_energy base hb g k hk,map_smul,map_smul]

/-- A canonical increment annihilating the actual CG unit step has genuinely zero physical direction probe.
Use: A canonical increment annihilating the actual CG unit step has genuinely zero physical direction probe.
Article: main_krylov, apB:lem:mu(d), actual canonical direction drift action.
Proof: Use the exact normalized physical direction drift action. -/
theorem canonical_drift_direction_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : cgOperator D (canonicalCGUnitStep base g k)=0) :
    cgOperator (metricRoot base*D*metricRoot base) (CG.direction (cgOperator base) g k)=0 := by
  rw [canonical_drift_direction_action base hb g k hk D,hD,map_zero,smul_zero]
end
end krylov.Envelope
