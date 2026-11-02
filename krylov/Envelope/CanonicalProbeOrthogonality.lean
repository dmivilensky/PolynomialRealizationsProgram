import krylov.Envelope.FinalErrorImage
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, genuine canonical-to-physical final-probe orthogonality.
Use: make the actual final search curvature invariant under a true
canonical cross-plane newest increment.
Source: existing genuine metric drift pairing and the proved actual
active CG direction energy normalization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- A true canonical last-step increment with zero genuine self-pairing has actual zero physical CG direction curvature defect.
Use: A true canonical last-step increment with zero genuine self-pairing has actual zero physical CG direction curvature defect.
Article: main_krylov, s3:thm:cf, genuine canonical-to-physical final-probe orthogonality.
Proof: Use genuine root-congruence pairing and the real active CG direction normalization to retain only the actual zero canonical self-pairing. -/
theorem canonical_probe_defect_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : inner ℝ (canonicalCGUnitStep base g k) (cgOperator D (canonicalCGUnitStep base g k))=0) :
    inner ℝ (CG.direction (cgOperator base) g k)
      (cgOperator (metricRoot base*D*metricRoot base) (CG.direction (cgOperator base) g k))=0 := by
  have he := metric_drift_pairing base D (CG.direction (cgOperator base) g k) (CG.direction (cgOperator base) g k)
  change inner ℝ (CG.direction (cgOperator base) g k)
    (cgOperator (metricRoot base*D*metricRoot base) (CG.direction (cgOperator base) g k))=
      inner ℝ (cgOperator (metricRoot base) (CG.direction (cgOperator base) g k))
        (cgOperator D (cgOperator (metricRoot base) (CG.direction (cgOperator base) g k))) at he
  rw [he,canonicalCG_direction_energy base hb g k hk]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right,hD,mul_zero]
end
end krylov.Envelope
