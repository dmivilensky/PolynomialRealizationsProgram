import krylov.Convergence.VirtualReferenceMidpoints
import krylov.Convergence.EvaluatedReferenceMidpoints

/-!
Article: main_krylov, thm:V and prop:EL, literal relative trial errors.
Use: identify the actual missed physical CG component with the source's
relative trial error times the true canonical step, using its proved
positive line length before dividing.
Source: genuine CG energy and exact nonzero line normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual missed line component equals the printed relative error
 times the true canonical step. Article: thm:V and prop:EL. -/
theorem canonical_relative_trial_miss
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : E)
    (i : ℕ) (hi : i<referenceAtomCount base hb g) (τ : ℝ) :
    cgOperator (metricRoot base) ((CG.length (cgOperator base) g i-τ) • CG.direction (cgOperator base) g i)=
      (1-τ/CG.length (cgOperator base) g i) • canonicalCGStep base g i := by
  have hα := (cgLength_pos base hb g i hi).ne'
  change cgOperator (metricRoot base) ((CG.length (cgOperator base) g i-τ) • CG.direction (cgOperator base) g i)=
    (1-τ/CG.length (cgOperator base) g i) •
      cgOperator (metricRoot base) (CG.length (cgOperator base) g i • CG.direction (cgOperator base) g i)
  rw [map_smul,map_smul,smul_smul]
  congr 1
  field_simp

end
end krylov.Convergence
