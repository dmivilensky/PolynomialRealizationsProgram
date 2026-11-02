import krylov.Reference.CGDirectionCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine incoming canonical drift coefficient.
Use: transform true physical final-launch rows to the original normalized
CG step frame, preserving each actual unmeasured operator difference.
Source: actual positive-root CG direction coordinates and real line scales.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual physical last-direction drift pairing has exactly the
source canonical unit-coordinate and true last-step norm coefficient.
Use: incoming old rows retain their original physical perturbations and
genuine positive reference normalization when moving to canonical space.
Article: main_krylov, thm:local(a), true canonical incoming drift action.
Proof: actual primal/dual pairing gives the genuine old unit coordinate.
The true inverse-root last direction scales by its real step length over
line length; the current real trial-reference length cancels that last
denominator on its independently proved active positive domain. -/
theorem canonicalCG_drift_pairing
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i k : ℕ)
    (hi : i<referenceAtomCount base hb g) (hk : k<referenceAtomCount base hb g)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    CG.length (cgOperator base) g k*
      inner ℝ (CG.direction (cgOperator base) g i) (D (CG.direction (cgOperator base) g k))=
      (‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i)*‖canonicalCGStep base g k‖*
        inner ℝ (canonicalCGUnitStep base g i)
          ((cgOperator (metricRoot base)⁻¹*D*cgOperator (metricRoot base)⁻¹) (canonicalCGUnitStep base g k)) := by
  rw [canonicalCG_direction_pairing base hb g i hi,
    physicalCG_direction_scale base hb g k hk,map_smul,map_smul,real_inner_smul_right]
  let a := inner ℝ (canonicalCGUnitStep base g i)
    ((cgOperator (metricRoot base)⁻¹*D*cgOperator (metricRoot base)⁻¹) (canonicalCGUnitStep base g k))
  let ci := ‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i
  let sigma := ‖canonicalCGStep base g k‖
  let alpha := CG.length (cgOperator base) g k
  have halpha : alpha≠0 := (cgLength_pos base hb g k hk).ne'
  have hcancel : alpha*(sigma/alpha)=sigma := by rw [mul_comm,div_mul_cancel₀ _ halpha]
  change alpha*(ci*((sigma/alpha)*a))=ci*sigma*a
  calc
    _ = ci*(alpha*(sigma/alpha))*a := by ring
    _ = _ := by rw [hcancel]

end
end krylov.Reference
