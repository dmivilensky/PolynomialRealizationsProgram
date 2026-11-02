import krylov.Reference.CGDirectionCoordinates
import krylov.Reference.CanonicalGradient
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true canonical relative-curvature coordinate.
Use: identify the actual frozen physical informed curvature coefficient
with the source's unit-CG canonical diagonal, without a scale assumption.
Source: actual primal/dual root pairing, true CG direction scale and
genuine active-step positivity and normalized-step unit norm.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual physical curvature quotient in an active CG direction
is exactly the genuine unit-CG canonical diagonal of the same real change.
Use: the actual informed last-curvature jet has the original source form.
Article: main_krylov, thm:local(a), exact normalized curvature dictionary.
Proof: true root pairing changes numerator and denominator to canonical
coordinates. The actual direction root image is its nonzero CG scale
times the true unit step; its squared scale cancels in the quotient. -/
theorem canonicalCG_curvature_quotient
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) (hi : i<referenceAtomCount base hb g)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    inner ℝ (CG.direction (cgOperator base) g i) (D (CG.direction (cgOperator base) g i))/
      inner ℝ (CG.direction (cgOperator base) g i)
        (cgOperator base (CG.direction (cgOperator base) g i))=
      inner ℝ (canonicalCGUnitStep base g i)
        ((cgOperator (metricRoot base)⁻¹*D*cgOperator (metricRoot base)⁻¹)
          (canonicalCGUnitStep base g i)) := by
  let h := canonicalCGUnitStep base g i
  let c := ‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i
  have hc : c≠0 := div_ne_zero
    (norm_ne_zero_iff.mpr (canonicalCGStep_ne_zero base hb g i
      (fun j hj => cg_nonstagnation base hb g j (hj.trans_lt hi))))
    (cgLength_pos base hb g i hi).ne'
  have hh : inner ℝ h h=1 := by
    rw [real_inner_self_eq_norm_sq]
    have ho := canonicalCGUnitStep_orthonormal base hb g (i+1)
      (fun j hj => cg_nonstagnation base hb g j (by omega))
    rw [show ‖h‖=1 from ho.norm_eq_one (Fin.last i),one_pow]
  have hnum : inner ℝ (CG.direction (cgOperator base) g i) (D (CG.direction (cgOperator base) g i))=
      c^2*inner ℝ h ((cgOperator (metricRoot base)⁻¹*D*cgOperator (metricRoot base)⁻¹) h) := by
    rw [canonicalCG_direction_pairing base hb g i hi,physicalCG_direction_scale base hb g i hi,
      map_smul,map_smul,real_inner_smul_right]
    change c*(c*inner ℝ h ((cgOperator (metricRoot base)⁻¹*D*cgOperator (metricRoot base)⁻¹) h))=_
    ring
  have hden : inner ℝ (CG.direction (cgOperator base) g i)
      (cgOperator base (CG.direction (cgOperator base) g i))=c^2 := by
    rw [canonical_search_pairing base hb,canonical_reference_action base hb]
    change inner ℝ (cgOperator (metricRoot base) (CG.direction (cgOperator base) g i))
      (cgOperator (metricRoot base) (CG.direction (cgOperator base) g i))=c^2
    rw [canonicalCG_direction_scale base hb g i hi]
    change inner ℝ (c • h) (c • h)=c^2
    rw [real_inner_smul_left,real_inner_smul_right,hh]
    ring
  rw [hnum,hden,mul_div_cancel_left₀ _ (pow_ne_zero 2 hc)]

end
end krylov.Reference
