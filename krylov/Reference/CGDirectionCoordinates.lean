import krylov.Reference.EnergyPositive
import krylov.Reference.CanonicalGradient
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual CG direction coordinate normalization.
Use: transfer genuine native physical incoming rows to the true canonical
orthonormal CG coordinates with their exact positive step/line scales.
Source: actual CG nonstagnation, genuine positive-root cancellation,
real primal/dual pairing and zero-safe normalization of actual CG steps.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual root image of an active CG direction has exactly its
true positive canonical step-length divided by line-length scale.
Use: no arbitrary direction normalization enters incoming coefficients.
Article: main_krylov, thm:local(a), genuine reference direction scale.
Proof: the active canonical step is nonzero. The actual canonical
direction identity and genuine norm-times-normalization identity give
its precise real scale; scalar commutativity identifies the quotient. -/
theorem canonicalCG_direction_scale
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) (hi : i<referenceAtomCount base hb g) :
    cgOperator (metricRoot base) (CG.direction (cgOperator base) g i)=
      (‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i) • canonicalCGUnitStep base g i := by
  have hn := canonicalCGStep_ne_zero base hb g i (fun j hj => cg_nonstagnation base hb g j (hj.trans_lt hi))
  have he := canonicalCG_direction base g i hn
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hs,smul_smul] at he
  have he' : cgOperator (metricRoot base) (CG.direction (cgOperator base) g i)=
      ((CG.length (cgOperator base) g i)⁻¹*‖canonicalCGStep base g i‖) • canonicalCGUnitStep base g i := he
  simpa only [div_eq_mul_inv,mul_comm] using he'

/-- The actual active physical CG direction is its true canonical unit
direction transported by the real inverse positive root, with exact scale.
Use: the current physical drift action retains its genuine canonical form.
Article: main_krylov, thm:local(a), real inverse-root direction coordinates.
Proof: apply the genuine inverse root to the true root-image identity
and cancel on the derived positive-root inverse domain. -/
theorem physicalCG_direction_scale
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) (hi : i<referenceAtomCount base hb g) :
    CG.direction (cgOperator base) g i=
      (‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i) •
        cgOperator (metricRoot base)⁻¹ (canonicalCGUnitStep base g i) := by
  have he := congrArg (cgOperator (metricRoot base)⁻¹) (canonicalCG_direction_scale base hb g i hi)
  rw [map_smul] at he
  have hcancel (v : EuclideanSpace ℝ (Fin n)) : cgOperator (metricRoot base)⁻¹ (cgOperator (metricRoot base) v)=v := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,
      Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
  rw [hcancel] at he
  exact he

/-- Pairing an actual active physical CG direction with a real gradient
gives its exact true canonical unit-coordinate times the real step scale.
Use: normalize actual native incoming-gradient row estimates faithfully.
Article: main_krylov, thm:local(a), exact incoming row normalization.
Proof: genuine primal/dual search pairing moves to the actual root/inverse
root coordinates; substitute the true canonical direction scale. -/
theorem canonicalCG_direction_pairing
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) (hi : i<referenceAtomCount base hb g)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (CG.direction (cgOperator base) g i) v=
      (‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i)*
        inner ℝ (canonicalCGUnitStep base g i) (cgOperator (metricRoot base)⁻¹ v) := by
  rw [canonical_search_pairing base hb]
  change inner ℝ (cgOperator (metricRoot base) (CG.direction (cgOperator base) g i))
    (cgOperator (metricRoot base)⁻¹ v)=_
  rw [canonicalCG_direction_scale base hb g i hi,real_inner_smul_left]

end
end krylov.Reference
