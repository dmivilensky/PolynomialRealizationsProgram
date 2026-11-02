import krylov.Methods.CorrectionFreeQuadraticPrefix
import krylov.Envelope.CanonicalDriftDirection
import krylov.Envelope.CanonicalProbeOrthogonality

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), genuine exact correction-free invisible-prefix execution.
Use: identify the actual affine final output when every true earlier canonical probe defect vanishes.
Source: actual global quadratic-history consistency, genuine canonical-to-physical direction actions and exact orthogonal-probe search algebra.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Vanishing canonical prefix probe defects and an orthogonal final defect force an exact actual affine correction-free gradient.
Use: Vanishing canonical prefix probe defects and an orthogonal final defect force an exact actual affine correction-free gradient.
Article: main_krylov, apB:lem:mu(d), genuine exact correction-free invisible-prefix execution.
Proof: Every actual earlier probe equals its true quadratic answer; the genuine complete prefix is fixed and the final exact-search response is affine. -/
theorem correctionFree_hidden_prefix_gradient
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) (hfree : Methods.CorrectionFree m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (hprefix : ∀ j<k,cgOperator (∑ l∈Finset.range j,E l) (canonicalCGUnitStep base g j)=0)
    (horth : inner ℝ (canonicalCGUnitStep base g k)
      (cgOperator (∑ l∈Finset.range k,E l) (canonicalCGUnitStep base g k))=0)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    probedGradient m (canonicalFCPath base E t) B g (k+1)=
      CG.gradient (cgOperator base) g (k+1)+t • cumulativeDrift base E k (referenceStep (cgOperator base) g k) := by
  -- Each zero canonical intermediate action makes the genuine physical oracle answer exactly quadratic for every parameter.
  have hprobe (j : ℕ) (hj : j<k) :
      canonicalFCPath base E t j (CG.direction (cgOperator base) g j)=
        cgOperator base (CG.direction (cgOperator base) g j) := by
    have hz := canonical_drift_direction_zero base hb g j (hj.trans hk)
      (∑ l∈Finset.range j,E l) (hprefix j hj)
    change cgOperator base (CG.direction (cgOperator base) g j)+
      t • cumulativeDrift base E j (CG.direction (cgOperator base) g j)=_
    rw [show cumulativeDrift base E j (CG.direction (cgOperator base) g j)=0 from hz,smul_zero,add_zero]
  -- The newest defect has no true curvature component, so the actual final search has an exact affine response.
  have ho : inner ℝ (CG.direction (cgOperator base) g k)
      (t • cumulativeDrift base E k (CG.direction (cgOperator base) g k))=0 := by
    rw [real_inner_smul_right]
    have hz := canonical_probe_defect_orthogonal base hb g k hk (∑ l∈Finset.range k,E l) horth
    change t*inner ℝ (CG.direction (cgOperator base) g k)
      (cgOperator (metricRoot base*(∑ l∈Finset.range k,E l)*metricRoot base)
        (CG.direction (cgOperator base) g k))=0
    rw [hz,mul_zero]
  have he := correctionFree_gradient_quadratic_prefix m hm hfree (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k
    (canonicalFCPath base E t) B hprobe
    (t • cumulativeDrift base E k (CG.direction (cgOperator base) g k)) rfl ho
  rw [he]
  simp only [referenceStep,map_smul,smul_smul,mul_comm]
end
end krylov.Envelope
