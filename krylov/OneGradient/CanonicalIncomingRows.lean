import krylov.Reference.CanonicalDriftPairing
import Mathlib.Analysis.Asymptotics.Ring
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), exact canonical incoming-row transfer.
Use: normalize genuine physical native incoming rows with the actual
reference CG direction scales, preserving the full perturbation norm.
Source: real canonical drift pairing, genuine active step/line positivity
and actual CG energy; only fixed nonzero reference factors are cancelled.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X]

/-- A genuine old physical native incoming-row bound gives its exact
canonical unit-row bound, cancelling only a true fixed nonzero reference
basis scale. Every actual operator increment is retained.
Use: both S and D real old columns normalize to the identical source row.
Article: main_krylov, thm:local(a), true old-row canonical normalization.
Proof: the actual physical direction pairing and last-direction drift
pairing give the exact common scalar factor. Active nonstagnation and
positive actual CG lengths make that factor nonzero. Multiply the actual
row remainder by its fixed inverse; no perturbation-dependent divisor appears. -/
theorem canonical_incoming_old_row
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i k : ℕ)
    (hi : i<referenceAtomCount base hb g) (hk : k<referenceAtomCount base hb g)
    (c : ℝ) (hc : c≠0) (G : X → EuclideanSpace ℝ (Fin n))
    (D : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrow : (fun z => inner ℝ (c • CG.direction (cgOperator base) g i) (G z)-
      CG.length (cgOperator base) g k*inner ℝ (c • CG.direction (cgOperator base) g i)
        (D z (CG.direction (cgOperator base) g k))) =O[𝓝 0] (fun z => ‖z‖^2)) :
    (fun z => inner ℝ (canonicalCGUnitStep base g i) (cgOperator (metricRoot base)⁻¹ (G z))-
      ‖canonicalCGStep base g k‖*inner ℝ (canonicalCGUnitStep base g i)
        ((cgOperator (metricRoot base)⁻¹*D z*cgOperator (metricRoot base)⁻¹) (canonicalCGUnitStep base g k)))
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let a := ‖canonicalCGStep base g i‖/CG.length (cgOperator base) g i
  let t := c*a
  have hs : canonicalCGStep base g i≠0 := canonicalCGStep_ne_zero base hb g i
    (fun j hj => cg_nonstagnation base hb g j (hj.trans_lt hi))
  have ht : t≠0 := mul_ne_zero hc (div_ne_zero (norm_ne_zero_iff.mpr hs) (cgLength_pos base hb g i hi).ne')
  have heq (z : X) : inner ℝ (c • CG.direction (cgOperator base) g i) (G z)-
      CG.length (cgOperator base) g k*inner ℝ (c • CG.direction (cgOperator base) g i)
        (D z (CG.direction (cgOperator base) g k))=
      t*(inner ℝ (canonicalCGUnitStep base g i) (cgOperator (metricRoot base)⁻¹ (G z))-
        ‖canonicalCGStep base g k‖*inner ℝ (canonicalCGUnitStep base g i)
          ((cgOperator (metricRoot base)⁻¹*D z*cgOperator (metricRoot base)⁻¹) (canonicalCGUnitStep base g k))) := by
    rw [real_inner_smul_left,real_inner_smul_left]
    calc
      _ = c*(inner ℝ (CG.direction (cgOperator base) g i) (G z)-
          CG.length (cgOperator base) g k*inner ℝ (CG.direction (cgOperator base) g i)
            (D z (CG.direction (cgOperator base) g k))) := by ring
      _ = _ := by
        rw [canonicalCG_direction_pairing base hb g i hi,canonicalCG_drift_pairing base hb g i k hi hk]
        dsimp only [t,a]
        ring
  apply (hrow.const_mul_left t⁻¹).congr_left
  intro z
  rw [heq,← mul_assoc,inv_mul_cancel₀ ht,one_mul]

/-- The genuine physical final-direction row normalizes to the actual
canonical final-unit row with the true last-step length coefficient.
Use: the unmeasured last pivot keeps the exact original energy normalization.
Article: main_krylov, thm:local(a), true last-row canonical normalization.
Proof: actual positive step and line lengths give a nonzero direction
scale. True CG energy identifies the residual-norm coefficient as that
scale times the last-step norm. Normalize the actual physical remainder
by this fixed genuine scale. -/
theorem canonical_incoming_last_row
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (G : X → EuclideanSpace ℝ (Fin n)) (eps : X → ℝ)
    (hrow : (fun z => inner ℝ (CG.direction (cgOperator base) g k) (G z)+
      eps z*‖CG.gradient (cgOperator base) g k‖^2) =O[𝓝 0] (fun z => ‖z‖^2)) :
    (fun z => inner ℝ (canonicalCGUnitStep base g k) (cgOperator (metricRoot base)⁻¹ (G z))+
      ‖canonicalCGStep base g k‖*eps z) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let sigma := ‖canonicalCGStep base g k‖
  let alpha := CG.length (cgOperator base) g k
  let t := sigma/alpha
  have hs : canonicalCGStep base g k≠0 := canonicalCGStep_ne_zero base hb g k
    (fun j hj => cg_nonstagnation base hb g j (hj.trans_lt hk))
  have halpha : alpha≠0 := (cgLength_pos base hb g k hk).ne'
  have ht : t≠0 := div_ne_zero (norm_ne_zero_iff.mpr hs) halpha
  have henergy : sigma^2=alpha*‖CG.gradient (cgOperator base) g k‖^2 := by
    have he := cgEnergy_eq_length_norm base hb g hk
    rw [cgEnergy_eq_norm_sq base hb] at he
    exact he
  have hcoef : ‖CG.gradient (cgOperator base) g k‖^2=t*sigma := by
    dsimp only [t]
    apply (mul_left_cancel₀ halpha)
    have he : alpha*(sigma/alpha*sigma)=sigma^2 := by field_simp
    nlinarith [henergy]
  have heq (z : X) : inner ℝ (CG.direction (cgOperator base) g k) (G z)+
      eps z*‖CG.gradient (cgOperator base) g k‖^2=
      t*(inner ℝ (canonicalCGUnitStep base g k) (cgOperator (metricRoot base)⁻¹ (G z))+sigma*eps z) := by
    rw [canonicalCG_direction_pairing base hb g k hk,hcoef]
    change t*inner ℝ (canonicalCGUnitStep base g k) (cgOperator (metricRoot base)⁻¹ (G z))+eps z*(t*sigma)=_
    ring
  apply (hrow.const_mul_left t⁻¹).congr_left
  intro z
  rw [heq,← mul_assoc,inv_mul_cancel₀ ht,one_mul]

end
end krylov.OneGradient
