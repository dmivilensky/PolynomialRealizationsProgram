import krylov.OneGradient.KnownBaseCentreGeometry
import krylov.Information.PhysicalRadius
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual centred-output coordinate dictionary.
Use: the genuine data-only method's returned gradient and centre inverse
are exactly the true normalized observed column and actual canonical solve.
Source: exact native final gradient, actual positive-root form transport,
true reference scale and genuine root/inverse cancellation.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine centring method's actual returned gradient is exactly
the true canonical increment column on the known last reference unit
direction, with the source's actual last-step normalization.
Use: observed centre coordinates have no O(omega²) measurement surrogate,
so the original singular corners require no centre continuity assumption.
Article: main_krylov, thm:local(c), exact observed canonical column.
Proof: actual calibrated queries give the exact physical last gradient.
The true canonical form dictionary moves its physical action to the real
normalized increment; genuine zero-safe step normalization gives its length. -/
theorem knownBaseCentre_observed_column (base C M : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : base.PosDef) (eta : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (hc : referenceAtomCount base hb g=2) (hrel : relativeOperator base (C-base)=eta • M) :
    let H := oneGradientRun (knownBaseCentredMethod base eta) (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    cgOperator (metricRoot base)⁻¹ H.gradient=
      (eta*‖canonicalCGStep base g 1‖) • cgOperator M (canonicalCGUnitStep base g 1) := by
  let H := oneGradientRun (knownBaseCentredMethod base eta) (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
  have hg : H.gradient=cgOperator (C-base) (cgStep base g 1) := by
    have h := knownBaseCentredMethod_last_gradient base hb eta (cgOperator C) g hc
    change H.gradient=(cgOperator C-cgOperator base) (referenceStep (cgOperator base) g 1) at h
    rw [show cgOperator C-cgOperator base=cgOperator (C-base) from (map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ)) C base).symm] at h
    exact h
  have hcanon : cgOperator (metricRoot base)⁻¹ H.gradient=
      cgOperator (relativeOperator base (C-base)) (canonicalCGStep base g 1) := by
    rw [hg]
    exact (canonical_form_action base (C-base) hb (cgStep base g 1)).symm
  have hs : canonicalCGStep base g 1=‖canonicalCGStep base g 1‖ • canonicalCGUnitStep base g 1 :=
    (NormedSpace.norm_smul_normalize _).symm
  have hsm : cgOperator (eta • M)=eta • cgOperator M := map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) eta M
  dsimp only
  rw [hcanon,hrel,hsm,_root_.smul_apply]
  calc
    _ = eta • cgOperator M (‖canonicalCGStep base g 1‖ • canonicalCGUnitStep base g 1) :=
      congrArg (fun v => eta • cgOperator M v) hs
    _ = _ := by rw [map_smul,smul_smul]

/-- The actual history-only centring output is exactly the canonical
inverse of the true observed-column centre, on the original physical
known-base scenario and its genuine complete recorded history.
Use: the finite hidden-plane inverse estimate applies to the actual M1
implementation, rather than a postulated correction using the unknown entry.
Article: main_krylov, thm:local(c), actual centred inverse dictionary.
Proof: the real returned gradient gives precisely the measured increment
column; its true positive reference scale and allowance cancel in the
actual normalization. The original initial field is preserved exactly.
Only known-root/inverse cancellation remains in the genuine output rule. -/
theorem knownBaseCentre_output_coordinates (base C M : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : base.PosDef) (eta : ℝ) (heta : 0< eta) (g : EuclideanSpace ℝ (Fin 2))
    (hc : referenceAtomCount base hb g=2) (hrel : relativeOperator base (C-base)=eta • M) :
    let m := knownBaseCentredMethod base eta
    let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g 1
    let a := inner ℝ e (cgOperator M h)
    let d := inner ℝ h (cgOperator M h)
    let J := 1+eta • planarMatrix e h (hiddenPlaneCentre a d) a d
    let rho := (eta*‖canonicalCGStep base g 1‖) • cgOperator M h
    cgOperator (metricRoot base) (m.output H)= -(cgOperator J⁻¹ rho) := by
  let m := knownBaseCentredMethod base eta
  let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
  let sigma := ‖canonicalCGStep base g 1‖
  have hsigma : 0< sigma := (knownBaseCentre_reference_scale base hb g hc).1
  have hi : H.initial=g := oneGradientRun_initial _ _ _ _
  have hcolumn := knownBaseCentre_observed_column base C M hb eta g hc hrel
  have hnorm : (eta*sigma)⁻¹ • (cgOperator (metricRoot base)⁻¹ H.gradient)=
      cgOperator M (canonicalCGUnitStep base g 1) := by
    rw [hcolumn,smul_smul,inv_mul_cancel₀ (mul_pos heta hsigma).ne',one_smul]
  change cgOperator (metricRoot base) (knownBaseCentreOutput base eta H)=_
  unfold knownBaseCentreOutput
  rw [hi]
  dsimp only
  rw [hnorm,hcolumn]
  rw [map_neg]
  have hcancel (v : EuclideanSpace ℝ (Fin 2)) : cgOperator (metricRoot base) (cgOperator (metricRoot base)⁻¹ v)=v := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
  rw [hcancel]

end
end krylov.OneGradient
