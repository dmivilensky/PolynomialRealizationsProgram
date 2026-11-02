import krylov.OneGradient.CalibratedNativeOutput
import krylov.OneGradient.EvaluatedCanonical
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true native reference flag dictionary.
Use: identify both actual implemented reference bases with the original
orthogonal CG flags, retaining their genuine distinct column scales.
Source: actual calibrated quadratic execution, positive CG lengths and
the already proved diagonal invariance of transported prefix flags.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Correction krylov.Variation
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X]

/-- The actual complete S/D reference basis has its true CG column scales.
Use: diagonal flag invariance applies to the implemented physical columns.
Article: main_krylov, thm:local(a), real native canonical columns.
Proof: exact calibrated S steps and exact quadratic D replay are genuine CG
directions. Their root images have the proved positive line/energy scales. -/
theorem calibrated_native_reference_columns (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (hcal : CalibratedTrial trial (cgOperator base) g (n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (hA0 : ∀ j,A 0 j=base) :
    metricRoot base*calibratedNativeReferenceColumns directions trial A g=
      canonicalCGUnitMatrix base g*diagonal (fun i : Fin n =>
        (if directions then (1 : ℝ) else CG.length (cgOperator base) g i.val)*
          (‖canonicalCGStep base g i.val‖/CG.length (cgOperator base) g i.val)) := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have ht : ∀ i<n,trial
      (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    calibrated_native_reference_nonzero true trial _ hp.1 hp.2 g n hpre hcal
  have hop0 : (fun k => cgOperator (A 0 k))=fun _ => cgOperator base :=
    funext (fun k => congrArg cgOperator (hA0 k))
  have hcol (i : Fin n) : WithLp.toLp 2 (fun a =>
      calibratedNativeReferenceColumns directions trial A g a i)=
        (if directions then (1 : ℝ) else CG.length (cgOperator base) g i.val) •
          CG.direction (cgOperator base) g i.val := by
    cases directions with
    | false =>
      change oneGradientStep (xrfcMethod fullMemory trial)
        (fun k => cgOperator (A 0 k)) g i.val=_
      rw [hop0]
      exact calibrated_reference_step trial _ hp.1 hp.2 g n hpre hcal i.val i.isLt
    | true =>
      change xrfcDExecutedDirection trial
        (fun k => cgOperator (A 0 k)) g i.val=1 • _
      rw [hop0,one_smul]
      exact xrfcD_executed_direction_reference _ _ hp.1 hp.2 g n hpre ht i.val i.isLt.le
  ext a i
  have he := congrArg (cgOperator (metricRoot base)) (hcol i)
  rw [map_smul,canonicalCG_direction_scale base hb g i.val (by omega),smul_smul] at he
  have he' : WithLp.toLp 2 (fun a =>
      (metricRoot base*calibratedNativeReferenceColumns directions trial A g) a i)=
        ((if directions then (1 : ℝ) else CG.length (cgOperator base) g i.val)*
          (‖canonicalCGStep base g i.val‖/CG.length (cgOperator base) g i.val)) •
            canonicalCGUnitStep base g i.val := he
  simpa only [Matrix.mul_diagonal,canonicalCGUnitMatrix,PiLp.smul_apply,smul_eq_mul,mul_comm]
    using congrArg (fun v : EuclideanSpace ℝ (Fin n) => v a) he'

/-- The genuine native calibrated S and D flags are precisely the article's
orthogonal CG prefix projections, despite their different actual scales.
Use: the actual cubic output has the original source staircase geometry.
Article: main_krylov, thm:local(a), native Pi_l=P_l.
Proof: true active lengths and step norms make every actual column scale
nonzero. Reuse diagonal flag invariance and the true full CG flag dictionary. -/
theorem calibrated_native_reference_flags (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (hcal : CalibratedTrial trial (cgOperator base) g (n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (hA0 : ∀ j,A 0 j=base) (l : ℕ) :
    cgOperator (transportedFlag
      (metricRoot base*calibratedNativeReferenceColumns directions trial A g) l)=
        (oldFlag base g l).starProjection := by
  rw [calibrated_native_reference_columns directions trial base hb g hc hcal A hA0,
    transportedFlag_right_diagonal]
  · exact canonicalCG_transportedFlag base hb g hc l
  · intro i
    have ha := (cgLength_pos base hb g i.val (by omega)).ne'
    have hs := (norm_pos_iff.mpr (canonicalCGStep_ne_zero base hb g i.val
      (fun j hj => cg_nonstagnation base hb g j (by omega)))).ne'
    have hcscale : (if directions then (1 : ℝ) else CG.length (cgOperator base) g i.val)≠0 := by
      cases directions
      · exact ha
      · exact one_ne_zero
    exact mul_ne_zero hcscale
      (div_ne_zero hs ha)

end
end krylov.OneGradient
