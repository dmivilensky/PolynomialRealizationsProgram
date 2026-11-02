import krylov.Envelope.CanonicalInjections
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual canonical missed-direction normalization.
Use: turn the genuine physical missed-line direction actions into the printed relative trial error times true square-root CG energy.
Source: real positive CG line domains, original root congruence cancellation and the actual zero-safe normalized CG step energy.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
variable {n : ℕ}

/-- The actual inverse-root image of a physical canonical increment on a genuine missed CG direction has the printed relative missed-line and square-root-energy normalization.
Use: The actual inverse-root image of a physical canonical increment on a genuine missed CG direction has the printed relative missed-line and square-root-energy normalization.
Article: main_krylov, thm:E1, actual canonical missed-direction normalization.
Proof: Rewrite the real missed direction as its true reciprocal-line multiple of the actual reference step, cancel the genuine root congruence and normalize the original canonical step. -/
theorem canonical_missed_direction_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (rho : ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (cgOperator (metricRoot base*C*metricRoot base) (rho • CG.direction (cgOperator base) g k))=
      (rho/CG.length (cgOperator base) g k*Real.sqrt (cgEnergy base g k)) •
        cgOperator C (canonicalCGUnitStep base g k) := by
  -- Establish the actual positive CG line before converting the genuine missed direction into its original reference-step multiple.
  have hp := cgOperator_positive base hb
  have ha : CG.length (cgOperator base) g k≠0 :=
    (CG.invariant_line_pos _ hp.2 g k (CG.invariant _ hp.1 hp.2 g k
      (fun i hi => cg_nonstagnation base hb g i (hi.trans hk))) (cg_nonstagnation base hb g k hk)).2.1.ne'
  have he : rho • CG.direction (cgOperator base) g k=
      (rho/CG.length (cgOperator base) g k) • referenceStep (cgOperator base) g k := by
    rw [referenceStep,smul_smul,div_mul_cancel₀ _ ha]
  have hdrift : Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (cgOperator (metricRoot base*C*metricRoot base) (referenceStep (cgOperator base) g k))=
      cgOperator C (cgOperator (metricRoot base) (referenceStep (cgOperator base) g k)) :=
    canonical_drift_action base C hb _
  rw [he,map_smul,map_smul,hdrift]
  change (rho/CG.length (cgOperator base) g k) • cgOperator C (canonicalCGStep base g k)=_
  have hs : canonicalCGStep base g k=‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hs,map_smul,smul_smul,cgEnergy_sqrt base hb]
end
end krylov.Envelope
