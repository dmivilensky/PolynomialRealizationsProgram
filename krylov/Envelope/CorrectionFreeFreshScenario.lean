import krylov.Envelope.CorrectionFreeLastSingleton
import krylov.Envelope.CanonicalProbeOrthogonality
import krylov.Envelope.FiniteSingletonTilt
import krylov.Envelope.ScenarioVariation
import krylov.Envelope.CanonicalInjections

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, actual universal correction-free fresh scenario response.
Use: identify genuine explored first variations of every real correction-free
smooth source method under a true newest cross increment, with arbitrary
actual independent correction defects.
Source: proved genuine exact affine final-gradient response, actual source
scenario differentiation and real positive-root drift cancellation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual correction-free smooth source method has the same genuine newest orthogonal-increment variation: square-root last energy times its true explored canonical increment action, independently of all real correction defects.
Use: Every actual correction-free smooth source method has the same genuine newest orthogonal-increment variation: square-root last energy times its true explored canonical increment action, independently of all real correction defects.
Article: main_krylov, s3:thm:cf, actual universal correction-free fresh scenario response.
Proof: The actual source newest increment leaves the real complete earlier quadratic history unchanged. Genuine correction-free execution ignores the true correction oracles. Differentiate the proved actual affine final gradient and cancel the real metric root. -/
theorem correctionFree_last_scenario_projection (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+2≤referenceAtomCount base hb g) (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : inner ℝ (canonicalCGUnitStep base g (k+1)) (cgOperator D (canonicalCGUnitStep base g (k+1)))=0)
    (F : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ) :
    scenarioVariation M.policy base g (k+2) (Pi.single ⟨k,by omega⟩ D,F)=
      Real.sqrt (cgEnergy base g (k+1)) •
        (exploredFlag base g (k+2)).starProjection (cgOperator D (canonicalCGUnitStep base g (k+1))) := by
  -- Use the genuine newest finite source increment and arbitrary real correction defects.
  let Θ : CanonicalScenario n (k+2) := (Pi.single ⟨k,by omega⟩ D,F)
  let V := cgOperator (metricRoot base*D*metricRoot base) (referenceStep (cgOperator base) g (k+1))
  have horth := canonical_probe_defect_orthogonal base hb g (k+1) (by omega) D hD
  have hA (t : ℝ) : scenarioProbe base (t • Θ)=canonicalFCPath base (Pi.single k D) t := by
    rw [scenarioProbe_scale]
    have he := matrixSequenceExtension_single (⟨k,by omega⟩ : Fin ((k+2)-1)) D
    change canonicalFCPath base (matrixSequenceExtension ((k+2)-1) (Pi.single ⟨k,by omega⟩ D)) t=_
    rw [he]
  -- Exact actual prefix nonanticipation and true empty corrections give the genuine affine output, rather than an assumed first-order response.
  have hpath (t : ℝ) : scenarioGradient M.policy base g (k+2) (t • Θ)=
      CG.gradient (cgOperator base) g (k+2)+t • V := by
    have hc : probedGradient M.policy (scenarioProbe base (t • Θ)) (scenarioCorrection base (t • Θ)) g (k+2)=
        probedGradient M.policy (scenarioProbe base (t • Θ)) (scenarioProbe base (t • Θ)) g (k+2) :=
      congrArg History.gradient (correctionFree_run_independent M.policy hfree
        (scenarioProbe base (t • Θ)) (scenarioCorrection base (t • Θ)) (scenarioProbe base (t • Θ)) g (k+2))
    unfold scenarioGradient
    rw [hc,hA t]
    exact correctionFree_last_singleton_gradient M.policy M.consistent hfree base hb g k D horth t
  have hd : HasDerivAt (fun t : ℝ => CG.gradient (cgOperator base) g (k+2)+t • V) V 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add (CG.gradient (cgOperator base) g (k+2))
  have hv := scenarioVariation_actual M base hb g (k+2) hcount Θ
  rw [show (fun t : ℝ => scenarioGradient M.policy base g (k+2) (t • Θ))=
    (fun t => CG.gradient (cgOperator base) g (k+2)+t • V) from funext hpath,hd.deriv] at hv
  -- Cancel the genuine metric root and normalize the actual last CG step after identifying the true source derivative.
  have hc := canonical_drift_action base D hb (referenceStep (cgOperator base) g (k+1))
  change cgOperator (metricRoot base)⁻¹ V=cgOperator D (canonicalCGStep base g (k+1)) at hc
  rw [hc] at hv
  have hs : canonicalCGStep base g (k+1)=Real.sqrt (cgEnergy base g (k+1)) • canonicalCGUnitStep base g (k+1) := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  rw [hs,map_smul,map_smul] at hv
  exact hv

/-- If the genuine newest canonical increment action lies in the actual explored flag, every real correction-free smooth source method has exactly the true square-root-energy fresh response.
Use: If the genuine newest canonical increment action lies in the actual explored flag, every real correction-free smooth source method has exactly the true square-root-energy fresh response.
Article: main_krylov, s3:thm:cf, actual universal correction-free fresh scenario response.
Proof: Apply the actual universal newest-increment variation and genuine explored projection membership. -/
theorem correctionFree_last_scenario_variation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+2≤referenceAtomCount base hb g) (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : inner ℝ (canonicalCGUnitStep base g (k+1)) (cgOperator D (canonicalCGUnitStep base g (k+1)))=0)
    (hmem : cgOperator D (canonicalCGUnitStep base g (k+1))∈exploredFlag base g (k+2))
    (F : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ) :
    scenarioVariation M.policy base g (k+2) (Pi.single ⟨k,by omega⟩ D,F)=
      Real.sqrt (cgEnergy base g (k+1)) • cgOperator D (canonicalCGUnitStep base g (k+1)) := by
  rw [correctionFree_last_scenario_projection M hfree base hb g k hcount D hD F,
    (exploredFlag base g (k+2)).starProjection_eq_self_iff.mpr hmem]
end
end krylov.Envelope
