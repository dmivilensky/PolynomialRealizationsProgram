import krylov.Envelope.CorrectionFreeHiddenPrefix
import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioPaths
import krylov.Envelope.CanonicalInjections

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), genuine correction-free hidden-prefix source variation.
Use: identify the actual explored derivative on every true finite source scenario with vanishing real earlier probe defects.
Source: proved exact actual affine hidden-prefix execution, genuine primitive-derived scenario differentiation and true metric-root cancellation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual correction-free smooth method has the exact projected newest cumulative response when the true earlier canonical probe defects vanish.
Use: Every actual correction-free smooth method has the exact projected newest cumulative response when the true earlier canonical probe defects vanish.
Article: main_krylov, apB:lem:mu(d), genuine correction-free hidden-prefix source variation.
Proof: Differentiate the real exact affine executed gradient on the genuine source axis and cancel its true positive metric root. -/
theorem correctionFree_hidden_scenario_projection (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (Θ : CanonicalScenario n (k+1))
    (hprefix : ∀ j<k,cgOperator (∑ l∈Finset.range j,matrixSequenceExtension ((k+1)-1) Θ.1 l)
      (canonicalCGUnitStep base g j)=0)
    (horth : inner ℝ (canonicalCGUnitStep base g k)
      (cgOperator (∑ l∈Finset.range k,matrixSequenceExtension ((k+1)-1) Θ.1 l) (canonicalCGUnitStep base g k))=0) :
    scenarioVariation M.policy base g (k+1) Θ=
      Real.sqrt (cgEnergy base g k) • (exploredFlag base g (k+1)).starProjection
        (cgOperator (∑ l∈Finset.range k,matrixSequenceExtension ((k+1)-1) Θ.1 l) (canonicalCGUnitStep base g k)) := by
  -- The actual finite source extension gives genuine operator paths and arbitrary independent correction defects.
  let E := matrixSequenceExtension ((k+1)-1) Θ.1
  let V := cumulativeDrift base E k (referenceStep (cgOperator base) g k)
  have hpath (t : ℝ) : scenarioGradient M.policy base g (k+1) (t • Θ)=
      CG.gradient (cgOperator base) g (k+1)+t • V := by
    unfold scenarioGradient
    rw [scenarioProbe_scale]
    exact correctionFree_hidden_prefix_gradient M.policy M.consistent hfree base hb g E k (by omega)
      hprefix horth (scenarioCorrection base (t • Θ)) t
  -- Differentiate the exact executed affine gradient; no response or regularity premise is added to the source class.
  have hd : HasDerivAt (fun t : ℝ => CG.gradient (cgOperator base) g (k+1)+t • V) V 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add (CG.gradient (cgOperator base) g (k+1))
  have hv := scenarioVariation_actual M base hb g (k+1) hcount Θ
  rw [show (fun t : ℝ => scenarioGradient M.policy base g (k+1) (t • Θ))=
    (fun t => CG.gradient (cgOperator base) g (k+1)+t • V) from funext hpath,hd.deriv] at hv
  -- Cancel the true physical congruence and retain the actual CG energy normalization.
  have hc := canonical_drift_action base (∑ l∈Finset.range k,E l) hb (referenceStep (cgOperator base) g k)
  change cgOperator (metricRoot base)⁻¹ V=
    cgOperator (∑ l∈Finset.range k,E l) (canonicalCGStep base g k) at hc
  rw [hc] at hv
  have hs : canonicalCGStep base g k=Real.sqrt (cgEnergy base g k) • canonicalCGUnitStep base g k := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  rw [hs,map_smul,map_smul] at hv
  exact hv
end
end krylov.Envelope
