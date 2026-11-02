import krylov.OneGradient.KnownBaseSourceEmbedding
import krylov.Stability.ReferenceErrorRegularity
import krylov.Stability.MovingFullReference
import krylov.Information.MetricSlack
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), true source-wide own-base normalization.
Use: derive a common actual own-base penultimate-error norm variation
bound on the full known-base source space, before source choices.
Source: genuine full symmetric source coordinates, actual positive
reference neighborhoods and proved true CG canonical error regularity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Reference krylov.Secant krylov.Information
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine source-cube base is positive on a derived neighborhood
of its true known reference, and its actual penultimate error norm has
first-order variation in the full original primitive source tuple.
Use: normalized whole-source upper bounds use the actual source reference
error instead of an assumed smooth normalization or a fixed denominator.
Article: main_krylov, thm:local(b), real joint reference normalization.
Proof: the actual affine symmetric prior coordinate is analytic. Its
relative physical displacement tends to zero, so the existing signed
Loewner theorem derives positivity on a genuine neighborhood. Apply the
proved actual CG reference-error norm variation to that real family. -/
theorem knownBaseSourceCube_reference_norm_order
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    (fun Theta : symmetricScenarios (n+1) (n+1) =>
      ‖cgCanonicalError (knownBaseSourceCube base Theta).base g n‖-‖cgCanonicalError base g n‖)
      =O[𝓝 0] (fun Theta => ‖Theta‖) := by
  let B := fun Theta : symmetricScenarios (n+1) (n+1) => (knownBaseSourceCube base Theta).base
  have hB0 : B 0=base := by
    have hzero := (knownBaseSourceCube_operator_data base hb).2.2 0
    simpa only [oneGradientScenarioMatrices_zero] using hzero
  have hBan : AnalyticAt ℝ B 0 := analyticAt_const.add
    ((analyticAt_const.mul (symmetricScenario_correction_analytic (n := n+1) (N := n+1) 0)).mul analyticAt_const)
  have hsym (Theta : symmetricScenarios (n+1) (n+1)) : (B Theta).IsSymm := by
    have h := (knownBaseSourceCube_operator_data base hb).2.1 Theta 0
    simpa only [oneGradientScenarioMatrices_zero] using h
  have hrel : ContinuousAt (fun Theta => relativeBudget base (B Theta-base)) 0 := by
    exact (((continuousAt_const.mul (hBan.continuousAt.sub continuousAt_const)).mul continuousAt_const).norm)
  have hrel0 : relativeBudget base (B 0-base)=0 := by
    simp only [hB0,sub_self,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero]
  have hnear : ∀ᶠ Theta in 𝓝 (0 : symmetricScenarios (n+1) (n+1)),(B Theta).PosDef := by
    have hsmall : ∀ᶠ Theta in 𝓝 (0 : symmetricScenarios (n+1) (n+1)),relativeBudget base (B Theta-base)<1/2 := by
      have h0 : relativeBudget base (B 0-base)<1/2 := by rw [hrel0];norm_num
      have hn : ∀ᶠ x : ℝ in 𝓝 (relativeBudget base (B 0-base)),x<1/2 := gt_mem_nhds h0
      exact hrel.tendsto.eventually hn
    filter_upwards [hsmall] with Theta hTheta
    exact (relative_displacement_base base (B Theta) hb (hsym Theta)
      (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1) hTheta.le).2.2
  have h := referenceError_norm_order B (fun _ => g) n hBan hnear analyticAt_const
    (fun i hi => by rw [hB0];exact cg_nonstagnation base hb g i (by omega))
  simpa only [hB0] using h

/-- The whole original physical source class has one common actual
penultimate reference-error norm tube at the known full CG reference.
Use: source-wide normalization is uniform even for discontinuously chosen
physical matrices and includes every original independent budget profile.
Article: main_krylov, thm:local(b), true all-source normalization tube.
Proof: unpack genuine joint reference norm variation, choose a real source
ball once, and use exact whole-source base reconstruction in that ball. -/
theorem knownBase_source_reference_norm_tube
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta D : ℝ,0<delta ∧ 0<D ∧ ∀ (S : Scenario (n+1)) (hbase : S.base.IsSymm)
      (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm),
      ‖knownBaseSourceParameters base hb S hbase hinc hterm‖<delta →
      |‖cgCanonicalError S.base g n‖-‖cgCanonicalError base g n‖|≤
        D*‖knownBaseSourceParameters base hb S hbase hinc hterm‖ := by
  obtain ⟨D,hD,hbound⟩ := isBigO_iff'.mp (knownBaseSourceCube_reference_norm_order base hb g hc)
  obtain ⟨delta,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨delta,D,hd,hD,?_⟩
  intro S hbase hinc hterm hsmall
  let Theta := knownBaseSourceParameters base hb S hbase hinc hterm
  have h := hnear (by simpa only [dist_zero_right] using hsmall)
  have hbaseeq := (knownBaseSourceParameters_reconstruct base hb hn S hbase hinc hterm).1
  rw [hbaseeq] at h
  simpa only [Real.norm_eq_abs,abs_norm] using h

end
end krylov.OneGradient
