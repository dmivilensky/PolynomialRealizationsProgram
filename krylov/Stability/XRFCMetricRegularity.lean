import krylov.Stability.ContDiffXRFC
import krylov.Stability.SmoothMetricCompact
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine joint varying-reference XRFC metric output regularity.
Use: derive compact-uniform norm remainders for the actual full-memory XRFC semantic output in true finite parameter charts with a varying physical metric.
Source: primitive observed C-two trial charts, actual positive quadratic model domains and the proved genuine inverse metric-root C-two calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped Topology Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The genuine varying-metric semantic XRFC output is jointly C-two in its actual primitive operator and observed trial data near the original positive quadratic reference.
Use: The genuine varying-metric semantic XRFC output is jointly C-two in its actual primitive operator and observed trial data near the original positive quadratic reference.
Article: main_krylov, thm:E1, genuine joint varying-reference XRFC metric output regularity.
Proof: Derive actual output regularity from primitive observed trial charts, then compose the real smooth inverse metric root with the genuine semantic output. -/
theorem xrfc_metric_output_contDiffAt (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : X) (N : ℕ)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ i,ContDiffAt ℝ 2 (fun p => A p i) x) (hB : ContDiffAt ℝ 2 B x) (hg : ContDiffAt ℝ 2 g x)
    (hAx : A x=fun _ => cgOperator (base x))
    (hpre : ∀ i<N,CG.gradient (cgOperator (base x)) (g x) i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k)) :
    let m := xrfcMethod fullMemory trial
    ContDiffAt ℝ 2 (fun p => cgOperator (metricRoot (base p))⁻¹
      (m.outputGradient (B p) (oneGradientRun m (A p) (g p) N))) x := by
  have hp := cgOperator_positive (base x) hpos.self_of_nhds
  have hout := (quadraticXRFC_output_contDiffAt trial A B g x hA hB hg
    (cgOperator (base x)) hAx hp.1 hp.2 N hpre ht hT).2
  exact (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x hb hpos)).clm_apply hout
end
end krylov.Stability
