import krylov.Convergence.SlidingMetricExecution
import krylov.Convergence.SlidingFCPathRate

/-!
Article: main_krylov, thm:G, original physical source normalization.
Use: construct a genuine admitted local metric chord from the original
physical neighbourhood, derive every pulled-back derivative and the exact
LH_E*lambda_min^(-3/2) allowance, then apply the invariant observed-path
proof to the unchanged physical FC direction rule.
Source: the true Hessian positive root and the Frechet chain rule.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1200000

/-- Original local regularity always admits a smaller closed source ball
with the standard small-Hessian margin. No algorithmic premise is used. -/
theorem local_source_closedBall_radius
    (S : Set (EuclideanSpace ℝ (Fin n))) (hn : S∈𝓝 (0:EuclideanSpace ℝ (Fin n))) (L : ℝ≥0) :
    ∃ R : ℝ,0<R ∧ ∀ r : ℝ,0<r → r≤R →
      Metric.closedBall (0:EuclideanSpace ℝ (Fin n)) r⊆S ∧ (L:ℝ)*r≤1/2 := by
  obtain ⟨ε,hε,hball⟩:=Metric.mem_nhds_iff.mp hn
  let R:=min (ε/2) (1/(2*((L:ℝ)+1)))
  have hR : 0<R := lt_min (by linarith) (by positivity)
  refine ⟨R,hR,fun r _hr hr=>⟨?_,?_⟩⟩
  · intro z hz
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    have hzr : ‖z‖≤r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hRe : R≤ε/2 := min_le_left _ _
    linarith
  · have hRL : R≤1/(2*((L:ℝ)+1)) := min_le_right _ _
    have hm:=(le_div_iff₀ (by positivity : 0<2*((L:ℝ)+1))).mp (hr.trans hRL)
    nlinarith [L.coe_nonneg]

/-- Complete physical sliding-FC theorem. Its norm and Lipschitz constant
are derived from the original Hstar, and all finite gates/frame domains
come from the genuine actual observed solves. The three conclusions are
the printed general constant, R-order and sharper half constant. -/
theorem metricSlidingFCSequence_original_source
    (base : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2))) (S : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hn : S∈𝓝 center) (hbase : H center=cgOperator base) (hG₀ : G center=0)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    {mu : ℝ} (hmu : 0<mu)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v)) :
    let T:=metricCoordinates base hb
    let LH:=(LE:ℝ)*mu^(-(3/2:ℝ))
    ∃ R : ℝ,0<R ∧ ∀ r : ℝ,0<r → r≤R →
      ∀ seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)),
      let x:=metricSlidingFCSequence T center f G r seed
      let e:=fun k=>‖T (x k-center)‖
      Tendsto x atTop (𝓝 center) →
      (∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G x k).det) →
      (∀ η : ℝ,0<η → ∀ᶠ k in atTop,e (k+n+2)≤
        (4*LH*((n+1:ℕ):ℝ)*Real.sqrt (n+1)+η)*e k*e (k+1)) ∧
      HasROrder e (fullConjugacyRoot (n+2)) ∧
      ((fun k=>T (x (k+1)-center))=o[atTop] e →
        ∀ η : ℝ,0<η → ∀ᶠ k in atTop,e (k+n+2)≤(LH/2+η)*e k*e (k+1)) := by
  let T:=metricCoordinates base hb
  let fh:=centeredMetricObjective T center f
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  have hLc : (L:ℝ)=(LE:ℝ)*mu^(-(3/2:ℝ)) := Real.coe_toNNReal _
    (mul_nonneg LE.coe_nonneg (Real.rpow_nonneg hmu.le _))
  have hHh:=centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _ :=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hGh₀ : Gh 0=0 := by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  have hT: T.symm.toContinuousLinearMap.IsSymmetric:=metricCoordinates_inverse_symmetric base hb
  obtain ⟨R,hR,hRsource⟩:=local_source_closedBall_radius (centeredMetricDomain T center S)
    (centeredMetricDomain_mem_nhds T center hn) L
  refine ⟨R,hR,fun r hr hrr seed=>?_⟩
  dsimp only
  intro hconv hsolve
  obtain ⟨hball,hLr⟩:=hRsource r hr hrr
  have hh : LipschitzOnWith L Hh (Metric.closedBall 0 r):=hHh.mono hball
  have hfh z (hz : z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r) :
      HasFDerivAt fh (innerSL ℝ (Gh z)) z :=
    centeredMetricObjective_hasFDerivAt T hT center f G z (hf _ (hball hz))
  have hGh z (hz : z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r) :
      HasFDerivAt Gh (Hh z) z :=
    centeredMetricGradient_hasFDerivAt T center G H z (hG _ (hball hz))
  have hdata:=metricSlidingFCSequence_source_data T hT center f G H hr hH₀ hLr hh hfh hGh seed hconv hsolve
  let x:=metricSlidingFCSequence T center f G r seed
  let z:=fun k=>T (x k-center)
  let d:=fun k=>T (slidingFCDirection (n:=n) G x (k-(n+1)))
  refine ⟨?_,?_,?_⟩
  · intro η hη
    have ht:=source_path_sharp_product fh Gh Hh hr hGh₀ hH₀ hLr hh hfh hGh z d
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hη
    simpa only [hLc] using ht
  · exact source_path_rorder fh Gh Hh hr hGh₀ hH₀ hLr hh hfh hGh z d
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  · intro hs η hη
    have ht:=source_path_half_product fh Gh Hh hr hGh₀ hH₀ hLr hh hfh hGh z d
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hs hη
    simpa only [hLc] using ht

end
end krylov.Convergence
