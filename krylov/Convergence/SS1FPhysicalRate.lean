import krylov.Convergence.WindowCenteredCoordinates
import krylov.Convergence.SS1PhysicalRate
import krylov.Convergence.SS1ObservedSplit

/-!
Article: main_krylov, thm:ss1F and cor:xrF, physical value secant rate.
Use: derive the printed improved order for the genuine observable executor
in an arbitrary actual minimizer metric. Physical incoming independence
and physical Hessian Lipschitz regularity are transported exactly. The
remaining third derivative hypotheses are the article's true scalar C3,1
source in that metric, rather than conclusions about any model or output.
Source: actual centered derivative reconstruction, oblique split estimates
and the proved improved SS1-F delayed characteristic recurrence.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- Genuine physical SS1-F has order tau_1(dimension). Its actual observed
covector policy satisfies (S) as a conclusion of the source estimates. -/
theorem ss1FObservedSequence_centered_physical_rorder
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L L₃ : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hbase : H center=cgOperator base)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    (T₃ : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (hT : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      HasFDerivAt (gradientHessian (centeredMetricHessian (metricCoordinates base hb) center H)) (T₃ z).form z)
    (hLip : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      ∀ w∈centeredMetricDomain (metricCoordinates base hb) center S,∀ h,‖h‖=1 →
      |(T₃ z).form h h h-(T₃ w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G (ss1FObservedSplit G) seed) atTop (𝓝 center))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep
        (ss1FSequence f G (ss1FObservedSplit G) seed) k)) c‖^2) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      (ss1FSequence f G (ss1FObservedSplit G) seed k-center)‖) (oneGradientRoot (n+1)) := by
  let J := metricCoordinates base hb
  let fh := centeredMetricObjective J center f
  let Gh := centeredMetricGradient J center G
  let Hh := centeredMetricHessian J center H
  let Sh := centeredMetricDomain J center S
  let sh := fun i=>J (seed i-center)
  let x := ss1FSequence f G (ss1FObservedSplit G) seed
  let xh := ss1FSequence fh Gh (ss1FObservedSplit Gh) sh
  have he (k : ℕ) : J (x k-center)=xh k :=
    ss1FObservedSequence_centered_coordinate J (metricCoordinates_inverse_symmetric base hb) center f G seed k
  have hSc : Convex ℝ Sh := centeredMetricDomain_convex J center hS
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈Sh := by
    simpa only [Sh,centeredMetricDomain,Set.mem_preimage,map_zero,add_zero] using hc
  have hnh : Sh∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))) := centeredMetricDomain_mem_nhds J center hn
  have hHh := centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _ :=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hfh (z) (hz : z∈Sh) : HasFDerivAt fh (innerSL ℝ (Gh z)) z :=
    centeredMetricObjective_hasFDerivAt J (metricCoordinates_inverse_symmetric base hb) center f G z (hf _ hz)
  have hGh (z) (hz : z∈Sh) : HasFDerivAt Gh (Hh z) z :=
    centeredMetricGradient_hasFDerivAt J center G H z (hG _ hz)
  have hGz : Gh 0=0 := by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  have hch : Tendsto xh atTop (𝓝 0) := by
    have hh := J.continuous.continuousAt.tendsto.comp (hconv.sub_const center)
    change Tendsto (fun k=>J (x k-center)) atTop (𝓝 (J (center-center))) at hh
    simpa only [sub_self,map_zero,he] using hh
  have hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))).det ∧
        σ*Real.sqrt (mu/upper)≤leastGain (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))) := by
    filter_upwards [hgain] with k hk
    have hh := metric_full_window_leastGain base hb (windowStep x k) hmu hu hσ hlower hupper hk
    have hw : (fun i : Fin (n+1)=>J (windowStep x k i))=windowStep xh k := by
      funext i
      have hdiff : windowStep x k i=(x (k+i.val+1)-center)-(x (k+i.val)-center) := by
        dsimp only [windowStep]
        abel_nf
      rw [hdiff,map_sub,he,he]
      rfl
    rwa [hw] at hh
  have hs : ∀ᶠ k in atTop,∀ i : Fin (n+1),windowStep xh k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    apply windowMatrix_step_ne_zero (unitWindow (windowStep xh k)) hk.1 i
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  have hw := observed_split_eventually_admissible Gh Hh Sh hSc h₀ hnh hHh hH₀ hGh xh hch hs
  have hr := (ss1FSequence_improved_rorder fh Gh Hh T₃ Sh hSc h₀ hnh hHh hH₀ hfh hGh hGz hT hLip
    (norm_nonneg (canonicalVariation (T₃ 0))) (canonicalVariation_unit_diagonal_bound (T₃ 0))
    (ss1FObservedSplit Gh) sh hch (by norm_num : (0:ℝ)≤3)
    (mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu))) hw hind).2
  change HasROrder (fun k=>‖J (x k-center)‖) _
  simpa only [he] using hr

end
end krylov.Convergence
