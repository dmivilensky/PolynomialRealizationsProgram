import krylov.Convergence.SlidingMetricProbe
import krylov.Convergence.SlidingMetricRegularity
import krylov.Convergence.RFCPathRefinedAngle
import krylov.Convergence.RFCPathGradientClock
import krylov.Convergence.SlidingRFCGradientClock

/-!
Article: main_krylov, thm:Ip, full original physical RFC source theorem.
Use: derive canonical old-window gain sigma_H, all true observed gates,
exact oldest-pair coefficient, the actual correction-angle refinement and
the two-gradient clock from the unchanged physical observed executor.
Source: true source derivative transport, primal/dual endpoint covariance,
and the proved invariant RFC path estimates. No canonical rate or phase
is a premise. The physical Hessian allowance is LH_E*mu^(-3/2).
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1600000

/-- The literal actual physical searched correction, after its genuine
objective search along the real evaluated RFC probe. -/
def metricSlidingRFCSearchCorrection
    (T : EuclideanSpace ℝ (Fin (n+2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2))) (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (r γ : ℝ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) :
    EuclideanSpace ℝ (Fin (n+2)) :=
  let x:=slidingRFCSequence G probe γ seed
  x (k+n+2)-centeredMetricExactPoint T center f (x (k+n+1)) (slidingRFCProbe G probe x k) r

/-- The actual correction is exactly the invariant source-path correction
in true metric coordinates; this is a point identity, not an error bound. -/
theorem metricSlidingRFCSearchCorrection_eq
    (T : EuclideanSpace ℝ (Fin (n+2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2))) (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (r γ : ℝ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) :
    T (metricSlidingRFCSearchCorrection T center f G probe r γ seed k)=
      rfcPathSearchCorrection (centeredMetricObjective T center f)
        (fun j=>T (slidingRFCSequence G probe γ seed j-center))
        (fun j=>T (slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) j)) r k := by
  simp only [metricSlidingRFCSearchCorrection,centeredMetricExactPoint,rfcPathSearchCorrection,
    map_sub,map_add,T.apply_symm_apply]
  abel_nf

/-- Every real accepted and probe gradient-query point transports exactly,
so the gradient clock counts the original physical executor's queries. -/
theorem slidingRFCGradientQuery_metric
    (T : EuclideanSpace ℝ (Fin (n+2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2)))
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (γ : ℝ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (j : ℕ) :
    T (slidingRFCGradientQuery G probe γ seed j-center)=
      rfcPathGradientQuery (n:=n) (fun k=>T (slidingRFCSequence G probe γ seed k-center))
        (fun k=>T (slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k)) j := by
  simp only [slidingRFCGradientQuery,rfcPathGradientQuery]
  split_ifs
  · rfl
  · simp only [map_sub,map_add]
    abel_nf

/-- Complete physical RFC theorem under the article's original local
source, bounded actual probes and physical old-window independence.
The sharper angle conclusion only invokes the original nonstationary
part of (A2); the main oldest bound includes exact zero-error branches. -/
theorem slidingRFCSequence_physical_original_source
    (base : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2))) (S : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hn : S∈𝓝 center) (hbase : H center=cgOperator base) (hG₀ : G center=0)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    {mu upper : ℝ} (hmu : 0<mu) (hu : 0<upper)
    (hlower : ∀ a,mu*‖a‖^2≤ inner ℝ a (cgOperator base a))
    (hupper : ∀ a,inner ℝ a (cgOperator base a)≤upper*‖a‖^2) :
    let T:=metricCoordinates base hb
    let LH:=(LE:ℝ)*mu^(-(3/2:ℝ))
    ∃ R : ℝ,0<R ∧∀ r : ℝ,0<r → r≤R →
      ∀ probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ,
      ∀ γ : ℝ,0<γ → ∀ seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)),
      let x:=slidingRFCSequence G probe γ seed
      let z:=fun k=>T (x k-center)
      let v:=fun k=>T (slidingRFCProbe G probe x k)
      Tendsto x atTop (𝓝 center) →
      (∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) G x k).det) →
      ∀ cP : ℝ,(∀ᶠ k in atTop,slidingRFCProbe G probe x k≠0 ∧
        ‖slidingRFCProbe G probe x k‖≤cP*‖z (k+n+1)‖) →
      ∀ σ : ℝ,0<σ →
      (∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=n+1) x k)) c‖^2) →
      (∀ᶠ k in atTop,‖pairDefect (windowStep (n:=n+1) x k) (windowImage G x k)‖<γ) ∧
      (∀ᶠ k in atTop,
        IsUnit (windowMatrix (unitWindow (Fin.snoc (windowStep (n:=n+1) z k) (v k)))).det ∧
        IsUnit (ss1Model (Fin.snoc (windowStep (n:=n+1) z k) (v k))
          (Fin.snoc (windowImage (centeredMetricGradient T center G) z k)
            (centeredMetricGradient T center G (z (k+n+1)+v k)-centeredMetricGradient T center G (z (k+n+1))))).det ∧
        z (k+n+2)=ss1Point (Fin.snoc (windowStep (n:=n+1) z k) (v k))
          (Fin.snoc (windowImage (centeredMetricGradient T center G) z k)
            (centeredMetricGradient T center G (z (k+n+1)+v k)-centeredMetricGradient T center G (z (k+n+1))))
          (centeredMetricGradient T center G (z (k+n+1))) (z (k+n+1)) ∧
        σ*Real.sqrt (mu/upper)≤slidingRFCStoredOldestDistance z k) ∧
      ((fun k=>z (k+1))=o[atTop](fun k=>‖z k‖)) ∧
      (∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
        ‖z (k+n+2)‖≤(1+theta k)*LH/(2*(slidingRFCStoredOldestDistance z k)^2)*‖z (k+n+1)‖*‖z k‖) ∧
      HasROrder (fun k=>‖z k‖) (oneGradientRoot (n+2)) ∧
      HasROrder (fun j=>‖T (slidingRFCGradientQuery G probe γ seed j-center)‖)
        ((oneGradientRoot (n+2))^(1/2:ℝ)) ∧
      ((∀ᶠ k in atTop,x k≠center) →
        (fun k=>rfcPathCorrectionRatio (centeredMetricObjective T center f) z v r k-
          Real.sin (InnerProductGeometry.angle (z (k+n+1)) (v k)))=O[atTop](fun k=>‖z k‖) ∧
        ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,‖z (k+n+2)‖≤K*‖z (k+n+1)‖*
          ((rfcPathCorrectionRatio (centeredMetricObjective T center f) z v r k+‖z k‖)*‖z k‖+
            ‖z (k+1)‖+‖z (k+n+1)‖)) := by
  let T:=metricCoordinates base hb
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  have hLc : (L:ℝ)=(LE:ℝ)*mu^(-(3/2:ℝ)):=Real.coe_toNNReal _
    (mul_nonneg LE.coe_nonneg (Real.rpow_nonneg hmu.le _))
  obtain ⟨R,hR,hRsource⟩:=physical_metric_source_radius base hb f G H center S hn hbase hG₀ hH hf hG hmu hlower
  refine ⟨R,hR,fun r hr hrr probe γ hγ seed=>?_⟩
  dsimp only
  intro hconv hsolve cP hprobe σ hσ hgain
  let x:=slidingRFCSequence G probe γ seed
  let z:=fun k=>T (x k-center)
  let v:=fun k=>T (slidingRFCProbe G probe x k)
  let fh:=centeredMetricObjective T center f
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  have hT:=metricCoordinates_inverse_symmetric base hb
  obtain ⟨hLr,hHh,hH₀,hGh₀,hfh,hGh⟩:=hRsource r hr hrr
  have hdata:=slidingRFCSequence_metric_data T hT center G probe γ seed hconv hsolve
  let σH:=σ*Real.sqrt (mu/upper)
  have hσH : 0<σH:=mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu))
  have hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+1),windowStep (n:=n+1) x k i≠0 := by
    filter_upwards [hsolve] with k hk i
    exact observed_solve_step_ne_zero _ _ hk i
  have hgainH:=metric_path_window_gain base hb center x hmu hu hσ.le hlower hupper hsteps hgain
  have hσH₁ : σH≤1 := by
    obtain ⟨k,hk⟩:= (hgainH.and hdata.2.2.1).exists
    exact unit_window_gain_le_one _ (fun i=>observed_solve_step_ne_zero _ _ hk.2 i) hσH.le hk.1
  have hprobeH : ∀ᶠ k in atTop,v k≠0 ∧‖v k‖≤(Real.sqrt upper*|cP|)*‖z (k+n+1)‖ := by
    have hh:=metric_path_probe_bound base hb center (fun k=>x (k+n+1))
      (slidingRFCProbe G probe x) hu hupper hprobe
    exact hh
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈Metric.closedBall 0 r := by simpa using hr.le
  have hnb:=Metric.closedBall_mem_nhds (0:EuclideanSpace ℝ (Fin (n+2))) hr
  have hs:=rfcPath_superlinear Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb hHh hH₀ hGh hGh₀
    z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH
  refine ⟨?_,?_,hs.2,?_,?_,?_,?_⟩
  · filter_upwards [hs.1] with k hk
    change ‖pairDefect (windowStep (n:=n+1) (fun j=>T (x j-center)) k)
      (windowImage (centeredMetricGradient T center G) (fun j=>T (x j-center)) k)‖<γ at hk
    rw [centered_metric_windowStep,centered_metric_windowImage,pairDefect_metric T hT] at hk
    exact hk
  · have hd:=rfcPath_window_domains Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb
      hHh hH₀ hGh hGh₀ z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH
    have hl:=(rfcPath_stored_distance_comparison Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb
      hHh hH₀ hGh hGh₀ z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH).1
    filter_upwards [hd,hl] with k hk hlk
    exact ⟨hk.1,hk.2.2.1,hk.2.2.2,hlk⟩
  · obtain ⟨theta,ht,hbnd⟩:=rfcPath_printed_oldest_bound Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb
      hHh hH₀ hGh hGh₀ z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH
    refine ⟨theta,ht,?_⟩
    filter_upwards [hbnd] with k hk
    rw [hLc] at hk
    convert hk using 1
    ring
  · exact rfcPath_rorder Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb
      hHh hH₀ hGh hGh₀ z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH
  · have hh:=rfcPath_gradient_query_rorder Gh Hh (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hnb
      hHh hH₀ hGh hGh₀ z v hγ hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH
    simpa only [slidingRFCGradientQuery_metric] using hh
  · intro hne
    have hnez : ∀ᶠ k in atTop,z k≠0 := by
      filter_upwards [hne] with k hk
      exact fun hz=>hk (sub_eq_zero.mp (T.injective (hz.trans T.map_zero.symm)))
    exact ⟨rfcPath_correction_angle fh Gh Hh hr hLr hHh hH₀ hfh hGh hGh₀ z v hγ
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH hnez,
      rfcPath_refined_angle_bound fh Gh Hh hr hLr hHh hH₀ hfh hGh hGh₀ z v hγ
        hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hprobeH hσH hσH₁ hgainH hnez⟩

end
end krylov.Convergence
