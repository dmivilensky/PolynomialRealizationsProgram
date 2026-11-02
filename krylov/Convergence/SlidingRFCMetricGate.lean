import krylov.Convergence.SlidingMetricRegularity
import krylov.Convergence.SlidingRFCMetric

/-!
Article: main_krylov, paragraph preceding thm:G and thm:Ip.
Use: show that original physical RFC defects tend to zero and every
fixed positive observed gate eventually passes, without old-window
independence. Source: true convergent endpoint secants, actual defined
observed solves, and invariant measured-energy normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- Original physical source and defined convergent observed solves alone
force actual RFC defect convergence. In particular the conclusion needs
neither (A4), successful corrections nor an assumed canonical model limit. -/
theorem slidingRFCSequence_physical_defects
    (base : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (center : EuclideanSpace ℝ (Fin (n+2))) (S : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hn : S∈𝓝 center) (hbase : H center=cgOperator base) (hG₀ : G center=0)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    {mu : ℝ} (hmu : 0<mu) (hlower : ∀ a,mu*‖a‖^2≤ inner ℝ a (cgOperator base a))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (γ : ℝ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingRFCSequence G probe γ seed) atTop (𝓝 center))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) G (slidingRFCSequence G probe γ seed) k).det) :
    let x:=slidingRFCSequence G probe γ seed
    Tendsto (fun k=>pairDefect (windowStep (n:=n+1) x k) (windowImage G x k)) atTop (𝓝 0) ∧
      ∀ threshold : ℝ,0<threshold → ∀ᶠ k in atTop,
        ‖pairDefect (windowStep (n:=n+1) x k) (windowImage G x k)‖<threshold := by
  let T:=metricCoordinates base hb
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  let x:=slidingRFCSequence G probe γ seed
  let z:=fun k=>T (x k-center)
  have hT:=metricCoordinates_inverse_symmetric base hb
  obtain ⟨R,hR,hRsource⟩:=physical_metric_source_radius base hb f G H center S hn hbase hG₀ hH hf hG hmu hlower
  obtain ⟨_hsmall,hHh,hH₀,_hGh₀,_hfh,hGh⟩:=hRsource R hR le_rfl
  have hdata:=slidingRFCSequence_metric_data T hT center G probe γ seed hconv hsolve
  have ha (i : Fin (n+1)) : Tendsto (fun k=>z (k+i.val)) atTop (𝓝 0) := hdata.2.1.comp (tendsto_add_atTop_nat i.val)
  have hb' (i : Fin (n+1)) : Tendsto (fun k=>z (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hdata.2.1.comp (tendsto_add_atTop_nat (i.val+1))
  have hnb:=Metric.closedBall_mem_nhds (0:EuclideanSpace ℝ (Fin (n+2))) hR
  have hm : ∀ᶠ k in atTop,(∀ i : Fin (n+1),z (k+i.val)∈Metric.closedBall 0 R) ∧
      (∀ i : Fin (n+1),z (k+i.val+1)∈Metric.closedBall 0 R) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnb).and
      (Filter.eventually_all.mpr fun i=>(hb' i).eventually hnb)
  have hs : ∀ᶠ k in atTop,∀ i : Fin (n+1),z (k+i.val+1)-z (k+i.val)≠0 := by
    filter_upwards [hdata.2.2.1] with k hk i
    exact observed_solve_step_ne_zero _ _ hk i
  have ht:=source_window_defects_tendsto Gh Hh (Metric.closedBall 0 R) (convex_closedBall _ _)
    (by simpa using hR.le) hHh hH₀ hGh (fun k i=>z (k+i.val)) (fun k i=>z (k+i.val+1)) ha hb' hm hs
  have hdef (k : ℕ) : pairDefect (windowStep (n:=n+1) z k) (windowImage Gh z k)=
      pairDefect (windowStep (n:=n+1) x k) (windowImage G x k) := by
    change pairDefect (windowStep (n:=n+1) (fun j=>T (x j-center)) k)
      (windowImage (centeredMetricGradient T center G) (fun j=>T (x j-center)) k)=_
    rw [centered_metric_windowStep,centered_metric_windowImage,pairDefect_metric T hT]
  have hout : Tendsto (fun k=>pairDefect (windowStep (n:=n+1) x k) (windowImage G x k)) atTop (𝓝 0) := by
    change Tendsto (fun k=>pairDefect (windowStep (n:=n+1) z k) (windowImage Gh z k)) atTop (𝓝 0) at ht
    simpa only [hdef] using ht
  refine ⟨hout,fun threshold hthreshold=>?_⟩
  have hh : Tendsto (fun k=>‖pairDefect (windowStep (n:=n+1) x k) (windowImage G x k)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hout.norm
  exact hh.eventually (gt_mem_nhds hthreshold)

end
end krylov.Convergence
