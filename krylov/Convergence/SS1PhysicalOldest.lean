import krylov.Convergence.SS1PrintedOldest
import krylov.Convergence.SS1CenteredRate
import krylov.Convergence.WindowCenteredCoordinates
import krylov.Convergence.SlidingMetricExecution

/-!
Article: main_krylov, thm:Ip, full SS1 physical oldest coefficient.
Use: transfer the genuine entire observed SS1 execution, derive sigma_H
from physical unit-column independence, and retain the original actual
oldest distance with the exact LH/2 coefficient. Source: actual endpoint
translation, true positive-root coordinates and the proved canonical
oldest-pair theorem, including the zero-Lipschitz case.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- Actual observed SS1, at an arbitrary physical nondegenerate critical
limit, satisfies every printed secant-rate conclusion in the true Hstar
norm. All canonical gains and Hessian allowances are derived. -/
theorem ss1Sequence_physical_oldest_source
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1))) (S : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hS : Convex ℝ S) (hc : center∈S) (hn : S∈𝓝 center)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S) (hbase : H center=cgOperator base)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤
      ‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2) :
    let T:=metricCoordinates base hb
    let z:=fun k=>T (ss1Sequence G seed k-center)
    let LH:=(LE:ℝ)*mu^(-(3/2:ℝ))
    (∀ᶠ k in atTop,σ*Real.sqrt (mu/upper)≤slidingOldestDistance z k) ∧
    ((fun k=>z (k+1))=o[atTop](fun k=>‖z k‖)) ∧
    (∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖z (k+n+2)‖≤(1+theta k)*LH/(2*(slidingOldestDistance z k)^2)*‖z (k+n+1)‖*‖z k‖) ∧
    HasROrder (fun k=>‖z k‖) (oneGradientRoot (n+2)) := by
  let T:=metricCoordinates base hb
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  let Sh:=centeredMetricDomain T center S
  let sh:=fun i=>T (seed i-center)
  let xh:=ss1Sequence Gh sh
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  have hLc : (L:ℝ)=(LE:ℝ)*mu^(-(3/2:ℝ)):=Real.coe_toNNReal _
    (mul_nonneg LE.coe_nonneg (Real.rpow_nonneg hmu.le _))
  have he (k : ℕ) : T (ss1Sequence G seed k-center)=xh k := by
    rw [ss1Sequence_translate]
    exact ss1Sequence_coordinate T (metricCoordinates_inverse_symmetric base hb) _ _ k
  have hch : Tendsto xh atTop (𝓝 0) := by
    have hx : Tendsto (fun k=>ss1Sequence G seed k-center) atTop (𝓝 0) := by simpa only [sub_self] using hconv.sub_const center
    have hh:=(T.continuous.tendsto 0).comp hx
    simpa only [Function.comp_def,map_zero,he] using hh
  have hSh : Convex ℝ Sh:=centeredMetricDomain_convex T center hS
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈Sh := by
    simpa only [Sh,centeredMetricDomain,Set.mem_preimage,map_zero,add_zero] using hc
  have hnh : Sh∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))):=centeredMetricDomain_mem_nhds T center hn
  have hHh : LipschitzOnWith L Hh Sh:=centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _ :=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hGh z (hz : z∈Sh) : HasFDerivAt Gh (Hh z) z :=
    centeredMetricGradient_hasFDerivAt T center G H z (hG _ hz)
  have hGh₀ : Gh 0=0 := by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  have hσH : 0<σ*Real.sqrt (mu/upper):=mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu))
  have hind : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))).det ∧
      σ*Real.sqrt (mu/upper)≤leastGain (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))) := by
    filter_upwards [hgain] with k hk
    have hh:=metric_full_window_leastGain base hb (windowStep (ss1Sequence G seed) k) hmu hu hσ hlower hupper hk
    have hs : (fun i : Fin (n+1)=>T (windowStep (ss1Sequence G seed) k i))=windowStep xh k := by
      have hh:=centered_metric_windowStep (n:=n+1) T center (ss1Sequence G seed) k
      have hfuneq : (fun j=>T (ss1Sequence G seed j-center))=xh:=funext he
      rw [hfuneq] at hh
      exact hh.symm
    rwa [hs] at hh
  have hlow : ∀ᶠ k in atTop,σ*Real.sqrt (mu/upper)≤slidingOldestDistance xh k := by
    filter_upwards [hind] with k hk
    exact hk.2.trans (oldest_distance_leastGain _ hk.1)
  have hsuper:=ss1Sequence_superlinear Gh Hh Sh hSh h₀ hnh hHh hH₀ hGh hGh₀ sh hch hσH hind
  obtain ⟨theta,ht,hbound⟩:=ss1Sequence_printed_oldest_bound Gh Hh Sh hSh h₀ hnh hHh hH₀ hGh hGh₀ sh hch hσH hind
  have hfun : (fun k=>metricCoordinates base hb (ss1Sequence G seed k-center))=ss1Sequence Gh sh:=funext he
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [xh,←hfun] using hlow
  · simpa only [xh,←hfun] using hsuper
  · refine ⟨theta,ht,?_⟩
    filter_upwards [hbound] with k hk
    rw [hLc] at hk
    simpa only [xh,←hfun,mul_div_assoc] using hk
  · simpa only [xh,←hfun] using ss1Sequence_rorder Gh Hh Sh hSh h₀ hnh hHh hH₀ hGh hGh₀ sh hch hσH hind

end
end krylov.Convergence
