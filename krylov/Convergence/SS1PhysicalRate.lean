import krylov.Convergence.WindowMetricExecution
import krylov.Convergence.WindowMetricRegularity
import krylov.Convergence.SS1Rate

/-!
Article: main_krylov, thm:Ip and thm:grow, physical SS1 normalization.
Use: obtain the literal R-order of the genuine physical recursive executor
from physical normalized-column independence and actual Hessian endpoints.
The canonical gain sigma*sqrt(mu/upper) and Hessian allowance
LH_E*mu^(-3/2) are derived, rather than inserted as source hypotheses.
Source: the positive Hessian root, the exact observed-model covariance,
and the proved delayed secant characteristic-order theorem.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Physical full-window independence gives the actual canonical
least-gain condition, with precisely the printed sigma_H. -/
theorem metric_full_window_leastGain (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hb : base.PosDef) (s : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ c : Fin (n+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2) :
    IsUnit (windowMatrix (unitWindow (fun i=>(metricCoordinates base hb) (s i)))).det ∧
      σ*Real.sqrt (mu/upper)≤leastGain
        (windowMatrix (unitWindow (fun i=>(metricCoordinates base hb) (s i)))) := by
  have hV := full_window_leastGain_of_gain (unitWindow s) hσ hgain
  have hs (i : Fin (n+1)) : s i≠0 := by
    intro hz
    apply windowMatrix_step_ne_zero (unitWindow s) hV.1 i
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  apply full_window_leastGain_of_gain _ (mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu)))
  intro c
  exact metric_window_gain base hb s hs hmu hu hσ.le hlower hupper hgain c

/-- The genuine SS1 executor has the printed one-gradient R-order in its
true Hessian norm. Only physical pair independence and primitive physical
Hessian bounds are assumed. -/
theorem ss1Sequence_physical_rorder
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=cgOperator base)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2) :
    HasROrder (fun k=>‖(metricCoordinates base hb) (ss1Sequence G seed k)‖)
      (oneGradientRoot (n+2)) := by
  let T := metricCoordinates base hb
  let Gh := coordinateGradient T G
  let Hh := coordinateDerivative T H
  let sh := fun i=>T (seed i)
  let xh := ss1Sequence Gh sh
  have hx (k : ℕ) : T (ss1Sequence G seed k)=xh k :=
    ss1Sequence_coordinate T (metricCoordinates_inverse_symmetric base hb) G seed k
  have hSh : Convex ℝ (T.symm ⁻¹' S) := hS.linear_preimage T.symm.toLinearMap
  have hzh : (0:EuclideanSpace ℝ (Fin (n+1)))∈T.symm ⁻¹' S := by
    simpa only [Set.mem_preimage,map_zero] using h₀
  have hnh : T.symm ⁻¹' S∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))) := by
    exact T.symm.continuous.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hnbhd)
  have hch : Tendsto xh atTop (𝓝 0) := by
    have hh := T.continuous.continuousAt.tendsto.comp hconv
    simpa only [map_zero,Function.comp_def,hx] using hh
  have hih : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))).det ∧
        σ*Real.sqrt (mu/upper)≤leastGain (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))) := by
    filter_upwards [hgain] with k hk
    have hh := metric_full_window_leastGain base hb (windowStep (ss1Sequence G seed) k)
      hmu hu hσ hlower hupper hk
    have he : (fun i : Fin (n+1)=>T (windowStep (ss1Sequence G seed) k i))=windowStep xh k := by
      funext i
      simp only [windowStep,map_sub,hx]
    rwa [he] at hh
  have hh := ss1Sequence_rorder Gh Hh (T.symm ⁻¹' S) hSh hzh hnh
    (metric_hessian_lipschitz_bound base hb H hH hmu hlower)
    (coordinateDerivative_metric_zero base hb H hH₀)
    (fun y hy=>coordinateGradient_hasFDerivAt T G H y (hG _ hy))
    (by simp only [Gh,coordinateGradient,map_zero,hG₀]) sh hch
    (mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu))) hih
  change HasROrder (fun k=>‖T (ss1Sequence G seed k)‖) _
  simpa only [hx] using hh

end
end krylov.Convergence
