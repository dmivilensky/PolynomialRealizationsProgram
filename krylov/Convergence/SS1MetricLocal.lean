import krylov.Convergence.SS1DeterminantLocal
import krylov.Convergence.SS1PhysicalOldest
import krylov.Convergence.SlidingMetricSource

/-!
Article: main_krylov, lem:ss1-local, original physical determinant criterion.
Use: derive an actual common initial radius and convergence of the literal
physical SS1 executor from its original determinant-separated normalized
Hstar-metric windows. Convergence is a conclusion, not an input.
Source: exact complete-execution metric covariance and the proved invariant
ball/compact determinant argument for the canonical sequential method.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The genuine local sequential secant theorem in physical coordinates.
One initial Hstar-radius works for every actual starting history with the
original uniform normalized determinant separation. -/
theorem ss1_local_physical_determinant_convergence
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1))) (S : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hS : Convex ℝ S) (hn : S∈𝓝 center)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S) (hbase : H center=cgOperator base)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    {mu σ₀ : ℝ} (hmu : 0<mu) (hσ₀ : 0<σ₀)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v)) :
    let T:=metricCoordinates base hb
    ∃ r : ℝ,0<r ∧∀ seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ i,‖T (seed i-center)‖≤r) →
      (∀ k,σ₀≤|(windowMatrix (unitWindow (windowStep (n:=n+1)
        (fun j=>T (ss1Sequence G seed j-center)) k))).det|) →
      Tendsto (ss1Sequence G seed) atTop (𝓝 center) ∧
      ((fun k=>T (ss1Sequence G seed (k+1)-center))=o[atTop]
        (fun k=>‖T (ss1Sequence G seed k-center)‖)) ∧
      HasROrder (fun k=>‖T (ss1Sequence G seed k-center)‖) (oneGradientRoot (n+2)) := by
  let T:=metricCoordinates base hb
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  let Sh:=centeredMetricDomain T center S
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  have hSh : Convex ℝ Sh:=centeredMetricDomain_convex T center hS
  have hnh : Sh∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))):=centeredMetricDomain_mem_nhds T center hn
  obtain ⟨R,hR,hRad⟩:=local_source_closedBall_radius Sh hnh L
  have hHh : LipschitzOnWith L Hh Sh:=centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _:=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hGh z (hz : z∈Sh) : HasFDerivAt Gh (Hh z) z :=
    centeredMetricGradient_hasFDerivAt T center G H z (hG _ hz)
  have hGh₀ : Gh 0=0:=by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  obtain ⟨r,hr,_hrR,hlocal⟩:=ss1_local_determinant_convergence Gh Hh Sh hSh hHh hH₀ hGh hGh₀
    hR hσ₀ (hRad R hR le_rfl).1
  refine ⟨r,hr,fun seed hseed hdet=>?_⟩
  let sh:=fun i=>T (seed i-center)
  have he (k : ℕ) : T (ss1Sequence G seed k-center)=ss1Sequence Gh sh k := by
    rw [ss1Sequence_translate]
    exact ss1Sequence_coordinate T (metricCoordinates_inverse_symmetric base hb) _ _ k
  have hfun : (fun k=>T (ss1Sequence G seed k-center))=ss1Sequence Gh sh:=funext he
  have hc:=hlocal sh hseed (by simpa only [←hfun] using hdet)
  refine ⟨?_,?_,?_⟩
  · have hp (k : ℕ) : center+T.symm (ss1Sequence Gh sh k)=ss1Sequence G seed k := by
      rw [←he,T.symm_apply_apply]
      abel_nf
    have ht:=(tendsto_const_nhds : Tendsto (fun _ : ℕ=>center) atTop (𝓝 center)).add
      ((T.symm.continuous.tendsto 0).comp hc.1)
    simpa only [Function.comp_def,map_zero,add_zero,hp] using ht
  · change (fun k=>T (ss1Sequence G seed (k+1)-center))=o[atTop](fun k=>‖T (ss1Sequence G seed k-center)‖)
    simpa only [he] using hc.2.1
  · change HasROrder (fun k=>‖T (ss1Sequence G seed k-center)‖) _
    simpa only [he] using hc.2.2

end
end krylov.Convergence
