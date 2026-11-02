import krylov.Convergence.SS1CenteredRate
import krylov.Convergence.SS1FPhysicalRate
import krylov.Convergence.WindowSourceGain
import krylov.Convergence.EuclideanWindowExecution
import krylov.Convergence.SS1FEuclideanPhysicalRate
import krylov.XR.LocalAlgorithmStationary

/-!
Article: main_krylov, cor:xrF, actual Euclidean XR-F full-window R-order.
Use: combine source-derived real memory activation and full chronological
execution with the physical SS1-F rate. The actual accepted trajectory,
its critical limit and its physical incoming gain are all supplied by the
literal algorithm; no output recurrence or successful phase is assumed.
Source: original G1--G4, genuine local C2,1 regularity and positive-root
normalization with sigma_H and LH_E*lambda_min^(-3/2).
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.XR krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The same original incoming gain is preserved when value correction
is enabled; the successful phase is derived from the selected-model source. -/
theorem euclidean_source_full_window_gain {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : EuclideanGrowthSource P f G H x₀ center bounds) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∀ᶠ k in atTop,∀ c : Fin n → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (fun j=>(euclideanAlgorithmRun P f G x₀ bounds j).point) k)) c‖^2 := by
  obtain ⟨K₁,hK₁⟩ := euclidean_source_full_observation_chronology P f G H x₀ center bounds D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.clean_phase hP
  filter_upwards [eventually_ge_atTop (max D.gainStart (max K₁ K₂))] with k hk c
  apply gain_chronological_records f G _ _ k (hK₁ k (by omega)) _ c
  rw [(hK₂ (k+n) (by omega)).1]
  exact D.gain (k+n) (by omega)


/-- A source-driven full-memory XR-F execution has the printed literal
improved one-gradient order in the true Hessian norm with the Euclidean split. All original memory gates,
full-window independence and stationarity are derived from its source. -/
theorem euclidean_source_full_XRF_physical_rorder (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : EuclideanGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hon : P.valuesEnabled=true) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (T₃ : EuclideanSpace ℝ (Fin (n+1)) → krylov.Functions.SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    {L₃ : ℝ≥0}
    (hT : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      HasFDerivAt (gradientHessian (centeredMetricHessian (metricCoordinates base hb) center H)) (T₃ z).form z)
    (hLip : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      ∀ w∈centeredMetricDomain (metricCoordinates base hb) center S,∀ h,‖h‖=1 →
      |(T₃ z).form h h h-(T₃ w).form h h h|≤(L₃:ℝ)*‖z-w‖) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      ((euclideanAlgorithmRun P f G x₀ bounds k).point-center)‖) (oneGradientRoot (n+1)) := by
  let x := fun k=>(euclideanAlgorithmRun P f G x₀ bounds k).point
  obtain ⟨K,hK⟩ := euclidean_source_full_eq_ss1FSequence P hon f G H x₀ center bounds D hP hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1FSequence f G ss1FEuclideanSplit seed j := hK j
  have hg₀ : G center=0 := by
    have hi := euclideanAlgorithmRun_initial_gradient_ne_zero P f G x₀ center bounds D.converges D.distinct
    obtain ⟨radius,hradius,L,hL,hf,hg⟩ := exists_local_gradient_data f G H center
      D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    have hc := algorithmInitialState_constants P hP f G x₀ bounds hi
    exact run_local_limit_stationary P (n+1) (euclideanAlgorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
      (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center radius hradius hf L hL hg D.converges
  have hconv : Tendsto (ss1FSequence f G ss1FEuclideanSplit seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1FSequence f G ss1FEuclideanSplit seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually
      (euclidean_source_full_window_gain P f G H x₀ center bounds D hP hmax)
    have hw (k : ℕ) : windowStep (n:=n+1) x (k+K)=windowStep (ss1FSequence f G ss1FEuclideanSplit seed) k := by
      funext i
      dsimp only [windowStep]
      rw [show k+K+i.val+1=K+(k+i.val+1) by omega,
        show k+K+i.val=K+(k+i.val) by omega,he,he]
    change ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep x (k+K))) c‖^2 at hh
    simpa only [hw] using hh
  have hlow (v) : D.mu*‖v‖^2≤ inner ℝ v (cgOperator base v) := by
    rw [←hbase]
    exact D.coercive v
  have hupp (v) : inner ℝ v (cgOperator base v)≤D.upper*‖v‖^2 := by
    rw [←hbase]
    calc
      _ ≤ ‖v‖*‖H center v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖*(D.upper*‖v‖) := mul_le_mul_of_nonneg_left
        ((H center).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right D.h_norm (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
  have hr := ss1FEuclideanSequence_centered_physical_rorder base hb f G H center S hS hc hn hH hbase hf hG hg₀
    T₃ hT hLip seed hconv D.mu_pos D.upper_pos D.sigma_pos hlow hupp hgain
  apply HasROrder.of_tail (zero_lt_one.trans (secantRoot_gt_one (n+1-1) 0)) K
  change HasROrder (fun j=>‖(metricCoordinates base hb) (x (K+j)-center)‖) _
  simpa only [he,oneGradientRoot] using hr

end
end krylov.Convergence
