import krylov.Convergence.SS1CenteredRate
import krylov.Convergence.WindowSourceGain
import krylov.XR.LocalAlgorithmStationary

/-!
Article: main_krylov, thm:grow, actual XR full-window R-order.
Use: combine source-derived real memory activation and full chronological
execution with the physical SS1 rate. The actual accepted trajectory,
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

/-- A source-driven full-memory XR execution has the printed literal
one-gradient order in the true Hessian norm. All original memory gates,
full-window independence and stationarity are derived from its source. -/
theorem source_full_XR_physical_rorder (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : GrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      ((algorithmRun P f G x₀ bounds k).point-center)‖) (oneGradientRoot (n+2)) := by
  let x := fun k=>(algorithmRun P f G x₀ bounds k).point
  obtain ⟨K,hK⟩ := source_full_eq_ss1Sequence P f G H x₀ center bounds D hP hoff hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1Sequence G seed j := hK j
  have hg₀ : G center=0 := algorithmRun_local_limit_stationary P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.converges
  have hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually
      (source_full_window_gain P f G H x₀ center bounds D hP hoff hmax)
    have hw (k : ℕ) : windowStep (n:=n+1) x (k+K)=windowStep (ss1Sequence G seed) k := by
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
  have hr := ss1Sequence_centered_physical_rorder base hb G H center S hS hc hn hH hbase hG hg₀
    seed hconv D.mu_pos D.upper_pos D.sigma_pos hlow hupp hgain
  apply HasROrder.of_tail (zero_lt_one.trans (secantRoot_gt_one (n+2-1) 0)) K
  change HasROrder (fun j=>‖(metricCoordinates base hb) (x (K+j)-center)‖) _
  simpa only [he,oneGradientRoot] using hr

end
end krylov.Convergence
