import krylov.XR.PracticalGrowthDictionary
import krylov.Convergence.WindowNativeSharp

/-!
# Physical local rates of practical XR and XR-F

Article Theorem 7.3 (`thm:grow`) and Corollary 7.4 (`cor:xrF`). The rates
below concern the literal accepted practical trajectory in the true Hessian
norm. Their full-window recursions, stationarity, physical gain and value
gates are derived from the primitive source, not supplied as hypotheses.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
/-- The actual accepted limit of literal XR is critical under the
original local C² hypothesis, with no added global regularity assumption. -/
theorem practicalRun_local_limit_stationary {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center)) :
    G center = 0 := by
  by_cases hzero : G x₀ = 0
  · have hr k : practicalRun P f G x₀ k = algorithmInitialState P f G x₀ none :=
      run_stationary P n (practicalModel P) f G _ hzero k
    have hconst : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 x₀) := by
      simpa only [hr, algorithmInitialState, initialState] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
    have heq : x₀ = center := tendsto_nhds_unique hconst hconv
    rw [← heq]
    exact hzero
  · obtain ⟨radius, hradius, L, hL, hf, hg⟩ := exists_local_gradient_data f G H center hF hG hH
    have hc := algorithmInitialState_constants P hP f G x₀ none hzero
    rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
    exact run_local_limit_stationary P n (practicalModel P) f G
      (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hsig (hsig₁.trans (by norm_num))
      center radius hradius hf L hL hg hconv

end
end krylov.XR

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.XR krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- A source-driven full-memory XR execution has the printed literal
one-gradient order in the true Hessian norm. All original memory gates,
full-window independence and stationarity are derived from its source. -/
theorem practical_source_full_XR_physical_rorder (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      ((practicalRun P f G x₀ k).point-center)‖) (oneGradientRoot (n+2)) := by
  let x := fun k=>(practicalRun P f G x₀ k).point
  obtain ⟨K,hK⟩ := practical_source_full_eq_ss1Sequence P f G H x₀ center D hP hoff hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1Sequence G seed j := hK j
  have hg₀ : G center=0 := practicalRun_local_limit_stationary P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.converges
  have hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually
      (practical_source_full_window_gain P f G H x₀ center D hP hmax)
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


/-- A source-driven full-memory XR-F execution has the printed literal
improved one-gradient order in the true Hessian norm. All original memory gates,
full-window independence and stationarity are derived from its source. -/
theorem practical_source_full_XRF_physical_rorder (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
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
      ((practicalRun P f G x₀ k).point-center)‖) (oneGradientRoot (n+1)) := by
  let x := fun k=>(practicalRun P f G x₀ k).point
  obtain ⟨K,hK⟩ := practical_source_full_eq_ss1FSequence P hon f G H x₀ center D hP hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1FSequence f G (ss1FObservedSplit G) seed j := hK j
  have hg₀ : G center=0 := practicalRun_local_limit_stationary P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.converges
  have hconv : Tendsto (ss1FSequence f G (ss1FObservedSplit G) seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1FSequence f G (ss1FObservedSplit G) seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually
      (practical_source_full_window_gain P f G H x₀ center D hP hmax)
    have hw (k : ℕ) : windowStep (n:=n+1) x (k+K)=windowStep (ss1FSequence f G (ss1FObservedSplit G) seed) k := by
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
  have hr := ss1FObservedSequence_centered_physical_rorder base hb f G H center S hS hc hn hH hbase hf hG hg₀
    T₃ hT hLip seed hconv D.mu_pos D.upper_pos D.sigma_pos hlow hupp hgain
  apply HasROrder.of_tail (zero_lt_one.trans (secantRoot_gt_one (n+1-1) 0)) K
  change HasROrder (fun j=>‖(metricCoordinates base hb) (x (K+j)-center)‖) _
  simpa only [he,oneGradientRoot] using hr


/-- Original selected G1--G4 imply the sharp true-Hstar delayed error
product for the actual values-off full-capacity executor. -/
theorem practical_source_full_XR_sharp_product (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) :
    let T:=metricCoordinates base hb
    let e:=fun k=>‖T ((practicalRun P f G x₀ k).point-center)‖
    let sigmaH:=D.sigma*Real.sqrt (D.mu/D.upper)
    let LH:=(L:ℝ)*D.mu^(-(3/2:ℝ))
    ∀ η : ℝ,0<η → ∀ᶠ k in atTop,e (k+1)≤(LH/(2*sigmaH^2)+η)*e k*e (k-(n+1)) := by
  let x := fun k=>(practicalRun P f G x₀ k).point
  obtain ⟨K,hK⟩ := practical_source_full_eq_ss1Sequence P f G H x₀ center D hP hoff hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1Sequence G seed j := hK j
  have hg₀ : G center=0 := practicalRun_local_limit_stationary P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.converges
  have hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually
      (practical_source_full_window_gain P f G H x₀ center D hP hmax)
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

  obtain ⟨hlow,_hsuper,⟨theta,htheta,hbound⟩,_hrate⟩:=ss1Sequence_physical_oldest_source
    base hb G H center S hS hc hn hH hbase hG hg₀ seed hconv
    D.mu_pos D.upper_pos D.sigma_pos hlow hupp hgain
  let sigmaH:=D.sigma*Real.sqrt (D.mu/D.upper)
  let LH:=(L:ℝ)*D.mu^(-(3/2:ℝ))
  have hσH : 0<sigmaH:=mul_pos D.sigma_pos (Real.sqrt_pos.mpr (div_pos D.mu_pos D.upper_pos))
  have hLH : 0≤LH:=mul_nonneg L.coe_nonneg (Real.rpow_nonneg D.mu_pos.le _)
  dsimp only
  intro η hη
  have hcoef : ∀ᶠ j in atTop,(1+theta j)*(LH/(2*sigmaH^2))≤LH/(2*sigmaH^2)+η := by
    have ht : Tendsto (fun j=>(1+theta j)*(LH/(2*sigmaH^2))) atTop (𝓝 (LH/(2*sigmaH^2))) := by
      have hh:=((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).add htheta).mul_const (LH/(2*sigmaH^2))
      simpa only [add_zero,one_mul] using hh
    exact (ht.eventually (gt_mem_nhds (by linarith))).mono fun _ h=>h.le
  have hthetaPos : ∀ᶠ j in atTop,0≤1+theta j := by
    filter_upwards [htheta.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0))] with j hj
    linarith
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hbound.and (hlow.and (hcoef.and hthetaPos)))
  filter_upwards [eventually_ge_atTop (K+N+n+1)] with k hk
  let j:=k-(K+n+1)
  have hj : N≤j:=by dsimp only [j];omega
  have hjnext : K+(j+n+2)=k+1:=by dsimp only [j];omega
  have hjcurrent : K+(j+n+1)=k:=by dsimp only [j];omega
  have hjold : K+j=k-(n+1):=by dsimp only [j];omega
  have hbnd:=(hN j hj).1
  have hd:=(hN j hj).2.1
  have hcj:=(hN j hj).2.2.1
  have hpos:=(hN j hj).2.2.2
  have hdiv : LH/(2*(slidingOldestDistance (fun i=>metricCoordinates base hb (ss1Sequence G seed i-center)) j)^2)≤
      LH/(2*sigmaH^2) := by
    apply div_le_div_of_nonneg_left hLH (by positivity : 0<2*sigmaH^2)
    have hsq : sigmaH^2≤(slidingOldestDistance (fun i=>metricCoordinates base hb (ss1Sequence G seed i-center)) j)^2:=
      (sq_le_sq₀ hσH.le (hσH.le.trans hd)).mpr hd
    linarith only [hsq]
  have hcoeff : (1+theta j)*LH/(2*(slidingOldestDistance
      (fun i=>metricCoordinates base hb (ss1Sequence G seed i-center)) j)^2)≤LH/(2*sigmaH^2)+η := by
    simpa only [mul_div_assoc] using (mul_le_mul_of_nonneg_left hdiv hpos).trans hcj
  have hh:=hbnd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (norm_nonneg _))
  dsimp only at hh
  change ‖metricCoordinates base hb (x (k+1)-center)‖≤_
  rw [←he,←he,←he] at hh
  simpa only [hjnext,hjcurrent,hjold] using hh

end
end krylov.Convergence
