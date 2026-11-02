import krylov.Convergence.WindowNativeSharp
import krylov.XR.GrowthOriginalTransition
import krylov.LinearAlgebra.SpectralEndpoints
import krylov.LinearAlgebra.SpectralUpperForm

/-!
Article: main_krylov, thm:grow and thm:XR, sharp original-floor product.
Use: keep the original physical independence and true spectral endpoints
through the source-derived full-memory phase. The auxiliary weakened G4
certificates do not weaken the printed asymptotic error constant.
Source: the original SS1 oldest-pair estimate, the genuine chronological
execution dictionary, and the real finite-dimensional spectral theorem.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.XR krylov.Methods krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The actual selected-source phase preserves an independently given
physical gain and true Hessian bounds in the sharp error coefficient. -/
theorem selected_source_full_XR_sharp_product_of_physical_gain (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : SelectedGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (mu upper sigma : ℝ) (hmu : 0<mu) (hupper : 0<upper) (hsigma : 0<sigma)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupperForm : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hwindowGain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep
        (fun j=>(algorithmRun P f G x₀ bounds j).point) k)) c‖^2) :
    let T:=metricCoordinates base hb
    let e:=fun k=>‖T ((algorithmRun P f G x₀ bounds k).point-center)‖
    let sigmaH:=sigma*Real.sqrt (mu/upper)
    let LH:=(L:ℝ)*mu^(-(3/2:ℝ))
    ∀ η : ℝ,0<η → ∀ᶠ k in atTop,e (k+1)≤(LH/(2*sigmaH^2)+η)*e k*e (k-(n+1)) := by
  let x := fun k=>(algorithmRun P f G x₀ bounds k).point
  obtain ⟨K,hK⟩ := selected_source_full_eq_ss1Sequence P f G H x₀ center bounds D hP hoff hmax
  let seed := fun i : Fin (n+2)=>x (K+i.val)
  have he (j : ℕ) : x (K+j)=ss1Sequence G seed j := hK j
  have hg₀ : G center=0 := algorithmRun_local_limit_stationary P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.converges
  have hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center) := by
    have hh := D.converges.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun j=>x (j+K)) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm _ K,he] using hh
  have hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2 := by
    have hh := (tendsto_add_atTop_nat K).eventually hwindowGain
    have hw (k : ℕ) : windowStep (n:=n+1) x (k+K)=windowStep (ss1Sequence G seed) k := by
      funext i
      dsimp only [windowStep]
      rw [show k+K+i.val+1=K+(k+i.val+1) by omega,
        show k+K+i.val=K+(k+i.val) by omega,he,he]
    change ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep x (k+K))) c‖^2 at hh
    simpa only [hw] using hh

  obtain ⟨hlow,_hsuper,⟨theta,htheta,hbound⟩,_hrate⟩:=ss1Sequence_physical_oldest_source
    base hb G H center S hS hc hn hH hbase hG hg₀ seed hconv
    hmu hupper hsigma hlower hupperForm hgain
  let sigmaH:=sigma*Real.sqrt (mu/upper)
  let LH:=(L:ℝ)*mu^(-(3/2:ℝ))
  have hσH : 0<sigmaH:=mul_pos hsigma (Real.sqrt_pos.mpr (div_pos hmu hupper))
  have hLH : 0≤LH:=mul_nonneg L.coe_nonneg (Real.rpow_nonneg hmu.le _)
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



/-- The original running-upper source has the literal sharp physical
product with the true minimum/maximum eigenvalues and the original G2
gain. No weakened activation certificate enters its error coefficient. -/
theorem original_floor_XR_physical_sharp_product (P : Parameters) (hP : P.Valid (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef) (hcenter : H center = cgOperator base)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (hupperMargin : ∃ k, ‖H center‖ <
      boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds)
    (hoff : P.valuesEnabled = false) (hmax : P.maximumCapacity = n+1) :
    ∃ a > 0, ∃ gain > 0, ∃ b > 0, ∃ ell > 0, ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant (n+1) a gain b trialUpper) →
      (dimensionNormConstant (n+1) a gain b ell <
        (algorithmInitialState P f G x₀ bounds).normConstant) →
      let lo:=spectralLower base hbase.1
      let hi:=spectralUpper base hbase.1
      let LH:=(L:ℝ)*lo^(-(3/2:ℝ))
      let sigmaH:=sigma*Real.sqrt (lo/hi)
      let e:=fun k=>‖metricCoordinates base hbase
        ((algorithmRun P f G x₀ bounds k).point-center)‖
      ∀ η : ℝ,0<η → ∀ᶠ k in atTop,
        e (k+1)≤(LH/(2*sigmaH^2)+η)*e k*e (k-(n+1)) := by
  let lo:=spectralLower base hbase.1
  let hi:=spectralUpper base hbase.1
  have hlo : 0<lo:=spectralLower_pos base hbase
  have hhi : 0<hi:=spectralUpper_pos base hbase
  have hlow (v : EuclideanSpace ℝ (Fin (n+1))) :
      lo*‖v‖^2≤ inner ℝ v (cgOperator base v) :=
    spectral_lower_form base hbase.1 (spectralLower_le base hbase.1) v
  have hupp (v : EuclideanSpace ℝ (Fin (n+1))) :
      inner ℝ v (cgOperator base v)≤hi*‖v‖^2 :=
    spectral_upper_form base hbase.1 (le_spectralUpper base hbase.1) v
  have hpositive (v) : lo*‖v‖^2≤ inner ℝ v (H center v) := by
    rw [hcenter]
    exact hlow v
  obtain ⟨a,ha,gain,hgainPos,b,hb,ell,hell,trialUpper,htrialUpper,hsource⟩ :=
    algorithmRun_original_floor_transition P hP f G H x₀ center bounds
      hF hG lo sigma hlo hsigma hpositive hconv hne K₀ hgain hprobeGain
      base hbase hcenter radius hradius L hLip hupperMargin
  refine ⟨a,ha,gain,hgainPos,b,hb,ell,hell,trialUpper,htrialUpper,?_⟩
  intro hG₄₁ hG₄₂
  obtain ⟨⟨D⟩,_⟩ := hsource hG₄₁ hG₄₂
  obtain ⟨rG,hrG,hderiv⟩:=Metric.eventually_nhds_iff.mp hG
  let r:=min radius rG
  have hr : 0<r:=lt_min hradius hrG
  have hsub : ball center r⊆ball center radius:=ball_subset_ball (min_le_left _ _)
  have hGS : ∀ z∈ball center r,HasFDerivAt G (H z) z := by
    intro z hz
    exact hderiv ((ball_subset_ball (min_le_right radius rG)) hz)
  have hfullGain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep
        (fun j=>(algorithmRun P f G x₀ bounds j).point) k)) c‖^2 := by
    obtain ⟨K₁,hK₁⟩:=selected_source_full_observation_chronology P f G H x₀ center bounds D hP hmax
    obtain ⟨K₂,hK₂⟩:=D.clean_phase hP
    filter_upwards [eventually_ge_atTop (max K₀ (max K₁ K₂))] with k hk c
    apply gain_chronological_records f G _ _ k (hK₁ k (by omega)) _ c
    rw [(hK₂ (k+(n+1)) (by omega)).1]
    exact hgain (k+(n+1)) (by omega)
  exact selected_source_full_XR_sharp_product_of_physical_gain P f G H x₀ center bounds
    D hP hoff hmax base hbase hcenter (ball center r) (convex_ball center r)
    (mem_ball_self hr) (isOpen_ball.mem_nhds (mem_ball_self hr)) (hLip.mono hsub) hGS
    lo hi sigma hlo hhi hsigma hlow hupp hfullGain

end
end krylov.Convergence
