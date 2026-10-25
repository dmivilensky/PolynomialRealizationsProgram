import polyak.Realization.ExplicitSpiral.CertifiedExecution
import polyak.Threshold.Cycle
import polyak.Threshold.Results

/-!
Article: Theorem threshold, the quantitative examples in exactly three real dimensions.
Use: the fixed Y=2 construction supplies the same function and start on every horizon,
including convergence to a nonconstant three-cycle at the critical condition number.
-/

namespace polyak.Results
noncomputable section
open Filter Dynamics Realization
open scoped Topology

private abbrev E := WithLp 2 (ℂ × ℝ)

/-- Article: the unit planar critical cycle in the explicit Y=2 model. -/
def criticalCycle (N : ℕ) : E :=
  WithLp.toLp 2 ((ExplicitSpiral.radialWave 1)^N, 0)

private theorem radialWave_one : ExplicitSpiral.radialWave 1 =
    Waves.z 0 (Real.arccos (Spiral.cosine 0)) := by
  have h := (ExplicitSpiral.radial_spiral_data (by norm_num : (0 : ℝ)<1)).2.1
  simpa only [ExplicitSpiral.radialWave, Real.log_one] using
    congrArg (fun c => Waves.z (Real.log 1) (Real.arccos c)) h.symm

theorem criticalCycle_period (N : ℕ) : criticalCycle (N+3)=criticalCycle N := by
  simp only [criticalCycle, radialWave_one, Spiral.critical_wave_period]

theorem criticalCycle_norm (N : ℕ) : ‖criticalCycle N‖=1 := by
  have hz := (ExplicitSpiral.radial_wave_coordinates (by norm_num : (0 : ℝ)<1)).1
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [criticalCycle, norm_pow, hz]

theorem criticalCycle_one_ne_zero : criticalCycle 1≠criticalCycle 0 := by
  intro h
  have hh := congrArg (fun v : E => v.fst) h
  simp only [criticalCycle, WithLp.toLp_fst, pow_one, pow_zero, radialWave_one] at hh
  exact Spiral.critical_wave_ne_one hh

/-- Article: the prescribed startup coordinate vanishes while the planar three-cycle remains. -/
theorem explicit_startup_tendsto_cycle {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    Tendsto (fun N => ‖ExplicitSpiral.position (ExplicitSpiral.radialWave 1) q (some N)-
      criticalCycle N‖) atTop (𝓝 0) := by
  have hr : Tendsto (response 0 (q^2)) atTop (𝓝 0) := by
    apply response_tendsto_zero (sq_nonneg q) (by nlinarith)
    simp only [abs_zero]
    positivity
  have he (N : ℕ) :
      ‖ExplicitSpiral.position (ExplicitSpiral.radialWave 1) q (some N)-criticalCycle N‖=
        |2*response 0 (q^2) N| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(ExplicitSpiral.radialWave 1)^N-(ExplicitSpiral.radialWave 1)^N‖^2+
      ‖2*response (0+(2*q)*0) (q^2) N-0‖^2=|2*response 0 (q^2) N|^2
    simp
  simpa only [he, mul_zero, abs_zero] using (hr.const_mul 2).abs

/-- Article: at κ=κc one fixed objective and the Y=2 start have both the exact
1/√5 lower bound on every horizon and a nonconstant unit three-cycle limit. -/
theorem exists_critical_three_cycle_quantitative {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hc : L/μ=Threshold.criticalKappa) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, ‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧
        (∀ N : ℕ, (1/Real.sqrt 5)*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) ∧
        ∃ p : ℕ → EuclideanSpace ℝ (Fin 3),
          (∀ N,p (N+3)=p N) ∧ p 1≠p 0 ∧ (∀ N,‖p N‖=1) ∧
          Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-p N‖)
            atTop (𝓝 0) := by
  have hq : polyakQ μ L=Threshold.criticalQ := by
    rw [polyakQ_eq_conditionQ hμ hL]
    exact (Threshold.conditionQ_eq_critical_iff (by rw [hc]; exact Threshold.one_lt_criticalKappa)).mpr hc
  have hF : Spiral.spiralPolynomial 1 (polyakQ μ L)=0 := by
    rw [hq, ← Spiral.factor_critical]
    exact (Spiral.factor_spec Threshold.criticalQ_pos Threshold.criticalQ_lt_one).2
  obtain ⟨ψ,hψ,hexec⟩ := ExplicitSpiral.exists_certified_execution hμ hL
    (by norm_num : (0 : ℝ)<1) hF
  let F := denormalizeFunction μ L ψ
  have hF : CenteredSmoothStronglyConvex μ L F := hψ.denormalize hμ hL
  let Q := (stdOrthonormalBasis ℝ E).repr.toLinearIsometry
  let G := extendObjective μ L Q F
  have hG : CenteredSmoothStronglyConvex μ L G := hF.extendObjective Q
  let x₀ := Q (ExplicitSpiral.position (ExplicitSpiral.radialWave 1) (polyakQ μ L) (some 0))
  have hxnorm : ‖x₀‖=Real.sqrt 5 := by
    rw [Q.norm_map]
    exact ExplicitSpiral.norm_position_zero _ _
  have hxne : x₀≠0 := norm_pos_iff.mp (by rw [hxnorm]; positivity)
  have hmodel (N : ℕ) :
      iterate (gradient G) (polyakAlpha μ L) (polyakBeta μ L) x₀ N=
        Q (ExplicitSpiral.position (ExplicitSpiral.radialWave 1) (polyakQ μ L) (some N)) := by
    rw [iterate_embedding Q (gradient F) (gradient G)
      (gradient_extendObjective_embed hF.toSmoothStronglyConvex Q)]
    exact congrArg Q (hexec N)
  have hdim : Module.finrank ℝ E=3 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq, Module.finrank_prod,
      Complex.finrank_real_complex, Module.finrank_self]
  have hresult : ∃ f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀, ‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧
        (∀ N : ℕ, (1/Real.sqrt 5)*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) ∧
        ∃ p : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          (∀ N,p (N+3)=p N) ∧ p 1≠p 0 ∧ (∀ N,‖p N‖=1) ∧
          Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-p N‖)
            atTop (𝓝 0) := by
    refine ⟨G,hG,x₀,hxnorm,hxne,fun N => ?_,fun N => Q (criticalCycle N),
      fun N => congrArg Q (criticalCycle_period N),
      fun h => criticalCycle_one_ne_zero (Q.injective h),fun N => ?_,?_⟩
    · rw [hxnorm, hmodel N, Q.norm_map]
      have hs : Real.sqrt 5≠0 := by positivity
      rw [one_div_mul_cancel hs]
      simpa only [one_pow] using ExplicitSpiral.norm_mode_le_position
        (ExplicitSpiral.radialWave 1) (polyakQ μ L) N
        |>.trans_eq' (by simp [(ExplicitSpiral.radial_wave_coordinates (by norm_num : (0 : ℝ)<1)).1])
    · rw [Q.norm_map, criticalCycle_norm]
    · convert explicit_startup_tendsto_cycle (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) using 1
      funext N
      rw [hmodel N, ← Q.map_sub, Q.norm_map]
  rwa [hdim] at hresult

/-- Article: above κc the explicit 1/√5 example diverges exponentially,
for the original from-rest Polyak executor and one fixed objective in ℝ³. -/
theorem exists_exponential_divergence_quantitative {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hc : Threshold.criticalKappa<L/μ) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, ‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧
        (∀ N : ℕ, (1/Real.sqrt 5)*(Spiral.factor (polyakQ μ L))^N*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) ∧
        1<Spiral.factor (polyakQ μ L) ∧
        Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) atTop atTop := by
  obtain ⟨f,hf,x₀,hn,hx,hbound⟩ := ExplicitSpiral.exists_spiral_lower hμ hL
  have hq : Threshold.criticalQ<polyakQ μ L := by
    rw [polyakQ_eq_conditionQ hμ hL]
    exact (Threshold.critical_lt_conditionQ_iff (by linarith [Threshold.one_lt_criticalKappa])).mpr hc
  have hfac := Spiral.one_lt_factor (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hq
  refine ⟨f,hf,x₀,hn,hx,hbound,hfac,?_⟩
  have hd : 0<(1/Real.sqrt 5)*‖x₀‖ := mul_pos (by positivity) (norm_pos_iff.mpr hx)
  apply tendsto_atTop_mono _ ((tendsto_pow_atTop_atTop_of_one_lt hfac).const_mul_atTop hd)
  intro N
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound N

end
end polyak.Results
