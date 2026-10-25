import polyak.Threshold.Lower
import polyak.Spiral.Cycle

/-!
Article: Theorem threshold, the critical trajectory converges to a three-cycle.
Use: retain the true initialized gradient iteration and a nonconstant period-three
limiting sequence in exactly three real dimensions.
Proof: the planar critical wave has period three; the explicit Polyak startup
coordinate tends to zero. A real orthonormal basis transports the entire model.
-/

noncomputable section

open Filter
open scoped Topology

namespace polyak.Threshold

open Spectral Waves Dynamics Realization

/-- Article: the planar singleton wave used by the critical example. -/
def criticalMode : Option ℕ → EuclideanSpace ℂ (Fin 1) :=
  finitePosition (fun _ => (1 : NNReal)) (fun _ => Spiral.atom 0) 0

/-- Article: the real three-dimensional Hilbert model before choosing coordinates. -/
abbrev CriticalSpace := WithLp 2 (EuclideanSpace ℂ (Fin 1) × ℝ)

/-- Article: the limiting planar three-cycle with zero added coordinate. -/
def criticalCycle (N : ℕ) : CriticalSpace := WithLp.toLp 2 (criticalMode (some N),0)

/-- Article: the cycle is periodic with period three. -/
theorem criticalCycle_period (N : ℕ) : criticalCycle (N+3)=criticalCycle N := by
  unfold criticalCycle criticalMode
  rw [Spiral.finitePosition_period]

/-- Article: the cycle has unit radius. -/
theorem criticalCycle_norm (N : ℕ) : ‖criticalCycle N‖=1 := by
  have hm : ‖criticalMode (some N)‖=1 := by
    have h := norm_finitePosition (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom 0)
      (by simp) 0 N
    simpa only [criticalMode,mul_zero,Real.exp_zero] using h
  have hs : ‖criticalCycle N‖^2=(1 : ℝ)^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [criticalCycle,WithLp.toLp_fst,WithLp.toLp_snd,hm,norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hs

/-- Article: the limiting cycle is not a stationary point. -/
theorem criticalCycle_one_ne_zero : criticalCycle 1 ≠ criticalCycle 0 := by
  intro he
  have hf := congrArg (fun v : CriticalSpace => v.fst 0) he
  change criticalMode (some 1) 0=criticalMode (some 0) 0 at hf
  simp only [criticalMode,finitePosition_apply,NNReal.coe_one,Real.sqrt_one,
    one_smul,pow_one,pow_zero] at hf
  exact Spiral.critical_wave_ne_one hf

/-- Article: only the added coordinate remains after subtracting the critical cycle. -/
theorem startup_distance_to_cycle (q Y : ℝ) (N : ℕ) :
    ‖startupPosition criticalMode 0 (2*q) (q^2) 0 Y (some N)-criticalCycle N‖ =
      |Y*response 0 (q^2) N| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖criticalMode (some N)-criticalMode (some N)‖^2+
    ‖Y*response (0+(2*q)*0) (q^2) N-0‖^2=|Y*response 0 (q^2) N|^2
  simp only [mul_zero,zero_add,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),
    sub_zero,Real.norm_eq_abs]


/-- Article: the decaying explicit startup coordinate yields convergence to the cycle. -/
theorem startup_tendsto_cycle {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (Y : ℝ) :
    Tendsto (fun N => ‖startupPosition criticalMode 0 (2*q) (q^2) 0 Y (some N)-criticalCycle N‖)
      atTop (𝓝 0) := by
  have hr : Tendsto (response 0 (q^2)) atTop (𝓝 0) := by
    apply response_tendsto_zero (sq_nonneg q) (by nlinarith)
    simp only [abs_zero]
    positivity
  simpa only [startup_distance_to_cycle,mul_zero,abs_zero] using (hr.const_mul Y).abs

/-- Article: the critical three-cycle is approached by a true from-rest source trajectory. -/
theorem exists_critical_cycle_model {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : polyakQ μ L=criticalQ) :
    ∃ f : CriticalSpace → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀ ≠ 0 ∧
        Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-
          criticalCycle N‖) atTop (𝓝 0) := by
  have hfeas : Feasible (0-Real.log (polyakQ μ L)) 0
      (finiteSpectrum (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom 0) (by simp)) 0 := by
    rw [Spiral.finiteSpectrum_one_eq,hc,log_criticalQ]
    simpa only [sub_neg_eq_add,zero_add] using Spiral.critical_feasible
  obtain ⟨Y,ψ,hY,hψ,hmodel⟩ := exists_polyak_startup_model hμ hL
    (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom 0) (by simp) hfeas
    (fun ht => by linarith)
  let f := denormalizeFunction μ L ψ
  let x₀ := startupPosition criticalMode 0 (2*polyakQ μ L) (polyakQ μ L^2) 0 Y (some 0)
  have hf : CenteredSmoothStronglyConvex μ L f := hψ.denormalize hμ hL
  have hnorm : 1 ≤ ‖x₀‖ := by
    have hh := norm_le_startupPosition criticalMode 0 (2*polyakQ μ L) (polyakQ μ L^2) 0 Y 0
    have hm := norm_finitePosition (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom 0)
      (by simp) 0 0
    have hm' : ‖criticalMode (some 0)‖=1 := by
      simpa only [criticalMode,mul_zero,Real.exp_zero] using hm
    rw [hm'] at hh
    exact hh
  refine ⟨f,hf,x₀,norm_pos_iff.mp (by linarith),?_⟩
  have hlim := startup_tendsto_cycle (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) Y
  convert hlim using 1
  funext N
  dsimp only [f,x₀,criticalMode]
  rw [hmodel N]

/-- Article: the critical three-cycle example in exactly ℝ³, with one fixed source function and start. -/
theorem exists_critical_three_cycle {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : polyakQ μ L=criticalQ) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀ ≠ 0 ∧ ∃ p : ℕ → EuclideanSpace ℝ (Fin 3),
        (∀ N,p (N+3)=p N) ∧ p 1 ≠ p 0 ∧ (∀ N,‖p N‖=1) ∧
        Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-p N‖)
          atTop (𝓝 0) := by
  obtain ⟨f,hf,x₀,hx,hlim⟩ := exists_critical_cycle_model hμ hL hc
  let Q := (stdOrthonormalBasis ℝ CriticalSpace).repr.toLinearIsometry
  let g := extendObjective μ L Q f
  have hg : CenteredSmoothStronglyConvex μ L g := hf.extendObjective Q
  have hdim : Module.finrank ℝ CriticalSpace=3 := by
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℂ (Fin 1) × ℝ)).finrank_eq,
      Module.finrank_prod,finiteMixture_real_finrank,Module.finrank_self]
    norm_num
  have hresult : ∃ g : EuclideanSpace ℝ (Fin (Module.finrank ℝ CriticalSpace)) → ℝ,
      CenteredSmoothStronglyConvex μ L g ∧
      ∃ y₀,y₀ ≠ 0 ∧ ∃ p : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ CriticalSpace)),
        (∀ N,p (N+3)=p N) ∧ p 1 ≠ p 0 ∧ (∀ N,‖p N‖=1) ∧
        Tendsto (fun N => ‖iterate (gradient g) (polyakAlpha μ L) (polyakBeta μ L) y₀ N-p N‖)
          atTop (𝓝 0) := by
    refine ⟨g,hg,Q x₀,fun hh => hx (Q.injective (hh.trans (Q.map_zero).symm)),
      fun N => Q (criticalCycle N),fun N => congrArg Q (criticalCycle_period N),
      fun hh => criticalCycle_one_ne_zero (Q.injective hh),fun N => ?_,?_⟩
    · rw [Q.norm_map,criticalCycle_norm]
    · convert hlim using 1
      funext N
      rw [iterate_embedding Q (gradient f) (gradient g)
        (gradient_extendObjective_embed hf.toSmoothStronglyConvex Q),← Q.map_sub,Q.norm_map]
  rwa [hdim] at hresult

end polyak.Threshold
