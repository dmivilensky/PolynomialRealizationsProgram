import nesterov.Oracle.Envelope
import nesterov.Momentum.Execution
import nesterov.Momentum.Parameters
import nesterov.Stationary.Centering
import nesterov.Robust.TMM

/-! Momentum is an actual policy in the unrestricted oracle model: exactly
one gradient call per update, with the prescribed rest start. Its ordinary
uniform rate bounds the literal oracle rate on the unit-radius class. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology

section Execution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def responseState (β h : ℝ) : (n : ℕ)→Transcript E n→E×E
  | 0,_ => (0,0)
  | n+1,t =>
    let p := responseState β h n (Fin.init t)
    (p.2,p.2+β • (p.2-p.1)-h • (t (Fin.last n)).2.2)

def momentumPolicy (β τ h : ℝ) : Policy E where
  query := fun n t=>Momentum.query τ (responseState β h n t)
  output := fun n t=>(responseState β h n t).2

end Execution

section ActualExecution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem responseState_run (β τ h : ℝ) (f : E→ℝ) (n : ℕ) :
    responseState β h n ((momentumPolicy β τ h).run (firstOrderOracle f) n)=
      Momentum.state (gradient f) β τ h (0:E) 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hq : (momentumPolicy β τ h).query n ((momentumPolicy β τ h).run (firstOrderOracle f) n)=
        Momentum.query τ (Momentum.state (gradient f) β τ h (0:E) 0 n) :=
      congrArg (Momentum.query τ) ih
    simp only [Policy.run,responseState,Fin.init_snoc,Fin.snoc_last,ih,firstOrderOracle,hq]
    rfl

theorem momentumPolicy_result (β τ h : ℝ) (f : E→ℝ) (n : ℕ) :
    (momentumPolicy β τ h).result (firstOrderOracle f) n=
      Momentum.iterate (gradient f) β τ h (0:E) n := by
  change (responseState β h n ((momentumPolicy β τ h).run (firstOrderOracle f) n)).2=_
  rw [responseState_run]
  rfl

end ActualExecution

def momentumAlgorithm (β τ h : ℝ) : Algorithm := fun _ _=>momentumPolicy β τ h

theorem momentum_error_le_envelope (T : Momentum.Tuning) {μ : ℝ} {N d : ℕ}
    {f : Space d→ℝ} {xstar : Space d} (hf : Instance μ d f xstar) :
    ‖(momentumAlgorithm T.beta T.tau T.stepSize N d).result (firstOrderOracle f) N-xstar‖≤
      Real.sqrt 2*Rates.envelope (Momentum.method T.beta T.tau T.stepSize T.step_pos.ne') μ 1 N := by
  let M := Momentum.method T.beta T.tau T.stepSize T.step_pos.ne'
  let w := Momentum.history (gradient f) T.beta T.tau T.stepSize (0:Space d) 0
  have hw : M.IsTrajectory (gradient f) w :=
    Momentum.history_isTrajectory _ T.beta T.tau T.stepSize T.step_pos.ne' _ _
  have hmin : ∀ z,f xstar≤f z := (hf.1.minimizer_iff xstar).mpr hf.2.1
  have hb := Rates.original_stateNorm_le_envelope M hf.1 xstar hmin hw 0 N
  simp only [Nat.zero_add] at hb
  have hinit : M.stateNorm (fun j=>w j-xstar) 0=Real.sqrt 2*‖xstar‖ := by
    change Real.sqrt (∑ j : Fin 2,‖w (0+j)-xstar‖^2)=_
    simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.zero_add,w,
      Momentum.history_zero,Momentum.history_one,zero_sub,norm_neg]
    rw [←two_mul,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_sq (norm_nonneg _)]
  have hn := M.norm_le_stateNorm (fun j=>w j-xstar) N (1:Fin 2)
  rw [hinit] at hb
  change ‖(momentumPolicy T.beta T.tau T.stepSize).result (firstOrderOracle f) N-xstar‖≤_
  rw [momentumPolicy_result]
  change ‖w (N+1)-xstar‖≤_
  calc
    _≤M.stateNorm (fun j=>w j-xstar) N := hn
    _≤Rates.envelope M μ 1 N*(Real.sqrt 2*‖xstar‖) := hb
    _≤Rates.envelope M μ 1 N*Real.sqrt 2 := by
      apply mul_le_mul_of_nonneg_left _ (Rates.envelope_nonneg M μ 1 N)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf.2.2 (Real.sqrt_nonneg 2)
    _=_ := mul_comm _ _

theorem momentum_literalRate_le (T : Momentum.Tuning) {μ : ℝ} (hμ : 0<μ) (hμ1 : μ<1) :
    literalRate (momentumAlgorithm T.beta T.tau T.stepSize) μ≤
      ENNReal.ofReal (Momentum.momentumRate T.beta T.tau T.stepSize T.step_pos.ne' μ 1) := by
  let M := Momentum.method T.beta T.tau T.stepSize T.step_pos.ne'
  have hC : 0<Real.sqrt 2 := by positivity
  have ht := (Rates.tendsto_const_root hC).mul (Rates.tendsto_envelope_root M hμ hμ1)
  simp only [one_mul] at ht
  have hu : Tendsto (fun n : ℕ=>(ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ 1 n))^((n:ℝ)⁻¹))
      atTop (𝓝 (ENNReal.ofReal (Rates.rate M μ 1))) := by
    convert ENNReal.tendsto_ofReal ht using 1
    funext n
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC.le (Rates.envelope_nonneg M μ 1 n)) (by positivity),
      Real.mul_rpow hC.le (Rates.envelope_nonneg M μ 1 n)]
  have he (N : ℕ) : error (momentumAlgorithm T.beta T.tau T.stepSize) μ N≤
      ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ 1 N) := by
    apply iSup_le
    intro d
    apply iSup_le
    intro f
    apply iSup_le
    intro xstar
    apply iSup_le
    intro hf
    exact ENNReal.ofReal_le_ofReal (momentum_error_le_envelope T hf)
  have hp : ∀ᶠ N : ℕ in atTop,
      error (momentumAlgorithm T.beta T.tau T.stepSize) μ N^((N:ℝ)⁻¹)≤
        (ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ 1 N))^((N:ℝ)⁻¹) :=
    Eventually.of_forall (fun N=>ENNReal.rpow_le_rpow (he N) (by positivity))
  have hh := limsup_le_limsup hp (by isBoundedDefault) (by isBoundedDefault)
  rw [hu.limsup_eq] at hh
  exact hh

end
end nesterov.Oracle
