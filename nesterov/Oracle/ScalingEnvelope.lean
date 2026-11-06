import nesterov.Oracle.MomentumPolicy

/-! Arbitrary smoothness and strong-convexity constants in the literal
oracle worst-case error, including the actual momentum policy dictionary. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology

def InstanceAt (μ L : ℝ) (d : ℕ) (f : Space d→ℝ) (xstar : Space d) : Prop :=
  polyak.SmoothStronglyConvex μ L f ∧ gradient f xstar=0 ∧ ‖xstar‖≤1

def errorAt (A : Algorithm) (μ L : ℝ) (N : ℕ) : ENNReal :=
  ⨆ (d : ℕ) (f : Space d→ℝ) (xstar : Space d) (_h : InstanceAt μ L d f xstar),
    ENNReal.ofReal ‖(A N d).result (firstOrderOracle f) N-xstar‖

def literalRateAt (A : Algorithm) (μ L : ℝ) : ENNReal :=
  limsup (fun N : ℕ=>errorAt A μ L N^((N:ℝ)⁻¹)) atTop

@[simp] theorem errorAt_one (A : Algorithm) (q : ℝ) (N : ℕ) : errorAt A q 1 N=error A q N := rfl
@[simp] theorem literalRateAt_one (A : Algorithm) (q : ℝ) : literalRateAt A q 1=literalRate A q := rfl

theorem instanceAt_error_le (A : Algorithm) {μ L : ℝ} {N d : ℕ}
    {f : Space d→ℝ} {xstar : Space d} (hf : InstanceAt μ L d f xstar) :
    ENNReal.ofReal ‖(A N d).result (firstOrderOracle f) N-xstar‖≤errorAt A μ L N :=
  le_iSup_of_le d (le_iSup_of_le f (le_iSup_of_le xstar (le_iSup_of_le hf le_rfl)))

theorem literalRateAt_ge_of_hard_instances (A : Algorithm) {μ L C ρ : ℝ}
    (hC : 0<C) (hρ : 0<ρ)
    (h : ∀ N : ℕ,∃ (d : ℕ) (f : Space d→ℝ) (xstar : Space d),
      InstanceAt μ L d f xstar ∧ C*ρ^N≤‖(A N d).result (firstOrderOracle f) N-xstar‖) :
    ENNReal.ofReal ρ≤literalRateAt A μ L := by
  have hp : ∀ᶠ N : ℕ in atTop,
      (ENNReal.ofReal (C*ρ^N))^((N:ℝ)⁻¹)≤errorAt A μ L N^((N:ℝ)⁻¹) := by
    apply Eventually.of_forall
    intro N
    obtain ⟨d,f,xstar,hf,hl⟩ := h N
    exact ENNReal.rpow_le_rpow ((ENNReal.ofReal_le_ofReal hl).trans (instanceAt_error_le A hf)) (by positivity)
  have hh := limsup_le_limsup hp (by isBoundedDefault) (by isBoundedDefault)
  rw [(geometric_root_tendsto hC hρ).limsup_eq] at hh
  exact hh

theorem momentum_errorAt_le_envelope (T : Momentum.Tuning) {μ L : ℝ} {N d : ℕ}
    {f : Space d→ℝ} {xstar : Space d} (hf : InstanceAt μ L d f xstar) :
    ‖(momentumAlgorithm T.beta T.tau T.stepSize N d).result (firstOrderOracle f) N-xstar‖≤
      Real.sqrt 2*Rates.envelope (Momentum.method T.beta T.tau T.stepSize T.step_pos.ne') μ L N := by
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
    _≤Rates.envelope M μ L N*(Real.sqrt 2*‖xstar‖) := hb
    _≤Rates.envelope M μ L N*Real.sqrt 2 := by
      apply mul_le_mul_of_nonneg_left _ (Rates.envelope_nonneg M μ L N)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf.2.2 (Real.sqrt_nonneg 2)
    _=_ := mul_comm _ _

theorem momentum_literalRateAt_le (T : Momentum.Tuning) {μ L : ℝ} (hμ : 0<μ) (hμ1 : μ<L) :
    literalRateAt (momentumAlgorithm T.beta T.tau T.stepSize) μ L≤
      ENNReal.ofReal (Momentum.momentumRate T.beta T.tau T.stepSize T.step_pos.ne' μ L) := by
  let M := Momentum.method T.beta T.tau T.stepSize T.step_pos.ne'
  have hC : 0<Real.sqrt 2 := by positivity
  have ht := (Rates.tendsto_const_root hC).mul (Rates.tendsto_envelope_root M hμ hμ1)
  simp only [one_mul] at ht
  have hu : Tendsto (fun n : ℕ=>(ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ L n))^((n:ℝ)⁻¹))
      atTop (𝓝 (ENNReal.ofReal (Rates.rate M μ L))) := by
    convert ENNReal.tendsto_ofReal ht using 1
    funext n
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC.le (Rates.envelope_nonneg M μ L n)) (by positivity),
      Real.mul_rpow hC.le (Rates.envelope_nonneg M μ L n)]
  have he (N : ℕ) : errorAt (momentumAlgorithm T.beta T.tau T.stepSize) μ L N≤
      ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ L N) := by
    apply iSup_le
    intro d
    apply iSup_le
    intro f
    apply iSup_le
    intro xstar
    apply iSup_le
    intro hf
    exact ENNReal.ofReal_le_ofReal (momentum_errorAt_le_envelope T hf)
  have hp : ∀ᶠ N : ℕ in atTop,
      errorAt (momentumAlgorithm T.beta T.tau T.stepSize) μ L N^((N:ℝ)⁻¹)≤
        (ENNReal.ofReal (Real.sqrt 2*Rates.envelope M μ L N))^((N:ℝ)⁻¹) :=
    Eventually.of_forall (fun N=>ENNReal.rpow_le_rpow (he N) (by positivity))
  have hh := limsup_le_limsup hp (by isBoundedDefault) (by isBoundedDefault)
  rw [hu.limsup_eq] at hh
  exact hh

end
end nesterov.Oracle
