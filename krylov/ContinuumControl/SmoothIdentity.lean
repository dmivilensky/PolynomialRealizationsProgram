import krylov.ContinuumControl.Potential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: main_krylov, apC:eq:fundamental, absolutely continuous specialization.
Use: integrate the actual Bellman derivative for a differentiable string state.
The hypotheses are state equations and the separating-graph ODE, rather than
an assumed potential identity. General continuous-BV strings require a separate
chain-rule argument; the theorem here does not claim that extension.
Source: the fundamental theorem of calculus in mathlib.
-/

namespace krylov.ContinuumControl
noncomputable section
open Set MeasureTheory

/-- The differential equations of an absolutely continuous string at a point.
Article: main_krylov, apC:eq:state, with density dM/dx = v². -/
structure SmoothStringAt (φ p K v : ℝ → ℝ) (x : ℝ) : Prop where
  φ_pos : 0 < φ x
  p_pos : 0 < p x
  K_pos : 0 < K x
  φ_deriv : HasDerivAt φ (p x) x
  p_deriv : HasDerivAt p (φ x * v x ^ 2) x
  K_deriv : HasDerivAt K (φ x ^ 2 * v x ^ 2) x

/-- The actual graph differential equation at one positive state ratio.
The multiplied form includes the equilibrium without a singular division.
Article: main_krylov, apC:lem:fund. -/
structure FeedbackGraphAt (γ : ℝ) (σ : ℝ → ℝ) (r : ℝ) : Prop where
  positive : 0 < σ r
  differentiable : DifferentiableAt ℝ σ r
  equation : r * deriv σ r * (σ r + 1 - r) = 2 * σ r * (σ r - 1 - γ * r)

/-- Collected type reward per unit physical length.
Article: main_krylov, apC:eq:fundamental, first integrand. -/
def rewardDensity (γ : ℝ) (K v : ℝ → ℝ) (x : ℝ) : ℝ :=
  K x ^ (-γ) * v x

/-- Square loss per unit length, before its factor 1/2.
Article: main_krylov, apC:eq:fundamental, second integrand. -/
def squareLossDensity (γ : ℝ) (σ φ p K v : ℝ → ℝ) (x : ℝ) : ℝ :=
  K x ^ (-γ) *
    (Real.sqrt (p x / (φ x * Real.sqrt (σ (φ x * p x / K x)))) -
      v x * Real.sqrt (φ x * Real.sqrt (σ (φ x * p x / K x)) / p x)) ^ 2

/-- Genuine pointwise derivative in reward-minus-loss form.
Article: main_krylov, apC:lem:fund, smooth part. -/
theorem hasDerivAt_stateValue_reward_loss {γ x : ℝ} {σ φ p K v : ℝ → ℝ}
    (hγ : γ ≠ 0) (hstate : SmoothStringAt φ p K v x)
    (hgraph : FeedbackGraphAt γ σ (φ x * p x / K x)) :
    HasDerivAt (fun u => stateValue γ σ (φ u) (p u) (K u))
      (-(rewardDensity γ K v x + 1 / 2 * squareLossDensity γ σ φ p K v x)) x := by
  have hd := hasDerivAt_stateValue (dx := 1) (dm := v x ^ 2) hγ
    (ne_of_gt hstate.φ_pos) (ne_of_gt hstate.p_pos) hstate.K_pos hgraph.positive
    hgraph.differentiable.hasDerivAt hgraph.equation
    (by simpa only [mul_one] using hstate.φ_deriv) hstate.p_deriv hstate.K_deriv
  convert hd using 1
  dsimp only [rewardDensity, squareLossDensity]
  have hs := drift_mass_square hstate.φ_pos hstate.p_pos
    (Real.sqrt_pos.2 hgraph.positive) (v x)
  linear_combination (K x ^ (-γ)) * hs

/-- The full integral identity for smooth strings. Integrability is explicit
and can be supplied, for example, by continuity on the compact interval.
Article: main_krylov, apC:eq:fundamental, no singular mass. -/
theorem smooth_fundamental_identity {γ a b : ℝ} {σ φ p K v : ℝ → ℝ}
    (hγ : γ ≠ 0)
    (hstate : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x)
    (hgraph : ∀ x ∈ uIcc a b, FeedbackGraphAt γ σ (φ x * p x / K x))
    (hreward : IntervalIntegrable (rewardDensity γ K v) volume a b)
    (hloss : IntervalIntegrable (squareLossDensity γ σ φ p K v) volume a b) :
    stateValue γ σ (φ a) (p a) (K a) - stateValue γ σ (φ b) (p b) (K b) =
      (∫ x in a..b, rewardDensity γ K v x) +
        1 / 2 * ∫ x in a..b, squareLossDensity γ σ φ p K v x := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_stateValue_reward_loss hγ (hstate x hx) (hgraph x hx))
    ((hreward.add (hloss.const_mul (1 / 2))).neg)
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_add hreward (hloss.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- Smooth strings cannot exceed the initial value; the terminal value and
square loss remain as explicit nonnegative deficits.
Article: main_krylov, proof of thm:value, upper certificate. -/
theorem smooth_reward_le_initial_value {γ a b : ℝ} {σ φ p K v : ℝ → ℝ}
    (hγ : 0 < γ) (hab : a ≤ b)
    (hstate : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x)
    (hgraph : ∀ x ∈ uIcc a b, FeedbackGraphAt γ σ (φ x * p x / K x))
    (hdom : K b ≤ φ b * p b)
    (hreward : IntervalIntegrable (rewardDensity γ K v) volume a b)
    (hloss : IntervalIntegrable (squareLossDensity γ σ φ p K v) volume a b) :
    (∫ x in a..b, rewardDensity γ K v x) ≤ stateValue γ σ (φ a) (p a) (K a) := by
  have hf := smooth_fundamental_identity (ne_of_gt hγ) hstate hgraph hreward hloss
  have hb := hstate b (right_mem_uIcc)
  have hgb := hgraph b (right_mem_uIcc)
  have hterm := stateValue_pos hγ hb.K_pos hdom hgb.positive
  have hsquare : 0 ≤ ∫ x in a..b, squareLossDensity γ σ φ p K v x := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg (hstate x (Icc_subset_uIcc hx)).K_pos.le _)
      (sq_nonneg _)
  linarith

/-- Strictly positive potential weight cannot hide a nonzero square loss.
Article: main_krylov, proof of thm:value, feedback equality condition. -/
theorem squareLossDensity_eq_zero_iff {γ x : ℝ} {σ φ p K v : ℝ → ℝ}
    (hφ : 0 < φ x) (hp : 0 < p x) (hK : 0 < K x)
    (hs : 0 < σ (φ x * p x / K x)) :
    squareLossDensity γ σ φ p K v x = 0 ↔
      v x = p x / (φ x * Real.sqrt (σ (φ x * p x / K x))) := by
  unfold squareLossDensity
  rw [mul_eq_zero, or_iff_right (ne_of_gt (Real.rpow_pos_of_pos hK _))]
  exact square_zero_iff_feedback hφ hp (Real.sqrt_pos.2 hs) (v x)

/-- Equality in the smooth finite-horizon certificate forces the actual
feedback density almost everywhere, and conversely that density attains it.
Article: main_krylov, proof of thm:value, loss-zero characterization. -/
theorem smooth_equality_iff_feedback_ae {γ a b : ℝ} {σ φ p K v : ℝ → ℝ}
    (hγ : γ ≠ 0) (hab : a ≤ b)
    (hstate : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x)
    (hgraph : ∀ x ∈ uIcc a b, FeedbackGraphAt γ σ (φ x * p x / K x))
    (hreward : IntervalIntegrable (rewardDensity γ K v) volume a b)
    (hloss : IntervalIntegrable (squareLossDensity γ σ φ p K v) volume a b) :
    (∫ x in a..b, rewardDensity γ K v x) =
      stateValue γ σ (φ a) (p a) (K a) - stateValue γ σ (φ b) (p b) (K b) ↔
      ∀ᵐ x ∂volume.restrict (Ioc a b),
        v x = p x / (φ x * Real.sqrt (σ (φ x * p x / K x))) := by
  have hf := smooth_fundamental_identity hγ hstate hgraph hreward hloss
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] squareLossDensity γ σ φ p K v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg
      (Real.rpow_nonneg (hstate x (Icc_subset_uIcc (Ioc_subset_Icc_self hx))).K_pos.le _)
      (sq_nonneg _)
  have hz := intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab hnonneg hloss
  have hpoint : ∀ᵐ x ∂volume.restrict (Ioc a b),
      (squareLossDensity γ σ φ p K v x = 0 ↔
        v x = p x / (φ x * Real.sqrt (σ (φ x * p x / K x)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx' : x ∈ uIcc a b := Icc_subset_uIcc (Ioc_subset_Icc_self hx)
    exact squareLossDensity_eq_zero_iff (hstate x hx').φ_pos (hstate x hx').p_pos
      (hstate x hx').K_pos (hgraph x hx').positive
  constructor
  · intro he
    have hi : (∫ x in a..b, squareLossDensity γ σ φ p K v x) = 0 := by linarith
    filter_upwards [hz.1 hi, hpoint] with x hx hp
    exact hp.1 hx
  · intro he
    have hzero : squareLossDensity γ σ φ p K v =ᵐ[volume.restrict (Ioc a b)] 0 := by
      filter_upwards [he, hpoint] with x hx hp
      exact hp.2 hx
    have hi := hz.2 hzero
    linarith

/-- Once the globally constructed feedback path has vanishing terminal
potential, its accumulated reward tends to the initial candidate value.
Article: main_krylov, proof of thm:value, attainment step. -/
theorem feedback_reward_tendsto_initial_value {γ a : ℝ} {σ φ p K v : ℝ → ℝ}
    (hγ : γ ≠ 0)
    (hstate : ∀ x, a ≤ x → SmoothStringAt φ p K v x)
    (hgraph : ∀ x, a ≤ x → FeedbackGraphAt γ σ (φ x * p x / K x))
    (hfeedback : ∀ x, a ≤ x →
      v x = p x / (φ x * Real.sqrt (σ (φ x * p x / K x))))
    (hreward : ∀ b, a ≤ b → IntervalIntegrable (rewardDensity γ K v) volume a b)
    (hterminal : Filter.Tendsto (fun b => stateValue γ σ (φ b) (p b) (K b))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun b => ∫ x in a..b, rewardDensity γ K v x) Filter.atTop
      (nhds (stateValue γ σ (φ a) (p a) (K a))) := by
  have heq : (fun b => ∫ x in a..b, rewardDensity γ K v x) =ᶠ[Filter.atTop]
      (fun b => stateValue γ σ (φ a) (p a) (K a) -
        stateValue γ σ (φ b) (p b) (K b)) := by
    filter_upwards [Filter.eventually_ge_atTop a] with b hb
    have hstate' : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x := by
      intro x hx
      exact hstate x ((uIcc_of_le hb ▸ hx).1)
    have hgraph' : ∀ x ∈ uIcc a b, FeedbackGraphAt γ σ (φ x * p x / K x) := by
      intro x hx
      exact hgraph x ((uIcc_of_le hb ▸ hx).1)
    have hloss : ∀ x ∈ uIcc a b, squareLossDensity γ σ φ p K v x = 0 := by
      intro x hx
      exact (squareLossDensity_eq_zero_iff (hstate' x hx).φ_pos (hstate' x hx).p_pos
        (hstate' x hx).K_pos (hgraph' x hx).positive).2
          (hfeedback x ((uIcc_of_le hb ▸ hx).1))
    have hint : IntervalIntegrable (squareLossDensity γ σ φ p K v) volume a b :=
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b).congr
        (fun x hx => (hloss x (uIoc_subset_uIcc hx)).symm)
    have hf := smooth_fundamental_identity hγ hstate' hgraph' (hreward b hb) hint
    have hi : (∫ x in a..b, squareLossDensity γ σ φ p K v x) = 0 := by
      calc
        _ = ∫ _x in a..b, (0 : ℝ) := intervalIntegral.integral_congr hloss
        _ = 0 := by simp
    linarith
  have ht := (tendsto_const_nhds (x := stateValue γ σ (φ a) (p a) (K a))).sub hterminal
  rw [sub_zero] at ht
  exact ht.congr' heq.symm

end
end krylov.ContinuumControl
