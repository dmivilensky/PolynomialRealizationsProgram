import krylov.Asymptotics.StepCoordinates
import krylov.ContinuumControl.Impulse

/-!
Article: main_krylov, apC:lem:step, exact one-step potential loss.
The drift and impulse integrals are defined on actual finite-string paths.
Their positivity, integrability and potential estimate are proved from the
constructed graph equation and exact state recurrence.
Source: the fundamental theorem of calculus and the proved finite-impulse
identity; no separate one-step-loss hypothesis is introduced.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- The true drift integrand, before its constant energy weight. -/
def driftCoeff (σ : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  S.p j / ((S.φ j + u * S.p j) * sqrt (σ (driftRatio S j u)))
/-- The true unfolded impulse integrand, before its variable energy weight. -/
def impulseCoeff (σ : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  S.φ (j + 1) * sqrt (σ (impulseRatio S j u)) / (S.p j + u * S.φ (j + 1))
/-- Actual drift integral in the source. -/
def driftIntegral (σ : ℝ → ℝ) (j : ℕ) : ℝ := ∫ u in 0..S.gap j, driftCoeff S σ j u
/-- Actual impulse integral in the source. -/
def impulseIntegral (σ : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ u in 0..S.mass (j + 1), impulseCoeff S σ j u

variable {γ : ℝ} {σ : ℝ → ℝ}
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
include hgraph

/-- Positive drift coefficients on the entire actual gap. -/
theorem driftCoeff_pos {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    0 < driftCoeff S σ j u := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hr : 1 ≤ driftRatio S j u := (S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu).1
  have hs := (hgraph _ hr).positive
  have hu₀ := hu.1
  dsimp [driftCoeff]
  exact div_pos (by linarith) (mul_pos (by positivity) (sqrt_pos.mpr hs))

/-- Positive impulse coefficients on the entire actual inserted mass. -/
theorem impulseCoeff_pos {j : ℕ} (hj : j < N) {u : ℝ}
    (hu : u ∈ Icc 0 (S.mass (j + 1))) : 0 < impulseCoeff S σ j u := by
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hp := (S.state_bounds j hj.le).2.1
  have hr : 1 ≤ impulseRatio S j u :=
    (S.ratio_ge_one (j + 1) (by omega)).trans (impulseRatio_bounds S hj hu).1
  have hu₀ := hu.1
  dsimp [impulseCoeff]
  exact div_pos (mul_pos (by linarith) (sqrt_pos.mpr (hgraph _ hr).positive)) (by positivity)

/-- Integrability of the actual drift follows from graph regularity. -/
theorem driftCoeff_continuousOn {j : ℕ} (hj : j < N) :
    ContinuousOn (driftCoeff S σ j) (uIcc 0 (S.gap j)) := by
  intro u hu
  have hu' : u ∈ Icc 0 (S.gap j) := uIcc_of_le (S.gap_pos j hj).le ▸ hu
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  have hu₀ := hu'.1
  have hφu : 0 < S.φ j + u * S.p j := by positivity
  have hr : 1 ≤ driftRatio S j u := (S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu').1
  have hcφ : ContinuousAt (fun u : ℝ ↦ S.φ j + u * S.p j) u := by fun_prop
  have hcr : ContinuousAt (driftRatio S j) u := by unfold driftRatio; fun_prop
  have hcs := (hgraph _ hr).differentiable.continuousAt.comp hcr
  exact (continuousAt_const.div (hcφ.mul hcs.sqrt)
    (mul_ne_zero hφu.ne' (sqrt_pos.mpr (hgraph _ hr).positive).ne')).continuousWithinAt

/-- Integrability of the actual impulse follows from graph regularity. -/
theorem impulseCoeff_continuousOn {j : ℕ} (hj : j < N) :
    ContinuousOn (impulseCoeff S σ j) (uIcc 0 (S.mass (j + 1))) := by
  intro u hu
  have hu' : u ∈ Icc 0 (S.mass (j + 1)) :=
    uIcc_of_le (S.mass_pos (j + 1) (by omega)).le ▸ hu
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  obtain ⟨_, hp, hK, _⟩ := S.state_bounds j hj.le
  have hu₀ := hu'.1
  have hp' : 0 < S.p j + u * S.φ (j + 1) := by positivity
  have hK' : 0 < S.K j + u * S.φ (j + 1) ^ 2 := by positivity
  have hr : 1 ≤ impulseRatio S j u :=
    (S.ratio_ge_one (j + 1) (by omega)).trans (impulseRatio_bounds S hj hu').1
  have hcp : ContinuousAt (fun u : ℝ ↦ S.p j + u * S.φ (j + 1)) u := by fun_prop
  have hcK : ContinuousAt (fun u : ℝ ↦ S.K j + u * S.φ (j + 1) ^ 2) u := by fun_prop
  have hcr : ContinuousAt (impulseRatio S j) u := (continuousAt_const.mul hcp).div hcK hK'.ne'
  have hcs := (hgraph _ hr).differentiable.continuousAt.comp hcr
  exact ((continuousAt_const.mul hcs.sqrt).div hcp hp'.ne').continuousWithinAt

/-- Every genuine positive gap has a positive drift integral. -/
theorem driftIntegral_pos {j : ℕ} (hj : j < N) : 0 < driftIntegral S σ j :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((driftCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume))
    (fun _ hu ↦ driftCoeff_pos S hgraph hj (Ioo_subset_Icc_self hu)) (S.gap_pos j hj)

/-- Every genuine positive mass has a positive impulse integral. -/
theorem impulseIntegral_pos {j : ℕ} (hj : j < N) : 0 < impulseIntegral S σ j :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((impulseCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume))
    (fun _ hu ↦ impulseCoeff_pos S hgraph hj (Ioo_subset_Icc_self hu))
    (S.mass_pos (j + 1) (by omega))

/-- Exact potential decrement along the actual free drift. -/
theorem drift_potential_decrement (hγ : γ ≠ 0) {j : ℕ} (hj : j < N) :
    stateValue γ σ (S.φ j) (S.p j) (S.K j) -
      stateValue γ σ (S.φ (j + 1)) (S.p j) (S.K j) =
        1 / 2 * S.K j ^ (-γ) * driftIntegral S σ j := by
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  have hd (u : ℝ) (hu : u ∈ uIcc 0 (S.gap j)) :
      HasDerivAt (fun u ↦ stateValue γ σ (S.φ j + u * S.p j) (S.p j) (S.K j))
        (-(S.K j ^ (-γ) / 2) * driftCoeff S σ j u) u := by
    have hu' : u ∈ Icc 0 (S.gap j) := uIcc_of_le (S.gap_pos j hj).le ▸ hu
    have hu₀ := hu'.1
    have hφu : 0 < S.φ j + u * S.p j := by positivity
    have hr : 1 ≤ driftRatio S j u := (S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu').1
    have hg := hgraph _ hr
    have h := hasDerivAt_stateValue (dx := 1) (dm := 0)
      (φ := fun u ↦ S.φ j + u * S.p j) (p := fun _ ↦ S.p j) (K := fun _ ↦ S.K j)
      hγ hφu.ne' (show S.p j ≠ 0 by linarith) (show 0 < S.K j by linarith)
      hg.positive hg.differentiable.hasDerivAt hg.equation
      (by simpa only [mul_one, one_mul, id_eq] using ((hasDerivAt_id u).mul_const (S.p j)).const_add (S.φ j))
      (by simpa only [mul_zero] using hasDerivAt_const u (S.p j))
      (by simpa only [mul_zero] using hasDerivAt_const u (S.K j))
    convert! h using 1
    simp only [driftCoeff, driftRatio, mul_zero, add_zero, mul_one]
    ring
  have hi := ((driftCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume)).const_mul (-(S.K j ^ (-γ) / 2))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at h
  simp only [zero_mul, add_zero] at h
  rw [← S.φ_succ] at h
  change -(S.K j ^ (-γ) / 2) * driftIntegral S σ j = _ at h
  linarith

/-- A real positive power gives the endpoint lower weight throughout the
actual impulse; this is the only inequality in the one-step loss estimate. -/
theorem impulseLoss_ge (hγ : 0 ≤ γ) {j : ℕ} (hj : j < N) :
    1 / 2 * S.K (j + 1) ^ (-γ) * impulseIntegral S σ j ≤
      impulseLoss γ σ (S.φ (j + 1)) (S.p j) (S.K j) (S.mass (j + 1)) := by
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  obtain ⟨_, hp, hK, _⟩ := S.state_bounds j hj.le
  have hmass := S.mass_pos (j + 1) (by omega)
  have hg : ∀ u ∈ Icc 0 (S.mass (j + 1)), FeedbackGraphAt γ σ (impulseRatio S j u) := by
    intro u hu
    exact hgraph _ ((S.ratio_ge_one (j + 1) (by omega)).trans (impulseRatio_bounds S hj hu).1)
  have hi := (impulseCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume)
  have hi' := continuousOn_impulse_massLossRate (show 0 < S.φ (j + 1) by linarith)
    (show 0 < S.p j by linarith) (show 0 < S.K j by linarith) hmass.le hg
  have hcmp := intervalIntegral.integral_mono_on hmass.le (hi.const_mul (S.K (j + 1) ^ (-γ)))
    (hi'.intervalIntegrable (μ := volume)) (fun u hu ↦ ?_)
  · rw [intervalIntegral.integral_const_mul] at hcmp
    dsimp [impulseLoss]
    change 1 / 2 * S.K (j + 1) ^ (-γ) * impulseIntegral S σ j ≤ _
    dsimp [impulseIntegral] at *
    nlinarith only [hcmp]
  · have hu₀ := hu.1
    have hKu : 0 < S.K j + u * S.φ (j + 1) ^ 2 := by positivity
    have hKle : S.K j + u * S.φ (j + 1) ^ 2 ≤ S.K (j + 1) := by
      rw [S.K_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sq_nonneg (S.φ (j + 1)))]
    have hweight := Real.rpow_le_rpow_of_nonpos hKu hKle (neg_nonpos.mpr hγ)
    have hcoeff := (impulseCoeff_pos S hgraph hj hu).le
    have hmul := mul_le_mul_of_nonneg_right hweight hcoeff
    simpa only [massLossRate, impulseCoeff, impulseRatio, mul_div_assoc, mul_assoc] using hmul

/-- The source one-step lower potential estimate for the actual integrals. -/
theorem step_potential_ge (hγ : 0 < γ) {j : ℕ} (hj : j < N) :
    1 / 2 * (S.K j ^ (-γ) * driftIntegral S σ j +
      S.K (j + 1) ^ (-γ) * impulseIntegral S σ j) ≤
      stateValue γ σ (S.φ j) (S.p j) (S.K j) -
        stateValue γ σ (S.φ (j + 1)) (S.p (j + 1)) (S.K (j + 1)) := by
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  obtain ⟨_, hp, hK, _⟩ := S.state_bounds j hj.le
  have hm := S.mass_pos (j + 1) (by omega)
  have hg : ∀ u ∈ Icc 0 (S.mass (j + 1)), FeedbackGraphAt γ σ (impulseRatio S j u) := by
    intro u hu
    exact hgraph _ ((S.ratio_ge_one (j + 1) (by omega)).trans (impulseRatio_bounds S hj hu).1)
  have hd := drift_potential_decrement S hgraph hγ.ne' hj
  have hi := impulse_potential_decrement hγ.ne' (show 0 < S.φ (j + 1) by linarith)
    (show 0 < S.p j by linarith) (show 0 < S.K j by linarith) hm.le hg
  rw [← S.p_succ, ← S.K_succ] at hi
  have hbound := impulseLoss_ge S hgraph hγ.le hj
  linarith

end DiscreteString
end
end krylov.Asymptotics
