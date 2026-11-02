import krylov.Asymptotics.LogSlope

/-!
Article: main_krylov, apC:lem:B and the averaging proof of apC:lem:step.
Use: integrate the actual derivative estimate to obtain monotonicity and
multiplicative log-Lipschitz control of `sqrt σ` on all physical ratios.
Source: Lagrange's mean value theorem in logarithmic coordinates.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Set
open scoped Topology

/-- Logarithmic feedback in logarithmic ratio coordinates. -/
def logControl (σ : ℝ → ℝ) (x : ℝ) : ℝ := log (σ (exp x)) / 2

/-- Exact derivative after both logarithmic coordinate changes. -/
theorem logControl_hasDerivAt {σ : ℝ → ℝ} {x : ℝ}
    (hs : 0 < σ (exp x)) (hd : DifferentiableAt ℝ σ (exp x)) :
    HasDerivAt (logControl σ) (logSlope σ (exp x)) x := by
  convert ((hd.hasDerivAt.comp x (Real.hasDerivAt_exp x)).log hs.ne').div_const 2 using 1
  · rfl
  · dsimp [logSlope]
    ring

/-- The derivative bound gives the source's exact finite log-growth estimate. -/
theorem log_sqrt_growth {σ : ℝ → ℝ} {B a b : ℝ}
    (hs : ∀ r ≥ 1, 0 < σ r)
    (hd : ∀ r ≥ 1, DifferentiableAt ℝ σ r)
    (hb : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ log (sqrt (σ b)) - log (sqrt (σ a)) ∧
      log (sqrt (σ b)) - log (sqrt (σ a)) ≤ B * log (b / a) := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := hapos.trans_le hab
  have hdF (x : ℝ) (hx : x ∈ Ici 0) :
      HasDerivAt (logControl σ) (logSlope σ (exp x)) x :=
    logControl_hasDerivAt (hs _ (one_le_exp_iff.mpr hx)) (hd _ (one_le_exp_iff.mpr hx))
  have hcF : ContinuousOn (logControl σ) (Ici 0) := fun x hx ↦
    (hdF x hx).continuousAt.continuousWithinAt
  have hdfF : DifferentiableOn ℝ (logControl σ) (interior (Ici 0)) := fun x hx ↦
    (hdF x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hl := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv hcF hdfF
    (fun x hx ↦ by
      rw [(hdF x (interior_subset hx)).deriv]
      exact (hb _ (one_le_exp_iff.mpr (interior_subset hx))).1)
    (log a) (log_nonneg ha) (log b) (log_nonneg (ha.trans hab))
    (log_le_log hapos hab)
  have hu := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hcF hdfF
    (fun x hx ↦ by
      rw [(hdF x (interior_subset hx)).deriv]
      exact (hb _ (one_le_exp_iff.mpr (interior_subset hx))).2)
    (log a) (log_nonneg ha) (log b) (log_nonneg (ha.trans hab))
    (log_le_log hapos hab)
  have heqa : logControl σ (log a) = log (sqrt (σ a)) := by
    rw [logControl, exp_log hapos, log_sqrt (hs a ha).le]
  have heqb : logControl σ (log b) = log (sqrt (σ b)) := by
    rw [logControl, exp_log hbpos, log_sqrt (hs b (ha.trans hab)).le]
  rw [heqa, heqb, zero_mul] at hl
  rw [heqa, heqb, ← log_div hbpos.ne' hapos.ne'] at hu
  exact ⟨hl, hu⟩

/-- In ordinary coordinates the optimal control is nondecreasing. -/
theorem sqrt_monotoneOn_of_logSlope {σ : ℝ → ℝ} {B : ℝ}
    (hs : ∀ r ≥ 1, 0 < σ r)
    (hd : ∀ r ≥ 1, DifferentiableAt ℝ σ r)
    (hb : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    MonotoneOn (fun r ↦ sqrt (σ r)) (Ici 1) := by
  intro a ha b _ hab
  have h := (log_sqrt_growth hs hd hb ha hab).1
  apply (log_le_log_iff (sqrt_pos.mpr (hs a ha))
    (sqrt_pos.mpr (hs b (ha.trans hab)))).mp
  linarith

/-- Multiplicative form used on every drift and unfolded impulse. -/
theorem sqrt_mul_bound_of_logSlope {σ : ℝ → ℝ} {B a b : ℝ}
    (hs : ∀ r ≥ 1, 0 < σ r)
    (hd : ∀ r ≥ 1, DifferentiableAt ℝ σ r)
    (hb : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    sqrt (σ b) ≤ sqrt (σ a) * exp (B * log (b / a)) := by
  have h := (log_sqrt_growth hs hd hb ha hab).2
  have hsa := sqrt_pos.mpr (hs a ha)
  have hsb := sqrt_pos.mpr (hs b (ha.trans hab))
  have he := Real.exp_le_exp.mpr h
  rw [exp_sub, exp_log hsa, exp_log hsb] at he
  exact (div_le_iff₀ hsa).mp he |>.trans_eq (mul_comm _ _)

end
end krylov.Asymptotics
