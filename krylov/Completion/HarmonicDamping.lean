import krylov.Completion.PhysicalDampingMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), exact harmonic-estimate damping comparison.
Use: quantify the larger damping objective when the harmonic trial is used
in place of the original arithmetic cancellation estimate.
Source: genuine physical endpoint attainment and the proved scalar harmonic
opposite-objective formula; singleton intervals are included.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.OneGradient
variable {n : ℕ}

/-- On the true physical completion class the harmonic trial has the exact
attained worst residual multiplier (r-1)/2, including coincident endpoints.
Use: compare the actual matrix-uncertainty damping objective with the smaller
arithmetic minimax value (r-1)/(r+1) from the original DC estimate.
Article: main_krylov, thm:dcs(c), harmonic-mean comparison.
Proof: the true positive reciprocal step interval gives a genuine positive
harmonic estimate. Actual endpoint matrices attain its damping maximum;
substitute the proved scalar opposite-objective formula and clear positive
original curvature endpoints and the positive observed descent pairing. -/
theorem physical_harmonic_damping_worst
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi : ℝ)
    (hq : 0<q) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi) :
    IsGreatest ((fun A => |1-physicalTrialLength d q A/harmonicTrial (q/hi) (q/lo)|) '' C)
      ((hi/lo-1)/2) := by
  have hhi : 0<hi := hlo.trans_le horder
  have ha : 0<q/hi := div_pos hq hhi
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  have hw := physical_damping_worst C d q lo hi hq hlo horder hrange
    (harmonicTrial (q/hi) (q/lo)) (harmonic_trial_attains ha hab).1
  rw [harmonic_damping_error ha hab] at hw
  have he : (q/lo-q/hi)/(2*(q/hi))=(hi/lo-1)/2 := by
    field_simp
  rwa [he] at hw

end
end krylov.Completion
