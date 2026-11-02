import krylov.Completion.ObservedWindowEstimate
import krylov.Completion.DampingBand
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant and thm:radau, one original observed harmonic rule.
Use: choose the same harmonic trial from real known window data on every
spectral-prior information fibre, including singular and collapsed windows.
Source: proved actual observed curvature endpoints and genuine physical
harmonic trial minimax, with the true spectral-band coefficient bound.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.OneGradient
variable {n p : ℕ}

/-- One data-only harmonic trial from the original observed window, class
endpoints and observed negative descent pairing.
Use: a single policy handles all physical references in the spectral prior.
Article: main_krylov, cor:quant and thm:radau. -/
def observedHarmonicTrial (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q : ℝ) : ℝ :=
  harmonicTrial (q/observedUpperCurvature S d T mu upper) (q/observedLowerCurvature S d T mu upper)

/-- On every genuine feasible physical window the single observed harmonic
trial is positive, equals the true midpoint-curvature rule and attains the
original exact physical minimax value, bounded by the known spectral coefficient.
Use: all actual endpoint domains follow from real physical feasibility;
ordinary shifted inverses and positive interval width are unnecessary.
Article: main_krylov, cor:quant(a) and thm:radau.
Proof: the actual observed curvature range is a positive attained interval.
Physical harmonic equioscillation gives its true matrix maximum, and testing
both real endpoint matrices gives the uniform spectral-band bound. -/
theorem observed_harmonic_trial_bound
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q : ℝ) (hmu : 0 < mu) (hmuL : mu≤upper)
    (hq : 0 < q) (hC : (windowCurvatureCompletions S d T mu upper).Nonempty) :
    let lo := observedLowerCurvature S d T mu upper
    let hi := observedUpperCurvature S d T mu upper
    let t := observedHarmonicTrial S d T mu upper q
    0 < t ∧ t=2*q/(lo+hi) ∧
      IsGreatest ((fun A => |1-t/physicalTrialLength d q A|) '' windowCurvatureCompletions S d T mu upper)
        ((hi-lo)/(hi+lo)) ∧ (hi-lo)/(hi+lo)≤(upper-mu)/(upper+mu) := by
  obtain ⟨hl,horder,hrange⟩ := observed_window_curvature_range S hS d hd T mu upper hmu hmuL hC
  let lo := observedLowerCurvature S d T mu upper
  let hi := observedUpperCurvature S d T mu upper
  have hhi : 0 < hi := hl.trans_le horder
  have ha : 0 < q/hi := div_pos hq hhi
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hl horder
  have hscalar := harmonic_trial_attains ha hab
  have hdictionary := harmonic_physical_curvature hl hhi hq
  dsimp only
  refine ⟨hscalar.1,hdictionary.1,?_,?_⟩
  · have hw := physical_trial_worst (windowCurvatureCompletions S d T mu upper) d q lo hi
      hq hl horder hrange (harmonicTrial (q/hi) (q/lo))
    rw [hscalar.2,hdictionary.2] at hw
    exact hw
  · exact physical_damping_band (windowCurvatureCompletions S d T mu upper) d lo hi mu upper
      hmu hmuL hl horder hrange (fun _ hA => ⟨hA.2.1,hA.2.2.1⟩)

end
end krylov.Completion
