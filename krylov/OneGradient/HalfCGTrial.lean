import krylov.OneGradient.XRFCForgetting
import krylov.Stability.TrialCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, actual one-half-error reference trials.
Use: realize the source's epsilon_j=1/2 counterexample by genuine data-only
trial functions with primitive smooth observed charts and nonzero true trials.
Source: actual measured positive CG reference lengths and the original
one-gradient history count; the trial coefficients are fixed constants in
each original observed-vector chart.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- A genuine data-only trial policy with prescribed half-CG reference lengths.
Use: the original counterexample has a real one-gradient implementation.
Article: main_krylov, prop:where, epsilon_j=1/2. -/
def halfCGTrial (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    History (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun H => CG.length (cgOperator base) g H.records.length/2

/-- The true executed policy reads exactly its actual iteration number.
Use: its reference trial values are derived from real histories.
Article: main_krylov, prop:where.
Proof: every actual one-gradient history has precisely its real iteration count. -/
theorem halfCGTrial_run (base : Matrix (Fin n) (Fin n) ℝ) (g h : EuclideanSpace ℝ (Fin n))
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n)))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    halfCGTrial base g (oneGradientRun m A h k)=CG.length (cgOperator base) g k/2 := by
  simp only [halfCGTrial,oneGradientRun_length]

/-- The original one-half-error rule is smooth in every primitive observed
vector chart, with arbitrary real differentiability order.
Use: the counterexample satisfies the genuine source trial regularity premise.
Article: main_krylov, prop:where.
Proof: its actual finite-chart coefficient is a true fixed real constant. -/
theorem halfCGTrial_contDiff {r : WithTop ℕ∞} (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ContDiff ℝ r (trialCoordinate (halfCGTrial base g) k) := by
  change ContDiff ℝ r (fun data => CG.length (cgOperator base) g (oneGradientHistoryChart data).records.length/2)
  simpa only [oneGradientHistoryChart,List.length_ofFn] using
    (contDiff_const : ContDiff ℝ r (fun _ : EuclideanSpace ℝ (Fin n) ×
      (Fin k → EuclideanSpace ℝ (Fin n)) × (Fin k → EuclideanSpace ℝ (Fin n)) => CG.length (cgOperator base) g k/2))

/-- Actual half-CG reference trials are strictly positive throughout the true active cycle.
Use: all native source model/replay domains are genuine on the counterexample.
Article: main_krylov, prop:where.
Proof: the true active CG length is positive and the actual trial is its half. -/
theorem halfCGTrial_positive (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    0<halfCGTrial base g (oneGradientRun (xrfcMethod fullMemory (halfCGTrial base g))
      (fun _ => cgOperator base) g k) := by
  rw [halfCGTrial_run]
  exact div_pos (cgLength_pos base hb g k hk) (by norm_num)

/-- Every original measured relative error of the true half-CG rule is exactly one half.
Use: the source counterexample has the stipulated actual epsilon sequence.
Article: main_krylov, prop:where.
Proof: insert the real trial and cancel only the proved positive actual CG line. -/
theorem halfCGTrial_error (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    xrfcTrialError (halfCGTrial base g) base g k=1/2 := by
  simp only [xrfcTrialError,halfCGTrial_run]
  field_simp [(cgLength_pos base hb g k hk).ne']
  ring

/-- Every actual direction-basis amplitude of the half-CG policy has precisely
one half of the genuine corresponding square-root CG energy.
Use: older errors are retained because all actual later virtual factors are one.
Article: main_krylov, prop:where.
Proof: the original exact absolute-amplitude formula has half relative error
and every true later correction ratio one, including the empty final product. -/
theorem halfCGTrial_amplitude (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : N≤referenceAtomCount base hb g)
    (l : ℕ) (hl : l<N) :
    |xrfcTrialCoefficient (halfCGTrial base g) base g N l|=Real.sqrt (cgEnergy base g l)/2 := by
  rw [xrfc_trial_coefficient_abs _ base hb g N l (hl.trans_le hN)]
  have he : |1-halfCGTrial base g (oneGradientRun (xrfcMethod fullMemory (halfCGTrial base g))
      (fun _ => cgOperator base) g l)/CG.length (cgOperator base) g l|=1/2 := by
    change |xrfcTrialError (halfCGTrial base g) base g l|=1/2
    rw [halfCGTrial_error base hb g l (hl.trans_le hN),abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  rw [he]
  have hp : (∏ j∈Finset.Ico (l+1) N,
      |(CG.length (cgOperator base) g j-halfCGTrial base g (oneGradientRun
        (xrfcMethod fullMemory (halfCGTrial base g)) (fun _ => cgOperator base) g j))/
        halfCGTrial base g (oneGradientRun (xrfcMethod fullMemory (halfCGTrial base g))
          (fun _ => cgOperator base) g j)|)=1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [halfCGTrial_run]
    have hpos := (cgLength_pos base hb g j ((Finset.mem_Ico.mp hj).2.trans_le hN)).ne'
    have hr : (CG.length (cgOperator base) g j-CG.length (cgOperator base) g j/2)/
        (CG.length (cgOperator base) g j/2)=1 := by field_simp [hpos];norm_num
    rw [hr,abs_one]
  rw [hp,mul_one]
  ring

end
end krylov.OneGradient
