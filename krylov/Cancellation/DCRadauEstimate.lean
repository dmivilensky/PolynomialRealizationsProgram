import krylov.Cancellation.DCCurvatureTrial
import krylov.Completion.ObservedWindowEstimate
import krylov.Completion.PhysicalDampingMinimax
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and thm:dcs(c), actual Gauss--Radau DC estimate.
Use: implement one real data-only history rule using the original untilted
window direction, virtual descent pairing, physical observed model and class
bounds; prove its physical minimax value and curvature-trial dictionary.
Source: genuine attained singular-Schur completion intervals and the proved
physical arithmetic damping minimax, including collapsed intervals.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Completion krylov.OneGradient
variable {n : ℕ}

/-- The original retained observed step columns in physical coordinates.
Use: actual completion policies read the same real window as the native solve.
Article: main_krylov, s8:dcsdef. -/
def dcObservedColumns (memory : ℕ → ℕ) (H : History (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin (selectedWindow memory H).length) ℝ :=
  fun i j => windowSteps (selectedWindow memory H) j i

/-- The actual original untilted FC direction in physical coordinates.
Use: choose the consistency interval before the real tilted direction is formed.
Article: main_krylov, s8:dcsdef. -/
def dcObservedUntilted (memory : ℕ → ℕ) (H : History (EuclideanSpace ℝ (Fin n))) : Fin n → ℝ :=
  fun i => windowDirection (selectedWindow memory H) H.gradient i

/-- The actual observed lower physical directional curvature for DC-slide.
Use: one data-only estimate works on all feasible original histories.
Article: main_krylov, s8:dcsdef. -/
def dcObservedLower (memory : ℕ → ℕ) (mu L : ℝ) (H : History (EuclideanSpace ℝ (Fin n))) : ℝ :=
  observedLowerCurvature (dcObservedColumns memory H) (dcObservedUntilted memory H)
    (windowModel (selectedWindow memory H)) mu L

/-- The actual observed upper physical directional curvature for DC-slide.
Use: both true original endpoint completions remain in the estimate's uncertainty class.
Article: main_krylov, s8:dcsdef. -/
def dcObservedUpper (memory : ℕ → ℕ) (mu L : ℝ) (H : History (EuclideanSpace ℝ (Fin n))) : ℝ :=
  observedUpperCurvature (dcObservedColumns memory H) (dcObservedUntilted memory H)
    (windowModel (selectedWindow memory H)) mu L

/-- The original Gauss--Radau arithmetic-step estimate as one genuine observed
history rule, read before either actual DC executor forms its tilted direction.
Use: instantiate dcSlideMethod or dcSlideOneGradient without supplying any
unobserved base matrix, feasible completion choice or independent trial field.
Article: main_krylov, s8:dcsdef, arithmetic mean of the two Gauss--Radau steps. -/
def dcGaussRadauEstimate (memory : ℕ → ℕ) (mu L : ℝ) : History (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun H => observedArithmeticEstimate (dcObservedColumns memory H) (dcObservedUntilted memory H)
    (windowModel (selectedWindow memory H)) mu L (dcCurvatureSlope memory H)

/-- The true observed curvature realizing the original arithmetic-step estimate.
Use: specialize the proved real curvature-based one-gradient trajectory dictionary.
Article: main_krylov, s8:dcsdef, harmonic mean of directional endpoint curvatures. -/
def dcGaussRadauCurvature (memory : ℕ → ℕ) (mu L : ℝ) : History (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun H => harmonicTrial (dcObservedLower memory mu L H) (dcObservedUpper memory mu L H)

/-- The real observed Gauss--Radau arithmetic step is exactly the original
curvature-trial rule with its true harmonic endpoint-curvature estimate.
Use: the same implemented policy enters the genuine DC/XRFC curvature dictionary.
Article: main_krylov, s8:dcsdef and thm:dcs(b).
Proof: substitute the two original observed endpoint steps and clear only the
strictly positive true endpoint curvatures and their positive sum. -/
theorem dc_gauss_radau_curvature_dictionary (memory : ℕ → ℕ) (mu L : ℝ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (hlo : 0<dcObservedLower memory mu L H) (hhi : 0<dcObservedUpper memory mu L H) :
    dcGaussRadauEstimate memory mu L H=
      dcCurvatureEstimate memory (dcGaussRadauCurvature memory mu L) H := by
  change arithmeticEstimate (dcCurvatureSlope memory H/dcObservedUpper memory mu L H)
    (dcCurvatureSlope memory H/dcObservedLower memory mu L H)=
      dcCurvatureSlope memory H/harmonicTrial (dcObservedLower memory mu L H) (dcObservedUpper memory mu L H)
  unfold arithmeticEstimate harmonicTrial
  field_simp

/-- On every genuine feasible original physical window the implemented DC
estimate is positive and uniquely minimizes the actual worst residual damping.
Use: the source minimax concerns the true matrix completion class, with the
real native untilted direction, virtual descent pairing and observed model;
there is no presumed scalar interval or supplied endpoint realization.
Article: main_krylov, s8:dcsdef and thm:dcs(c).
Proof: actual feasibility derives all singular-Schur side conditions and the
attained positive known-data curvature interval. Physical damping equioscillation
then gives the exact worst value, unique positive optimizer and genuine
implementation equality for the single original observed policy. -/
theorem dc_gauss_radau_minimax (memory : ℕ → ℕ) (mu L : ℝ)
    (H : History (EuclideanSpace ℝ (Fin n))) (hmu : 0<mu) (hmuL : mu≤L)
    (hS : Function.Injective (dcObservedColumns memory H).mulVec)
    (hd : dcObservedUntilted memory H∉LinearMap.range (dcObservedColumns memory H).mulVecLin)
    (hC : (windowCurvatureCompletions (dcObservedColumns memory H) (dcObservedUntilted memory H)
      (windowModel (selectedWindow memory H)) mu L).Nonempty)
    (hq : 0<dcCurvatureSlope memory H) :
    let C := windowCurvatureCompletions (dcObservedColumns memory H) (dcObservedUntilted memory H)
      (windowModel (selectedWindow memory H)) mu L
    let lo := dcObservedLower memory mu L H
    let hi := dcObservedUpper memory mu L H
    let q := dcCurvatureSlope memory H
    0<dcGaussRadauEstimate memory mu L H ∧
      IsGreatest ((fun A => |1-physicalTrialLength (dcObservedUntilted memory H) q A/
        dcGaussRadauEstimate memory mu L H|) '' C) ((hi-lo)/(hi+lo)) ∧
      (∀ t : ℝ,0<t → ((∀ A∈C,|1-physicalTrialLength (dcObservedUntilted memory H) q A/t|≤(hi-lo)/(hi+lo)) ↔
        t=dcGaussRadauEstimate memory mu L H)) := by
  let S := dcObservedColumns memory H
  let d := dcObservedUntilted memory H
  let T := windowModel (selectedWindow memory H)
  let q := dcCurvatureSlope memory H
  let lo := dcObservedLower memory mu L H
  let hi := dcObservedUpper memory mu L H
  obtain ⟨hl,horder,hrange⟩ := observed_window_curvature_range S hS d hd T mu L hmu hmuL hC
  have ha : 0<q/hi := div_pos hq (hl.trans_le horder)
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hl horder
  have he : dcGaussRadauEstimate memory mu L H=q*(lo⁻¹+hi⁻¹)/2 := by
    change arithmeticEstimate (q/hi) (q/lo)=_
    unfold arithmeticEstimate
    ring
  refine ⟨(arithmetic_estimate_attains ha hab).1,?_,?_⟩
  · have hw := physical_damping_worst (windowCurvatureCompletions S d T mu L) d q lo hi
      hq hl horder hrange (dcGaussRadauEstimate memory mu L H) (arithmetic_estimate_attains ha hab).1
    have hvalue : dampingEndpointError (q/hi) (q/lo) (dcGaussRadauEstimate memory mu L H)=(hi-lo)/(hi+lo) :=
      (arithmetic_estimate_attains ha hab).2.trans (harmonic_physical_curvature hl (hl.trans_le horder) hq).2
    rw [hvalue] at hw
    exact hw
  · intro t ht
    rw [(physical_damping_minimax (windowCurvatureCompletions S d T mu L) d q lo hi hq hl horder hrange).2 t ht,he]

end
end krylov.Cancellation
