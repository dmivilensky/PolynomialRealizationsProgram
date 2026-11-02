import krylov.Correction.RFCLinearAngles
import krylov.Stability.UniformObservedLine

/-!
Article: main_krylov, thm:UCq, true finite uniform RFC constants.
Use: Construct explicit monotone error allowances from dimension, conditioning
and the proved actual correction, angle and projected-residual coefficients.
Source: genuine observed CG search bounds and elementary finite recurrences.
-/

namespace krylov.Correction
noncomputable section
open krylov.Stability

/-- Explicit finite step-error constants for the actual nonstagnating RFC induction.
Use: Choose all earlier-step allowances before the real reference and trajectory.
Article: main_krylov, thm:UCq.
-/
def rfcUniformStepConstant (N : ℕ) (κ K C L : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => rfcUniformStepConstant N κ K C L k+
      observedCGStepConstant k κ (rfcUniformStepConstant N κ K C L k)
        ((k : ℝ)*(rfcUniformStepConstant N κ K C L k+(1+K)*(rfcUniformStepConstant N κ K C L k+1)))
        ((N : ℝ)*rfcLinearAngleConstant N K C) (1+K)+
      2*rfcRelativeCorrectionConstant N K C*L

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem rfcRelativeCorrectionConstant_nonneg (N : ℕ) {K C : ℝ} (hK : 0≤K) (hC : 0≤C) :
    0≤rfcRelativeCorrectionConstant N K C := by unfold rfcRelativeCorrectionConstant; positivity

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem rfcLinearAngleConstant_pos (N : ℕ) {K C : ℝ} (hK : 0≤K) (hC : 0≤C) :
    0<rfcLinearAngleConstant N K C := by
  have hQ := rfcRelativeCorrectionConstant_nonneg N hK hC
  unfold rfcLinearAngleConstant
  positivity

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem observedCGStepConstant_nonneg (k : ℕ) {κ C D a K : ℝ}
    (hκ : 0≤κ) (hC : 0≤C) (hD : 0≤D) (ha : 0≤a) (hK : 0≤K) :
    0≤observedCGStepConstant k κ C D a K := by unfold observedCGStepConstant; positivity

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem rfcUniformStepConstant_nonneg (N : ℕ) {κ K C L : ℝ}
    (hκ : 0≤κ) (hK : 0≤K) (hC : 0≤C) (hL : 0≤L) (k : ℕ) :
    0≤rfcUniformStepConstant N κ K C L k := by
  have ha := (rfcLinearAngleConstant_pos N hK hC).le
  have hQ := rfcRelativeCorrectionConstant_nonneg N hK hC
  induction k with
  | zero => rfl
  | succ k ih =>
    exact add_nonneg (add_nonneg ih (observedCGStepConstant_nonneg k hκ ih (by positivity) (by positivity) (by positivity))) (by positivity)

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem rfcUniformStepConstant_monotone (N : ℕ) {κ K C L : ℝ}
    (hκ : 0≤κ) (hK : 0≤K) (hC : 0≤C) (hL : 0≤L) :
    Monotone (rfcUniformStepConstant N κ K C L) := by
  have ha := (rfcLinearAngleConstant_pos N hK hC).le
  have hQ := rfcRelativeCorrectionConstant_nonneg N hK hC
  apply monotone_nat_of_le_succ
  intro k
  have hs := rfcUniformStepConstant_nonneg N hκ hK hC hL k
  have hn : 0≤observedCGStepConstant k κ (rfcUniformStepConstant N κ K C L k)
      ((k : ℝ)*(rfcUniformStepConstant N κ K C L k+(1+K)*(rfcUniformStepConstant N κ K C L k+1)))
      ((N : ℝ)*rfcLinearAngleConstant N K C) (1+K) :=
    observedCGStepConstant_nonneg k hκ hs (by positivity) (by positivity) (by positivity)
  change _≤rfcUniformStepConstant N κ K C L k+_+_
  linarith [mul_nonneg (by positivity : 0≤2*rfcRelativeCorrectionConstant N K C) hL]

/-- The actual explicit finite coefficient has the sign or monotone allowance needed in the uniform induction.
Use: Derive real scalar bounds uniformly before the original run.
Article: main_krylov, thm:UCq.
Proof: Every added observed-search and correction coefficient is nonnegative. Expand the true recurrence and use these signs; no actual trajectory estimate is assumed.
-/
theorem rfcUniformStepConstant_next_allowance (N k : ℕ) {κ K C L : ℝ}
    (hκ : 0≤κ) (hK : 0≤K) (hC : 0≤C) (hL : 0≤L) :
    observedCGStepConstant k κ (rfcUniformStepConstant N κ K C L k)
      ((k : ℝ)*(rfcUniformStepConstant N κ K C L k+(1+K)*(rfcUniformStepConstant N κ K C L k+1)))
      ((N : ℝ)*rfcLinearAngleConstant N K C) (1+K)+2*rfcRelativeCorrectionConstant N K C*L≤
      rfcUniformStepConstant N κ K C L (k+1) := by
  have hs := rfcUniformStepConstant_nonneg N hκ hK hC hL k
  change _≤rfcUniformStepConstant N κ K C L k+_+_
  linarith

end
end krylov.Correction
