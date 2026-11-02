import krylov.Methods.OneGradientCoordinates
import krylov.Methods.NonlinearCGObserved
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical, literal observed Nazareth implementation.
Use: reconstruct true trial directions and their genuine operator images
from old measured steps, then execute the original three-term Lanczos rule.
Source: Nazareth77 equations (10),(16), reproduced in main_krylov; actual
trial lengths are retained, without rescaling the requested trial schedule. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The previous actually queried direction reconstructed from its measured
step and the true trial decision at the preceding complete history.
Use: the original Nazareth recurrence uses t_j, rather than silently replacing
it by its differently scaled measured step.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10). -/
def measuredTrialDirection (trial : History E → ℝ) (H : History E) : E :=
  match H.records with
  | [] => 0
  | r::_ => (trial (historyTail H))⁻¹ • r.step

/-- The actual previous direction image reconstructed from its returned
gradient difference and the same actual old trial decision.
Use: no hidden or newly queried matrix action enters the Lanczos recurrence.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10). -/
def measuredTrialImage (trial : History E → ℝ) (H : History E) : E :=
  (trial (historyTail H))⁻¹ • (H.gradient-(historyTail H).gradient)

/-- The literal original three-term observed Lanczos direction.
Use: both old directions and both images are reconstructed with their own
actual old trials; multiply by the original preceding trial as in
t_(j+1)=lambda_j*p_(j+1). The absent older term is exactly zero.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10). -/
def nazarethDirection (trial : History E → ℝ) (H : History E) : E :=
  match H.records with
  | [] => -H.initial
  | _::_ =>
    let t := measuredTrialDirection trial H
    let q := measuredTrialImage trial H
    let old := measuredTrialDirection trial (historyTail H)
    let oldq := measuredTrialImage trial (historyTail H)
    trial (historyTail H) • (-q+(inner ℝ q q/inner ℝ t q) • t+(inner ℝ oldq q/inner ℝ old oldq) • old)

/-- The original measured pair projection using its own newly returned
gradient, with the genuine step/secant energy denominator.
Use: the final source correction uses only the actually recorded observations.
Article: main_krylov, prop:classical(b), Nazareth77 equation (16). -/
def recordedProjectionCorrection (H : History E) : E :=
  ((H.records.zip H.pairs).map (fun rp =>
    (-inner ℝ rp.2.1 rp.1.gradient/inner ℝ rp.2.1 rp.2.2) • rp.2.1)).sum

/-- The genuine one-gradient Nazareth procedure with its supplied actual
trial schedule and original observed final projection correction.
Use: its direction is the literal measured three-term recurrence, and its
output spends no further query or unobserved matrix action.
Article: main_krylov, prop:classical(a,b), Nazareth77 equations (10),(16). -/
def nazarethMethod (trial : History E → ℝ) : OneGradientMethod E where
  step H := trial H • nazarethDirection trial H
  output H := recordedProjectionCorrection H

/-- Removing the newest genuine one-gradient record recovers exactly the
actual preceding complete history for every method and segment sequence.
Use: old trial decisions in observed recurrences are the real executed ones.
Article: main_krylov, prop:classical(a).
Proof: one real evaluated query prepends exactly one record and preserves
all old records and the genuine initial observation. -/
theorem oneGradient_historyTail_succ (method : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    historyTail (oneGradientRun method A g (k+1))=oneGradientRun method A g k := rfl

/-- Reconstructing the actual measured direction of the original Nazareth
executor gives exactly its previous computed direction on arbitrary segments.
Use: this is an executed observation identity, independent of quadratic CG
consistency or any recurrence field supplied by the theorem user.
Article: main_krylov, prop:classical(a).
Proof: the real measured step is the actual old trial times the computed
direction. The genuine preceding history and nonzero trial cancel exactly. -/
theorem nazareth_measured_direction (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (ht : trial (oneGradientRun (nazarethMethod trial) A g k)≠0) :
    measuredTrialDirection trial (oneGradientRun (nazarethMethod trial) A g (k+1))=
      nazarethDirection trial (oneGradientRun (nazarethMethod trial) A g k) := by
  change (trial (historyTail (oneGradientRun (nazarethMethod trial) A g (k+1))))⁻¹ •
    (trial (oneGradientRun (nazarethMethod trial) A g k) •
      nazarethDirection trial (oneGradientRun (nazarethMethod trial) A g k))=_
  rw [oneGradient_historyTail_succ,smul_smul,inv_mul_cancel₀ ht,one_smul]

/-- Reconstructing the actual previous Nazareth image gives the real
segment action on its true computed direction, also on varying segments.
Use: no constant-operator or desired replay-image hypothesis enters the rule.
Article: main_krylov, prop:classical(a).
Proof: the actual one-gradient query returns its true segment action on the
measured step. Recover the real old history and cancel its nonzero trial. -/
theorem nazareth_measured_image (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (ht : trial (oneGradientRun (nazarethMethod trial) A g k)≠0) :
    measuredTrialImage trial (oneGradientRun (nazarethMethod trial) A g (k+1))=
      A k (nazarethDirection trial (oneGradientRun (nazarethMethod trial) A g k)) := by
  unfold measuredTrialImage
  rw [oneGradient_historyTail_succ]
  change (trial (oneGradientRun (nazarethMethod trial) A g k))⁻¹ •
    ((oneGradientRun (nazarethMethod trial) A g k).gradient+
      A k (trial (oneGradientRun (nazarethMethod trial) A g k) •
        nazarethDirection trial (oneGradientRun (nazarethMethod trial) A g k))-
      (oneGradientRun (nazarethMethod trial) A g k).gradient)=_
  rw [add_sub_cancel_left,map_smul,smul_smul,inv_mul_cancel₀ ht,one_smul]

end
end krylov.Methods
