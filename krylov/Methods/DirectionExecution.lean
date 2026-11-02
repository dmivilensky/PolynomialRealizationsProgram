import krylov.Methods.DirectionReplay
import krylov.Methods.VirtualCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, alg:xrfc-D and thm:I, exact actual direction-replay coordinates.
Use: connect the true data-only XRFC-D implementation to fixed chronological
arrays before deriving its regularity and varying-prefix first variation.
Source: the existing real one-gradient executor and observed replay recursion;
all images below use returned gradients, never an unknown operator action.
-/

namespace krylov.Methods
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full-memory XRFC-D retained replay on its original observed history.
Use: its finite coordinates are reconstructed solely from real previous queries.
Article: main_krylov, alg:xrfc-D. -/
def xrfcDWindow (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : List (E × E) :=
  selectedDirectionWindow fullMemory trial (oneGradientRun (xrfcDMethod fullMemory trial) A g k)

/-- The actual extrapolated XRFC-D gradient computed from the genuine retained replay.
Use: distinguish the observed incoming gradient from the data-only virtual one.
Article: main_krylov, alg:xrfc-D. -/
def xrfcDVirtualGradient (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  virtualGradient (xrfcDWindow trial A g k) (oneGradientGradient (xrfcDMethod fullMemory trial) A g k)

/-- The actual direction chosen by the original full-memory XRFC-D policy.
Use: this vector is computed before the real next gradient is returned.
Article: main_krylov, alg:xrfc-D. -/
def xrfcDExecutedDirection (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  windowDirection (xrfcDWindow trial A g k) (xrfcDVirtualGradient trial A g k)

/-- The actual observed direction image recovered by the original XRFC-D replay.
Use: no operator action on the actual direction is presumed for varying data.
Article: main_krylov, alg:xrfc-D, q_k=(g_(k+1)-ghat_k)/tau_k. -/
def xrfcDExecutedImage (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (trial (oneGradientRun (xrfcDMethod fullMemory trial) A g k))⁻¹ •
    (oneGradientGradient (xrfcDMethod fullMemory trial) A g (k+1)-xrfcDVirtualGradient trial A g k)

/-- The real replay on an executed full-memory XRFC-D history is exactly the
newest-first transcript of its actual directions and returned-gradient images.
Use: true finite-array formulas follow without an assumed replay correctness
for varying operators.
Article: main_krylov, alg:xrfc-D and thm:I.
Proof: every real query appends exactly its actual chosen direction and the
actual inverse-trial observed gradient difference; induction retains the old replay. -/
theorem xrfcD_run_replay (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := oneGradientRun (xrfcDMethod fullMemory trial) A g k
    directionReplay fullMemory trial H.initial H.records=
      executedPairs (xrfcDExecutedDirection trial A g) (xrfcDExecutedImage trial A g) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only
    change directionReplay fullMemory trial
      (oneGradientAdvance (xrfcDMethod fullMemory trial) (A k)
        (oneGradientRun (xrfcDMethod fullMemory trial) A g k)).initial
      (oneGradientAdvance (xrfcDMethod fullMemory trial) (A k)
        (oneGradientRun (xrfcDMethod fullMemory trial) A g k)).records=_
    rw [directionReplay_advance]
    change (xrfcDExecutedDirection trial A g k,xrfcDExecutedImage trial A g k)::
      directionReplay fullMemory trial (oneGradientRun (xrfcDMethod fullMemory trial) A g k).initial
        (oneGradientRun (xrfcDMethod fullMemory trial) A g k).records=_
    rw [ih]
    rfl

/-- Full-memory direction retention keeps the actual entire replay transcript.
Use: turn genuine XRFC-D window solves into fixed finite coordinates.
Article: main_krylov, alg:xrfc-D.
Proof: the exact actual replay has precisely the actual number of records,
so the prescribed full-memory take discards no observed pair. -/
theorem xrfcD_full_window (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    xrfcDWindow trial A g k=
      executedPairs (xrfcDExecutedDirection trial A g) (xrfcDExecutedImage trial A g) k := by
  unfold xrfcDWindow selectedDirectionWindow
  rw [xrfcD_run_replay,oneGradientRun_length]
  exact List.take_of_length_le (by rw [executedPairs_length];rfl)

/-- The actual XRFC-D virtual correction and virtual gradient are the genuine
native inverse-model solve on its fixed newest-age direction/image arrays.
Use: primitive finite smooth solve calculus applies to the original replayed data.
Article: main_krylov, alg:xrfc-D and thm:I.
Proof: the full actual replay has its true fixed chronological coordinates;
the existing virtual-window reindexing theorem preserves the exact solve. -/
theorem xrfcD_virtual_coordinates (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := oneGradientRun (xrfcDMethod fullMemory trial) A g k
    let D := fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val)
    let Q := fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)
    virtualCorrection (xrfcDWindow trial A g k) H.gradient=
      combine D (modelCoefficients D (pairModel D Q) H.gradient) ∧
      xrfcDVirtualGradient trial A g k=H.gradient+combine Q (modelCoefficients D (pairModel D Q) H.gradient) := by
  let d := xrfcDExecutedDirection trial A g
  let q := xrfcDExecutedImage trial A g
  let W := executedPairs d q k
  have hlen : W.length=k := executedPairs_length d q k
  let D := fun i : Fin k => d (k-1-i.val)
  let Q := fun i : Fin k => q (k-1-i.val)
  have hd : windowSteps W=D ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.fst (executedPairs_get d q k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  have hq : windowImages W=Q ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.snd (executedPairs_get d q k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  dsimp only
  unfold xrfcDVirtualGradient
  rw [xrfcD_full_window]
  exact virtualWindow_coordinates W hlen D Q hd hq _

/-- The real direction-replay conjugacy solve has its exact fixed finite array formula.
Use: derive actual direction regularity from actual earlier replayed vectors.
Article: main_krylov, alg:xrfc-D and thm:I.
Proof: insert the exact genuine full replay in the existing executed-window
conjugacy reindexing theorem. -/
theorem xrfcD_direction_coordinates (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    xrfcDExecutedDirection trial A g k=
      conjugacyDirection (fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val))
        (fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)) (xrfcDVirtualGradient trial A g k) := by
  unfold xrfcDExecutedDirection
  rw [xrfcD_full_window,windowDirection_executed]
  rfl

end
end krylov.Methods
