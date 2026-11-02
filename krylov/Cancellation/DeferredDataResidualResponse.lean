import krylov.Cancellation.DeferredDataResidualJet
import krylov.Cancellation.DeferredResponse
import krylov.Envelope.ResidualCoordinates
import krylov.Methods.CorrectionFreeSearch
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, actual original deferred residual response vector.
Use: reconstruct the genuine arbitrary-observed-estimate finite DC response
from the derived actual recorded residual first derivatives.
Source: original native residual jets, true old-flag spatial response
coordinates and the existing genuine finite CG residual reconstruction theorem.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Variation krylov.Envelope
variable {n : ℕ}

/-- The original arbitrary positive C-two observed-estimate DC executor has
exactly the printed deferred spatial residual response on every real active
finite prefix, with its true uncalibrated reference damping value.
Use: no constant-estimate surrogate or assumed response derivative is inserted.
Article: main_krylov, thm:DC, actual sum P_l E_l vtilde_l.
Proof: the real native last old-residual jets are the proved damped FC plus
fresh coordinates. Genuine final exact search annihilates the actual own-step
residual. The literal spatial response has exactly these same real canonical
coordinates and belongs to the true explored flag; existing genuine finite
CG residual reconstruction identifies the full actual residual vector. -/
theorem deferred_data_residualVariation
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ j<k+1,ContDiffAt ℝ 2 (fun t => B t j) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : k+1≤referenceAtomCount base hb g)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    residualVariation base g m (canonicalFCPath base E) B (k+1)=
      deferredResponse base g k (1-CG.length Q g k/a0) E := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let A := canonicalFCPath base E
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  let F := deferredResponse base g k epsilon E
  have hF : F∈exploredFlag base g (k+1) :=
    exploredFlag_mono base g (show k≤k+1 by omega) (deferred_response_mem base hb g k epsilon E)
  apply residualVariation_of_coordinates base hb g (k+1) hcount m A B F hF
  intro i hi
  by_cases hik : i=k
  · subst i
    have heq : (fun t => inner ℝ (probedStep m (A t) (B t) g k) (probedGradient m (A t) (B t) g (k+1)))=
        fun _ : ℝ => (0 : ℝ) := by
      funext t
      exact correctionFree_last_residual m (fun _ _ => rfl) (A t) (B t) g k
    rw [heq,deriv_const,deferred_response_last_coordinate base hb g k hcount epsilon E]
  · have hil : i<k := by omega
    rw [deferred_data_residual_derivative estimate base hb g E hE B k hB hB0 hcount ha ha0 i hil]
    exact (deferred_response_physical_coordinates base hb g k hcount epsilon E i hil).symm

end
end krylov.Cancellation
