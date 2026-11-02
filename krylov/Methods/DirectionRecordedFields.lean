import krylov.Methods.DirectionStepChange
import krylov.Methods.PairModelChangeOrder
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual recorded fields on a native D run.
Use: identify the original history-only S policy fields with a genuine
common pair change on that same real direction-basis execution.
Source: exact one-gradient transcript coordinates and the actual observed
step/image change, without an off-quadratic replay-correctness premise.
-/

namespace krylov.Methods
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original recorded-pair virtual fields on a true native D history
are exactly the real changed native-pair fields, on arbitrary operators.
Use: the informed policy reads these recorded S fields even during D
execution; their actual difference from native D fields must be estimated.
Article: main_krylov, thm:local(a), genuine recorded-policy dictionary.
Proof: actual step and image columns have their exact common observed
change. Insert these true finite arrays into the reused full-history
virtual-gradient and conjugacy-direction coordinate dictionaries. -/
theorem xrfcD_recorded_virtual_fields (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (ht : ∀ i<k,trial (oneGradientRun (xrfcDMethod fullMemory trial) A g i)≠0) :
    let m := xrfcDMethod fullMemory trial
    let H := oneGradientRun m A g k
    let D := fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val)
    let Q := fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)
    let T := xrfcDObservedStepChange trial A g k
    let gv := pairVirtualGradient (rightChange D T) (rightChange Q T) H.gradient
    virtualGradient H.pairs H.gradient=gv ∧
      windowDirection H.pairs (virtualGradient H.pairs H.gradient)=
        conjugacyDirection (rightChange D T) (rightChange Q T) gv := by
  dsimp only
  let m := xrfcDMethod fullMemory trial
  let H := oneGradientRun m A g k
  let D := fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val)
  let Q := fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)
  let T := xrfcDObservedStepChange trial A g k
  have hs : (fun i : Fin k => oneGradientStep m A g (k-1-i.val))=rightChange D T :=
    funext fun j => (xrfcDObservedStepChange_steps trial A g k j).symm
  have hy : (fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val)))=rightChange Q T :=
    funext fun j => (xrfcDObservedStepChange_images trial A g k j (ht _ (by omega))).symm
  have hv := (oneGradient_full_virtual_coordinates m A g k).2
  rw [selectedWindow_full,hs,hy] at hv
  have hd := oneGradient_full_direction_coordinates m A g (virtualGradient H.pairs H.gradient) k
  rw [selectedWindow_full,hs,hy,hv] at hd
  refine ⟨hv,?_⟩
  rw [hv]
  exact hd

end
end krylov.Methods
