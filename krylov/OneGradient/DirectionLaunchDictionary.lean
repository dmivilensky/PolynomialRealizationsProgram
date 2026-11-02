import krylov.OneGradient.ReplayLaunchModel
import krylov.Information.FullModelQuery
import krylov.Methods.DirectionExecution
import krylov.Correction.ChronologicalCorrection
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), exact native full direction-output dictionary.
Use: the actual implemented XRFC-D semantic output is its genuine full
ambient observed model solve on its real chronological replay columns.
Source: actual data-only replay coordinates, true chronological latest
model reindexing and exact full physical coefficient reconstruction.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Information krylov.Correction krylov.LinearAlgebra krylov.Stability
variable {n : ℕ}

/-- The actual original full direction-basis semantic output is exactly
the genuine ambient inverse replay-model correction. The real replayed
images are retained; no true varying-operator image identity is assumed.
Use: the cubic replay-model comparison applies to the original algorithm,
rather than a substituted final correction on hypothetical observations.
Article: main_krylov, thm:local(a), true direction output dictionary.
Proof: the native executed replay has its real newest-first coordinates.
Chronological latest-model reindexing preserves that exact solve. Its
true cross Gram is the actual column transpose times the image matrix;
full physical coefficient reconstruction identifies the genuine output. -/
theorem xrfcD_semantic_replay_dictionary
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hu : IsUnit (fullBasisMatrix (fun i : Fin n =>
      xrfcDExecutedDirection trial (fun k => cgOperator (A k)) g i.val)).det) :
    let m := xrfcDMethod fullMemory trial
    let op := fun k => cgOperator (A k)
    let H := oneGradientRun m op g n
    let D := fullBasisMatrix (fun i : Fin n => xrfcDExecutedDirection trial op g i.val)
    let Y := fullBasisMatrix (fun i : Fin n => xrfcDExecutedImage trial op g i.val)
    m.outputGradient (op n) H=H.gradient-op n (cgOperator (replayLaunchModel D Y)⁻¹ H.gradient) := by
  let m := xrfcDMethod fullMemory trial
  let op := fun k => cgOperator (A k)
  let H := oneGradientRun m op g n
  let d := fun i : Fin n => xrfcDExecutedDirection trial op g i.val
  let y := fun i : Fin n => xrfcDExecutedImage trial op g i.val
  let D := fullBasisMatrix d
  let Y := fullBasisMatrix y
  have hcross : crossGram d y=Dᵀ*Y := by
    ext i j
    exact column_inner_eq_coordinate D i (y j)
  have hchron := chronological_modelCorrection d y H.gradient
  rw [hcross] at hchron
  have hquery : m.output H=combine d (modelCoefficients d (latest (Dᵀ*Y)) H.gradient) := by
    change virtualCorrection (xrfcDWindow trial op g n) H.gradient=_
    rw [(xrfcD_virtual_coordinates trial op g n).1]
    simpa only [d,y,H,Function.comp_def,Fin.revPerm_apply,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using hchron.symm
  have hq := full_model_query d (latest (Dᵀ*Y)) hu H.gradient
  dsimp only
  change H.gradient+op n (m.output H)=_
  rw [hquery,hq,map_neg]
  rfl

end
end krylov.OneGradient
