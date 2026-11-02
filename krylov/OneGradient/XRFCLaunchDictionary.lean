import krylov.OneGradient.LaunchFirstJet
import krylov.Correction.ChronologicalCorrection
import krylov.OneGradient.XRFCColumns
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch(b) and thm:I, actual XRFC/full-model dictionary.
Use: identify the genuine implemented full-memory XRFC semantic output with
the true physical observed-model launch solve on its original recorded steps.
Source: actual full-memory transcript coordinates, exact chronological model
reindexing and the genuine native full-model coefficient identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Correction
variable {n : ℕ}

/-- The true implemented XRFC output equals the original physical full-window
launch solve on the actual chronological evaluated steps and their true observations.
Use: the general launch derivative and remainder apply to the original method,
without presuming any response or replacement trajectory.
Article: main_krylov, prop:launch(b); thm:I, step basis.
Proof: actual full-memory finite transcript coordinates give the native
newest-first virtual correction. The proved chronological model identity
reindexes the very same solve, and the real compressed physical observations
identify its actual full-model matrix. The true native coefficient launch
identity then identifies the original semantic output exactly. -/
theorem xrfc_semantic_launch_dictionary
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hu : IsUnit (fullBasisMatrix (fun i : Fin n => oneGradientStep (xrfcMethod fullMemory trial)
      (fun k => cgOperator (A k)) g i.val)).det) :
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun k => cgOperator (A k)) g n
    let S := fullBasisMatrix (fun i : Fin n => oneGradientStep m (fun k => cgOperator (A k)) g i.val)
    m.outputGradient (cgOperator (A n)) H=launchSemanticGradient S A H.gradient := by
  let m := xrfcMethod fullMemory trial
  let op := fun k => cgOperator (A k)
  let H := oneGradientRun m op g n
  let s := fun i : Fin n => oneGradientStep m op g i.val
  let y := fun i : Fin n => op i.val (s i)
  let S := fullBasisMatrix s
  have hcross : crossGram s y=Sᵀ*pairImages S A := by
    ext i j
    rw [← observed_compression]
    exact (compressed_entry_pairing S (A j.val) i j).symm
  have hchron := chronological_modelCorrection s y H.gradient
  rw [hcross] at hchron
  have hn := (oneGradient_full_virtual_coordinates m op g n).1
  have hquery : m.output H=combine s (modelCoefficients s (latest (Sᵀ*pairImages S A)) H.gradient) := by
    change virtualCorrection (selectedWindow fullMemory H) H.gradient=_
    rw [hn]
    simpa only [s,y,H,Function.comp_def,Fin.revPerm_apply,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using hchron.symm
  have hl := launch_semantic_coefficients S hu A H.gradient
  change H.gradient+cgOperator (A n) (m.output H)=_
  rw [hquery]
  exact hl.symm

end
end krylov.OneGradient
