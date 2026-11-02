import krylov.Correction.DeepSource
import krylov.Correction.CertificatePrefix
import krylov.Correction.CertificateGate
import krylov.Correction.CertificateInput

/-!
Article: main_krylov, prop:deep, independently specified original RFC arithmetic.
Use: Define every checked output directly from the genuine rational source
and actual newest-first RFC array operations, before any interval annotation.
Source: the printed seven rational rows, original RFC conjugacy and latest
symmetric model, and the standard determinant/adjugate inverse identity.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate

/-- The original affine family parameter in its exact first real input slot.
Use: Preserve the true source parameter across every finite certificate block.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceParameter : Term := .input 0

/-- The independent arithmetic prefix read from the genuine four-dimensional observed input layout.
Use: Compile exactly the current gradient and newest-first total steps and measured secants.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceInputPrefix (k : ℕ) : TermPrefix 4 k where
  gradient := if k=0 then sourceInitial else fun i => .input (1+i.val)
  steps := fun i j => .input (5+4*i.val+j.val)
  images := fun i j => .input (5+4*k+4*i.val+j.val)

/-- The original observed-array RFC conjugacy direction expression.
Use: Certify the actual data-only direction without a prescribed desired trajectory.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceDirection (k : ℕ) : Fin 4 → Term := (sourceInputPrefix k).direction

/-- The true independent physical probe applied to the original current RFC direction.
Use: Preserve the genuine measured direction image.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceImage (k : ℕ) : Fin 4 → Term := termMatVec (sourceProbe k) (sourceDirection k)

/-- The actual post-line-search gradient expression before the original correction.
Use: Retain the exact real line-search arithmetic.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourcePost (k : ℕ) : Fin 4 → Term :=
  termPostSearch (sourceInputPrefix k).gradient (sourceDirection k) (sourceImage k)

/-- The genuine newest-first augmented direction and prior total-step family.
Use: Use the original latest-probe model coordinates.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceAugSteps (k : ℕ) : Fin (k+1) → Fin 4 → Term :=
  Fin.cons (sourceDirection k) (sourceInputPrefix k).steps

/-- The genuine newest-first augmented probe image and prior measured-secant family.
Use: Keep the exact original observed model data.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceAugImages (k : ℕ) : Fin (k+1) → Fin 4 → Term :=
  Fin.cons (sourceImage k) (sourceInputPrefix k).images

/-- The actual symmetric latest-probe model expression on the genuine augmented family.
Use: Certify the original final model determinant and leading principal minors.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceModel (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) Term :=
  termPairModel (sourceAugSteps k) (sourceAugImages k)

/-- The true terminal physical adjugate numerator in the original inverse-model correction.
Use: Expose the actual last RFC residual singularity without dividing by its model determinant.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceNumerator : Fin 4 → Term :=
  termMatVec (sourceCorrection 3) (termCombine (sourceAugSteps 3)
    (termMatVec (termAdj (sourceModel 3)) (termCoordinates (sourceAugSteps 3) (sourcePost 3))))

/-- The four genuine augmented source directions stored as physical matrix columns.
Use: Certify the actual terminal basis determinant.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceBasis : Matrix (Fin 4) (Fin 4) Term := fun i j => sourceAugSteps 3 j i

/-- An actual leading principal minor of the original terminal latest-probe model.
Use: Keep all printed lower-dimensional positive principal-minor assertions tied to their real model.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceLeading (n : ℕ) (hn : n≤4) : Term :=
  termDet ((sourceModel 3).submatrix (Fin.castLE hn) (Fin.castLE hn))

/-- The complete next real input layout computed by one actual source RFC phase.
Use: Propagate certified gradient and genuine observed total-step/secant coordinates to the next block.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceNextInputs (k : ℕ) : List Term :=
  let h := (sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)
  List.ofFn (fun i : Fin (5+8*(k+1)) =>
    encodeInput (k+1) sourceParameter h.gradient h.steps h.images (.literal 0 1) i.val)

/-- The independently specified finite output inventory of each original source phase.
Use: Decode all line-search, gate, model, next-state and terminal singularity bounds from the unchanged kernel checker.
Article: main_krylov, prop:deep, independently specified actual source arithmetic. -/
def sourceOutputs (k : Fin 4) : List Term :=
  let p := k.val
  [termLineLength (sourceInputPrefix p).gradient (sourceDirection p) (sourceImage p),
    termDot (sourceDirection p) (sourceImage p),
    termDefectSquare (sourceAugSteps p) (sourceAugImages p),
    termDefectSquare (sourceInputPrefix p).steps (sourceInputPrefix p).images,
    termDet (sourceModel p)]++
  List.ofFn (fun i : Fin (p+1) => termDot (sourceAugSteps p i) (sourceAugImages p i))++
  (List.ofFn (fun i : Fin 4 => [sourceDirection p i,sourceImage p i,sourcePost p i])).flatten++
  if p<3 then sourceNextInputs p else
    [termDot sourceNumerator sourceNumerator,termDot (sourcePost 3) (sourcePost 3),termDet sourceBasis]++
      List.ofFn sourceNumerator++[sourceLeading 1 (by decide),sourceLeading 2 (by decide),sourceLeading 3 (by decide)]

end
end krylov.Correction.Certificate
