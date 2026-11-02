import krylov.OneGradient.XRFCTwoBasisOutput
import krylov.Methods.DirectionExecution
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true native final-launch program dictionary.
Use: the shared primitive last-row calculus applies to exactly the real
S or D implementation, on its actual old columns and observed images.
Source: genuine full-memory transcript coordinates and actual native
replay/direction dictionaries, without operator-image substitutions.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
variable {n : ℕ}

/-- The actual old native basis columns in their genuine newest-age
coordinates: recorded steps for S, actual replayed directions for D.
Use: one source-level dictionary for both implemented basis choices.
Article: main_krylov, thm:local(a), true native old columns. -/
def xrfcNativeColumns (directions : Bool) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  if directions then xrfcDExecutedDirection trial A g (k-1-i.val)
  else oneGradientStep (xrfcMethod fullMemory trial) A g (k-1-i.val)

/-- The actual old native observed image columns: returned step images
for S and the genuine data-only replayed images for D.
Use: no true unqueried varying-operator direction image replaces replay.
Article: main_krylov, thm:local(a), true native old images. -/
def xrfcNativeImages (directions : Bool) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  if directions then xrfcDExecutedImage trial A g (k-1-i.val)
  else A (k-1-i.val) (oneGradientStep (xrfcMethod fullMemory trial) A g (k-1-i.val))

/-- The actual next returned native gradient is precisely the genuine
finite observed virtual-launch program, in either real basis and on
arbitrary operators. No regularity, inverse or positivity premise is needed.
Use: primitive row estimates concern the true implemented gradient, not
an auxiliary program with the same quadratic reference behavior.
Article: main_krylov, thm:local(a), exact both-native launch dictionary.
Proof: actual full-memory coordinate theorems identify the genuine virtual
correction, virtual gradient and subsequent conjugacy direction on their
true S or D observations. Substitute these exact finite coordinates into
the original real evaluated step and returned-gradient recursion. -/
theorem xrfc_native_last_launch (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let m := xrfcBasisMethod directions trial
    let H := oneGradientRun m A g k
    let s := xrfcNativeColumns directions trial A g k
    let y := xrfcNativeImages directions trial A g k
    let w := modelCoefficients s (pairModel s y) H.gradient
    let gv := H.gradient+combine y w
    let d := conjugacyDirection s y gv
    oneGradientGradient m A g (k+1)=H.gradient+A k (combine s w+trial H • d) := by
  cases directions with
  | false =>
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m A g k
    have hv := oneGradient_full_virtual_coordinates m A g k
    have hd := oneGradient_full_direction_coordinates m A g
      (virtualGradient (selectedWindow fullMemory H) H.gradient) k
    change H.gradient+A k
      (virtualCorrection (selectedWindow fullMemory H) H.gradient+
        trial H • windowDirection (selectedWindow fullMemory H)
          (virtualGradient (selectedWindow fullMemory H) H.gradient))=_
    rw [hv.1,hd,hv.2]
    rfl
  | true =>
    let m := xrfcDMethod fullMemory trial
    let H := oneGradientRun m A g k
    have hv := xrfcD_virtual_coordinates trial A g k
    have hd := xrfcD_direction_coordinates trial A g k
    change H.gradient+A k (virtualCorrection (xrfcDWindow trial A g k) H.gradient+
      trial H • xrfcDExecutedDirection trial A g k)=_
    rw [hv.1,hd,hv.2]
    rfl

end
end krylov.OneGradient
