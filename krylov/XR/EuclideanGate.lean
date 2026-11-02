import krylov.XR.EuclideanWindowBounds
import krylov.XR.CorrectedGate

/-!
Article: main_krylov, cor:xrF, genuine Euclidean corrected Hermitian gate.
Use: derive the real complex gate from normalized true model errors.
Source: the proved generic Hermitian/relative-budget equivalence and exact
raw-pair normalization; no successful branch is assumed.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The implemented corrected test is exactly the general model/skew
Hermitian test of the relative-metric theorem. -/
theorem euclideanCorrectedWindowPasses_iff_test (theta : ℝ) (x : E) (W : List (PairObservation E)) :
    euclideanCorrectedWindowPasses theta x W ↔
      (hermitianTest theta (euclideanStoredValueModel x W) (defect (storedPairing W))).PosDef := by
  have he : (euclideanStoredValueModel x W).map Complex.ofReal +
      (Complex.I / (theta : ℂ)) • (defect (storedPairing W)).map Complex.ofReal =
      hermitianTest theta (euclideanStoredValueModel x W) (defect (storedPairing W)) := by
    ext i j
    simp only [hermitianTest, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  unfold euclideanCorrectedWindowPasses
  rw [he]

/-- Actual raw corrected windows pass their complex test from primitive
normalized source data, with exact pair-rescaling invariance. -/
theorem euclideanCorrectedWindowPasses_of_errors (theta : ℝ) (htheta : 0 < theta) (x : E)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (W : List (PairObservation E)) (hs : ∀ i, storedSteps W i ≠ 0)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages W i - H (storedSteps W i)‖ ≤ epsilon * ‖storedSteps W i‖)
    (hmodel : ‖rescaleModel (euclideanStoredValueModel x W) (fun i => ‖storedSteps W i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps W))‖ ≤ (W.length : ℝ) * epsilon)
    (hsmall : (W.length : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * (W.length : ℝ) * epsilon / localCoercivity mu sigma < theta) :
    euclideanCorrectedWindowPasses theta x W := by
  let s := storedSteps W
  let y := storedImages W
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  let T := rescaleModel (euclideanStoredValueModel x W) c
  have hsym : T.IsSymm := by
    change (diagonal c * euclideanStoredValueModel x W * diagonal c)ᵀ = diagonal c * euclideanStoredValueModel x W * diagonal c
    rw [transpose_mul, transpose_mul, diagonal_transpose, (euclideanStoredValueModel_isSymm x W).eq]
    noncomm_ring
  have hpass := local_general_hermitian_gate theta htheta H hH sn yn T hsym
    (krylov.Convergence.unitWindow_norm s hs) mu sigma epsilon hmu hsigma he hpositive hgain
    (unitWindow_reference_error H s y hs epsilon hy) hmodel hsmall hgate
  have hD : defect (crossGram sn yn) = rescaleModel (defect (storedPairing W)) c := by
    rw [show crossGram sn yn = rescaleModel (crossGram s y) c from
      krylov.Convergence.window_crossGram_rescale s y c, defect_rescaleModel]
    rfl
  rw [hD] at hpass
  apply (euclideanCorrectedWindowPasses_iff_test theta x W).2
  apply (hermitianTest_congruence_iff theta _ _ (diagonal c)
    (krylov.Convergence.unitWindow_diagonal_unit s hs)).mp
  simpa only [T, rescaleModel, diagonal_transpose] using hpass

end
end krylov.XR
