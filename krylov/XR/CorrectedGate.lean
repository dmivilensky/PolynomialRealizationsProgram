import krylov.XR.CorrectedWindowBounds

/-!
Article: main_krylov, cor:xrF, genuine corrected Hermitian gate.
Use: a primitive corrected-model approximation forces the actual complex
test, with the original observed skew matrix. The positive model and its
inverse budget are derived from true Hessian coercivity and G2.
Source: the proved exact Hermitian/relative-norm equivalence and congruence.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The implemented corrected test is exactly the general model/skew
Hermitian test of the relative-metric theorem. -/
theorem correctedWindowPasses_iff_test (theta : ℝ) (W : List (PairObservation E)) :
    correctedWindowPasses theta W ↔
      (hermitianTest theta (storedValueModel W) (defect (storedPairing W))).PosDef := by
  have he : (storedValueModel W).map Complex.ofReal +
      (Complex.I / (theta : ℂ)) • (defect (storedPairing W)).map Complex.ofReal =
      hermitianTest theta (storedValueModel W) (defect (storedPairing W)) := by
    ext i j
    simp only [hermitianTest, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  unfold correctedWindowPasses
  rw [he]

/-- Any genuinely small symmetric model error, rather than a supplied
positive-model certificate, forces the actual Hermitian gate. -/
theorem local_general_hermitian_gate (theta : ℝ) (htheta : 0 < theta)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hTsym : T.IsSymm) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin p → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * (p : ℝ) * epsilon / localCoercivity mu sigma < theta) :
    (hermitianTest theta T (defect (crossGram s y))).PosDef := by
  have hd := local_general_model_domains H hH s y T hs mu sigma epsilon hmu hsigma he
    hpositive hgain hy hmodel hsmall
  have hc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hT : T.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hTsym)
    intro w hw
    have hn : 0 < ‖WithLp.toLp 2 w‖ ^ 2 := sq_pos_of_pos
      (norm_pos_iff.mpr (fun hz => hw ((WithLp.toLp_injective 2) hz)))
    simpa only [star_trivial] using (mul_pos hc hn).trans_le (hd.1 w)
  apply (hermitianTest_posDef_iff theta htheta T _ hTsym (defect_transpose _)).2
  refine ⟨hT, ?_⟩
  have hrel : relativeBudget T (defect (crossGram s y)) ≤
      2 * (p : ℝ) * epsilon / localCoercivity mu sigma := by
    calc
      _ ≤ ‖T⁻¹‖ * ‖defect (crossGram s y)‖ := relativeBudget_le_inverse_norm _ _ hT
      _ ≤ (localCoercivity mu sigma)⁻¹ * (2 * (p : ℝ) * epsilon) :=
        mul_le_mul hd.2.2.1 (local_defect_norm H hH s y hs he hy) (norm_nonneg _) (inv_nonneg.mpr hc.le)
      _ = _ := by ring
  exact hrel.trans_lt hgate

/-- Actual raw corrected windows pass their complex test from primitive
normalized source data, with exact pair-rescaling invariance. -/
theorem correctedWindowPasses_of_errors (theta : ℝ) (htheta : 0 < theta)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (W : List (PairObservation E)) (hs : ∀ i, storedSteps W i ≠ 0)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages W i - H (storedSteps W i)‖ ≤ epsilon * ‖storedSteps W i‖)
    (hmodel : ‖rescaleModel (storedValueModel W) (fun i => ‖storedSteps W i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps W))‖ ≤ (W.length : ℝ) * epsilon)
    (hsmall : (W.length : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * (W.length : ℝ) * epsilon / localCoercivity mu sigma < theta) :
    correctedWindowPasses theta W := by
  let s := storedSteps W
  let y := storedImages W
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  let T := rescaleModel (storedValueModel W) c
  have hsym : T.IsSymm := by
    change (diagonal c * storedValueModel W * diagonal c)ᵀ = diagonal c * storedValueModel W * diagonal c
    rw [transpose_mul, transpose_mul, diagonal_transpose, (storedValueModel_isSymm W).eq]
    noncomm_ring
  have hpass := local_general_hermitian_gate theta htheta H hH sn yn T hsym
    (krylov.Convergence.unitWindow_norm s hs) mu sigma epsilon hmu hsigma he hpositive hgain
    (unitWindow_reference_error H s y hs epsilon hy) hmodel hsmall hgate
  have hD : defect (crossGram sn yn) = rescaleModel (defect (storedPairing W)) c := by
    rw [show crossGram sn yn = rescaleModel (crossGram s y) c from
      krylov.Convergence.window_crossGram_rescale s y c, defect_rescaleModel]
    rfl
  rw [hD] at hpass
  apply (correctedWindowPasses_iff_test theta W).2
  apply (hermitianTest_congruence_iff theta _ _ (diagonal c)
    (krylov.Convergence.unitWindow_diagonal_unit s hs)).mp
  simpa only [T, rescaleModel, diagonal_transpose] using hpass

end
end krylov.XR
