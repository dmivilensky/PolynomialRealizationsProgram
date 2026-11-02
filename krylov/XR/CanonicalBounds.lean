import krylov.XR.SkewCongruence
import krylov.XR.LocalRelative

/-!
Article: main_krylov, apH:canon.
Use: actual pair normalization, its exact relative-defect invariance, and
both amplification bounds. The operator-norm endpoints are the largest
eigenvalue and reciprocal smallest eigenvalue of the positive model.
Source: positive-root congruence and the C*-norm identity.
-/

/-!
Article: krylov, Lemma F.5 [apH:canon].

The canonical normalization preserves the actual relative norm, and the two operator-norm
estimates yield exactly the extreme-eigenvalue comparison. The two-pair formula has determinant
denominator.
For an SPD model, operator norm is λmax and inverse operator norm is 1/λmin; these equivalent
spectral forms explain the printed bounds. Comparability does not assert identical gate
decisions.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The positive root has exactly the squared spectral norm of the
original positive model. Article: main_krylov, apH:canon. -/
theorem metricRoot_norm_sq (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    ‖metricRoot T‖^2=‖T‖ := by
  have hs : star (metricRoot T)=metricRoot T := by
    rw [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,(metricRoot_isSymm T).eq]
  calc
    _ = ‖star (metricRoot T)*metricRoot T‖ := by rw [CStarRing.norm_star_mul_self,pow_two]
    _ = ‖T‖ := by rw [hs,metricRoot_square T hT]

/-- Reconstruction gives the lower amplification inequality even for
skew and nonsymmetric errors. Article: main_krylov, apH:canon. -/
theorem norm_le_model_norm_relativeBudget (T D : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    ‖D‖≤‖T‖*relativeBudget T D := by
  calc
    ‖D‖ = ‖metricRoot T*relativeOperator T D*metricRoot T‖ :=
      congrArg norm (relativeOperator_reconstruct T D hT).symm
    _ ≤ (‖metricRoot T‖*‖relativeOperator T D‖)*‖metricRoot T‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖metricRoot T‖^2*relativeBudget T D := by change _=_*‖relativeOperator T D‖; ring
    _ = _ := by rw [metricRoot_norm_sq T hT]

/-- The two exact amplification bounds in the canonical positive model.
For nonempty windows the denominators are its actual spectral endpoints.
Article: main_krylov, apH:canon. -/
theorem canonical_amplification (T D : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    ‖D‖≤‖T‖*relativeBudget T D ∧ relativeBudget T D≤‖T⁻¹‖*‖D‖ :=
  ⟨norm_le_model_norm_relativeBudget T D hT,relativeBudget_le_inverse_norm T D hT⟩

/-- The actual data-only pair normalizer, fixed by positive observed
curvatures rather than a freely chosen whitening. Article: apH:canon. -/
def pairNormalizer (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  diagonal (fun i=>(Real.sqrt (M i i))⁻¹)

/-- The canonical normalized model built from the actual observed pair
curvatures. Article: main_krylov, apH:canon, N_c. -/
def canonicalModel (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  pairNormalizer M*latest M*pairNormalizer M

/-- A positive observed model has positive actual diagonal curvatures.
Article: main_krylov, apH:canon. -/
theorem latest_diagonal_pos (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) (i : Fin p) :
    0<M i i := by
  have hh := hM.diag_pos (i := i)
  simpa only [latest,min_self,max_self] using hh

/-- The actual pair normalizer is invertible on the true positive-model
domain. Article: main_krylov, apH:canon. -/
theorem pairNormalizer_det_unit (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) :
    IsUnit (pairNormalizer M).det := by
  rw [pairNormalizer,det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero (Real.sqrt_pos.mpr (latest_diagonal_pos M hM i)).ne'

/-- Actual diagonal congruence gives exactly the printed entrywise
canonical defect. Article: main_krylov, apH:canon. -/
theorem canonicalDefect_congruence (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) :
    canonicalDefect M=pairNormalizer M*defect M*pairNormalizer M := by
  ext i j
  simp only [canonicalDefect,pairNormalizer,diagonal_mul,mul_diagonal]
  rw [Real.sqrt_mul (latest_diagonal_pos M hM i).le]
  rw [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- Positive pair normalization gives an actual positive canonical model.
Article: main_krylov, apH:canon. -/
theorem canonicalModel_posDef (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) :
    (canonicalModel M).PosDef := by
  have hu := (isUnit_iff_isUnit_det _).mpr (pairNormalizer_det_unit M hM)
  simpa only [conjTranspose_eq_transpose_of_trivial,canonicalModel,pairNormalizer,diagonal_transpose]
    using hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)

/-- The actual canonical defect has exactly the original relative norm,
without a conditioning loss from the pair scaling. Article: apH:canon. -/
theorem canonical_relativeBudget (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) :
    relativeBudget (canonicalModel M) (canonicalDefect M)=relativeBudget (latest M) (defect M) := by
  rw [canonicalDefect_congruence M hM]
  have hh := relativeBudget_skew_congruence (latest M) (defect M) (pairNormalizer M)
    hM (defect_transpose M) (pairNormalizer_det_unit M hM)
  simpa only [pairNormalizer,diagonal_transpose,canonicalModel] using hh

/-- Both canonical amplification inequalities apply to the literal
observed model and its literal relative defect. Article: apH:canon. -/
theorem canonical_defect_bounds (M : Matrix (Fin p) (Fin p) ℝ) (hM : (latest M).PosDef) :
    ‖canonicalDefect M‖≤‖canonicalModel M‖*relativeBudget (latest M) (defect M) ∧
    relativeBudget (latest M) (defect M)≤‖(canonicalModel M)⁻¹‖*‖canonicalDefect M‖ := by
  have hh := canonical_amplification (canonicalModel M) (canonicalDefect M) (canonicalModel_posDef M hM)
  rwa [canonical_relativeBudget M hM] at hh

end
end krylov.XR
