import krylov.Methods.RepeatedCorrection
import krylov.Methods.StaticTermination
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, lem:projected-residual and apD:eq:resid.
Use: normalize the actual rectangular model solve without changing its physical
correction, then propagate the genuine residual through repeated RFC queries.
Source: diagonal change of coordinates and the nonsingular-inverse API in
mathlib; the execution is the existing observed-gradient correction protocol.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal change of coordinates in an actual rectangular stored window.
Use: column-length normalization does not require a square physical window.
Article: main_krylov, lem:projected-residual, T=UD. -/
def rescaleWindow (s : ι → E) (d : ι → ℝ) : ι → E := fun i => d i • s i

/-- The model in the same diagonally rescaled window coordinates.
Use: both exterior normalizers belong to the coefficient space.
Article: main_krylov, lem:projected-residual, normalized H. -/
def rescaleModel (H : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal d * H * diagonal d

/-- The actual projected residual in its Euclidean coefficient norm.
Use: avoids the supremum norm on coordinate functions in all RFC bounds.
Article: main_krylov, lem:projected-residual, ρ. -/
def projectedResidual (s : ι → E) (g : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (coordinates s g)

/-- Rescaled physical coordinates equal the diagonal action on the original coordinates.
Use: transfer the genuine observed right-hand side to normalized coordinates.
Article: main_krylov, lem:projected-residual.
Proof: real inner products are linear in the rescaled first vector. -/
theorem coordinates_rescale (s : ι → E) (d : ι → ℝ) (g : E) :
    coordinates (rescaleWindow s d) g=diagonal d *ᵥ coordinates s g := by
  ext i
  simp only [coordinates, rescaleWindow, real_inner_smul_left, mulVec_diagonal]

/-- The true Euclidean projected residual rescales by the actual diagonal coefficient operator.
Use: locally bounded actual column normalizers preserve the genuine first-order residual estimate.
Article: main_krylov, lem:projected-residual, normalized ρ.
Proof: lift the proved exact coordinate rescaling identity to its genuine Euclidean normed space. -/
theorem projectedResidual_rescale (s : ι → E) (d : ι → ℝ) (g : E) :
    projectedResidual (rescaleWindow s d) g=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal d) (projectedResidual s g) := by
  change WithLp.toLp 2 (coordinates (rescaleWindow s d) g)=_
  rw [coordinates_rescale]
  rfl

/-- Combining a rescaled window applies the diagonal to its coefficients.
Use: compare physical corrections before and after normalization.
Article: main_krylov, lem:projected-residual.
Proof: associate each actual scalar multiple in the finite physical sum. -/
theorem combine_rescale (s : ι → E) (d c : ι → ℝ) :
    combine (rescaleWindow s d) c=combine s (diagonal d *ᵥ c) := by
  simp only [combine, rescaleWindow, mulVec_diagonal, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A nonsingular diagonal coordinate change cancels around the actual inverse model.
Use: justify normalization of rectangular-window solves by coefficient algebra alone.
Article: main_krylov, lem:projected-residual.
Proof: reverse the inverse product and cancel the two genuine diagonal inverses. -/
theorem rescaleModel_inverse (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) :
    diagonal d * (rescaleModel H d)⁻¹ * diagonal d=H⁻¹ := by
  -- All inverses here act in the finite coefficient space, even for rectangular windows.
  rw [rescaleModel, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = (diagonal d * (diagonal d)⁻¹) * H⁻¹ * ((diagonal d)⁻¹ * diagonal d) := by
      noncomm_ring
    _ = _ := by rw [mul_nonsing_inv _ hd, nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_one]

/-- The actual computed physical correction is unchanged by a nonsingular column rescaling.
Use: normalized estimates apply to the original executed RFC coefficient solve.
Article: main_krylov, lem:projected-residual, χ=Uw=Tŵ.
Proof: move the two exterior diagonal factors into the actual inverse and cancel them. -/
theorem modelCorrection_rescale (s : ι → E) (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) (g : E) :
    combine (rescaleWindow s d) (modelCoefficients (rescaleWindow s d) (rescaleModel H d) g)=
      combine s (modelCoefficients s H g) := by
  rw [combine_rescale, modelCoefficients, coordinates_rescale, mulVec_neg,
    mulVec_mulVec, mulVec_mulVec, rescaleModel_inverse H d hd]
  rfl

/-- The true physical compression of the correction operator into a stored window.
Use: this matrix is formed for the proof; the method queries only its chosen correction.
Article: main_krylov, lem:projected-residual, UᵀBU. -/
def correctionCompression (s : ι → E) (B : E →L[ℝ] E) : Matrix ι ι ℝ :=
  crossGram s (fun i => B (s i))

/-- True rectangular operator compression transforms by the genuine coefficient diagonal congruence.
Use: normalized model errors are actual bounded-diagonal transforms of the raw observed errors.
Article: main_krylov, lem:projected-residual, N=D(UᵀBU−H)D.
Proof: move both real column scalars through the actual operator and the actual inner product. -/
theorem correctionCompression_rescale (s : ι → E) (d : ι → ℝ) (B : E →L[ℝ] E) :
    correctionCompression (rescaleWindow s d) B=rescaleModel (correctionCompression s B) d := by
  ext i j
  simp only [correctionCompression,crossGram,rescaleWindow,map_smul,real_inner_smul_left,
    real_inner_smul_right,rescaleModel,diagonal_mul,mul_diagonal]
  ring

omit [DecidableEq ι] in
/-- The actual projected operator action on a physical window combination is its genuine compressed matrix action.
Use: a nonsingular real compression certifies actual window independence.
Article: main_krylov, lem:projected-residual, actual compressed action.
Proof: move the actual operator through the physical finite sum and apply the proved coordinate-combination identity. -/
theorem coordinates_operator_combine (s : ι → E) (B : E →L[ℝ] E) (c : ι → ℝ) :
    coordinates s (B (combine s c))=correctionCompression s B *ᵥ c := by
  have he : B (combine s c)=combine (fun i => B (s i)) c := by simp only [combine,map_sum,map_smul]
  rw [he]
  exact coordinates_combine s _ c

/-- Any genuine nonsingular operator compression proves linear independence of the actual physical window.
Use: actual positive reference model domains also justify the raw physical Gram domain.
Article: main_krylov, lem:projected-residual, nondegenerate augmented window.
Proof: a zero physical combination has zero compressed coordinates; the
genuine compressed inverse then forces every actual coefficient to vanish. -/
theorem compression_unit_independent (s : ι → E) (B : E →L[ℝ] E)
    (hu : IsUnit (correctionCompression s B).det) : LinearIndependent ℝ s := by
  -- Nonsingularity is used only after producing the true zero compressed action.
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hphys : combine s c=0 := hc
  have hz : correctionCompression s B *ᵥ c=0 := by
    rw [← coordinates_operator_combine,hphys,map_zero]
    ext i
    exact inner_zero_right _
  have he := congrArg (fun a => (correctionCompression s B)⁻¹ *ᵥ a) hz
  rw [mulVec_mulVec,nonsing_inv_mul _ hu,one_mulVec,mulVec_zero] at he
  exact fun i => congrFun he i

/-- A genuine nonsingular operator compression gives a genuine nonsingular Euclidean Gram matrix for the actual window.
Use: the recorded-step coordinate transfer has its actual inverse-Gram domain discharged.
Article: main_krylov, lem:projected-residual, true Gram inverse domain.
Proof: the compression proves actual physical independence; the already
proved positive-operator Gram theorem applied to the identity gives positive Gram determinant. -/
theorem gram_unit_of_compression_unit (s : ι → E) (B : E →L[ℝ] E)
    (hu : IsUnit (correctionCompression s B).det) : IsUnit (crossGram s s).det := by
  have hp : (crossGram s s).PosDef := operatorGram_posDef (ContinuousLinearMap.id ℝ E)
    (by intro v w; rfl) (fun v hv => by
      simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using
        sq_pos_of_pos (norm_pos_iff.mpr hv)) (compression_unit_independent s B hu)
  exact isUnit_iff_ne_zero.mpr hp.det_pos.ne'

/-- The actual physical model correction has its exact projected-error recurrence.
Use: no symmetry or square-window assumption is needed for the correction identity.
Article: main_krylov, apD:eq:resid.
Proof: expand the actual linear oracle action and cancel the solved model equation. -/
theorem modelCorrection_projected (s : ι → E) (H : Matrix ι ι ℝ)
    (hH : IsUnit H.det) (B : E →L[ℝ] E) (g : E) :
    coordinates s (g+B (combine s (modelCoefficients s H g)))=
      -((correctionCompression s B-H)*H⁻¹) *ᵥ coordinates s g := by
  -- Expand the executed oracle action before collecting the model residual.
  have he : coordinates s (g+B (combine s (modelCoefficients s H g)))=
      coordinates s g+correctionCompression s B *ᵥ modelCoefficients s H g := by
    rw [show B (combine s (modelCoefficients s H g))=
      combine (fun i => B (s i)) (modelCoefficients s H g) by simp only [combine, map_sum, map_smul]]
    ext i
    exact (inner_add_right _ _ _).trans (congrArg (fun t => coordinates s g i+t)
      (congrFun (coordinates_combine s _ _) i))
  rw [he, modelCoefficients, mulVec_neg, neg_mulVec, Matrix.sub_mul, sub_mulVec,
    mul_nonsing_inv _ hH, one_mulVec, mulVec_mulVec]
  abel

/-- The actual normalized residual obeys the exact normalized error/inverse recurrence.
Use: both the physical correction and its right-hand side are those actually executed.
Article: main_krylov, lem:projected-residual, ρ₊=−N Ĥ⁻¹ρ.
Proof: identify the actual correction with its rescaled solve and apply the proved projected identity. -/
theorem normalizedCorrection_projected (s : ι → E) (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) (hH : IsUnit (rescaleModel H d).det)
    (B : E →L[ℝ] E) (g : E) :
    projectedResidual (rescaleWindow s d) (g+B (combine s (modelCoefficients s H g)))=
      -(Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((correctionCompression (rescaleWindow s d) B-rescaleModel H d)*(rescaleModel H d)⁻¹)
        (projectedResidual (rescaleWindow s d) g)) := by
  rw [← modelCorrection_rescale s H d hd g]
  change WithLp.toLp 2 (coordinates (rescaleWindow s d) _)=_
  rw [modelCorrection_projected _ _ hH]
  ext i
  simp only [neg_mulVec]
  rfl

/-- Each actual normalized RFC correction contracts its residual by the normalized model error times the inverse bound.
Use: the estimate has no dependence on the individual physical column lengths.
Article: main_krylov, lem:projected-residual, normalized residual bound.
Proof: the exact normalized recurrence and two spectral operator-norm inequalities. -/
theorem normalizedCorrection_bound (s : ι → E) (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) (hH : IsUnit (rescaleModel H d).det)
    (B : E →L[ℝ] E) (g : E) :
    ‖projectedResidual (rescaleWindow s d) (g+B (combine s (modelCoefficients s H g)))‖≤
      ‖correctionCompression (rescaleWindow s d) B-rescaleModel H d‖*
        ‖(rescaleModel H d)⁻¹‖*‖projectedResidual (rescaleWindow s d) g‖ := by
  -- Both factors use their genuine coefficient-space spectral norms after the exact physical normalization.
  rw [normalizedCorrection_projected s H d hd hH, norm_neg]
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ)
    ((correctionCompression (rescaleWindow s d) B-rescaleModel H d)*(rescaleModel H d)⁻¹)).le_opNorm
      (projectedResidual (rescaleWindow s d) g)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  exact ho.trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
    (norm_nonneg (projectedResidual (rescaleWindow s d) g)))

/-- Repeated actual observed-gradient corrections multiply the same normalized residual bound.
Use: this concerns the implemented finite adaptive tree, including its genuine updated right-hand sides.
Article: main_krylov, lem:projected-residual, fixed-model repeated corrections.
Proof: induction unfolds the executed next query and applies the one-correction bound. -/
theorem repeatedModel_projected_bound (s : ι → E) (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) (hH : IsUnit (rescaleModel H d).det)
    (B : E →L[ℝ] E) (g : E) (c : ℕ) :
    ‖projectedResidual (rescaleWindow s d)
      (runCorrections (repeatedModelTree s H c g) B g).gradient‖≤
      (‖correctionCompression (rescaleWindow s d) B-rescaleModel H d‖*
        ‖(rescaleModel H d)⁻¹‖)^c*‖projectedResidual (rescaleWindow s d) g‖ := by
  -- The next right-hand side is the actual gradient returned by the preceding query.
  induction c generalizing g with
  | zero => simp only [repeatedModelTree, runCorrections, pow_zero, one_mul, le_refl]
  | succ c ih =>
    change ‖projectedResidual (rescaleWindow s d)
      (runCorrections (repeatedModelTree s H c _) B _).gradient‖≤_
    exact (ih _).trans ((mul_le_mul_of_nonneg_left
      (normalizedCorrection_bound s H d hd hH B g) (pow_nonneg (mul_nonneg (norm_nonneg _)
        (norm_nonneg _)) c)).trans_eq (by rw [pow_succ]; ring))

/-- The physical synthesis energy is exactly the quadratic form of the actual column Gram matrix.
Use: control a rectangular correction by its normalized coefficient norm.
Article: main_krylov, lem:projected-residual, TᵀT.
Proof: expand both finite physical sums in their real inner product. -/
theorem combine_norm_sq (s : ι → E) (c : ι → ℝ) :
    ‖combine s c‖^2=inner ℝ (WithLp.toLp 2 c)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram s s) (WithLp.toLp 2 c)) := by
  rw [Matrix.inner_toEuclideanCLM, ← real_inner_self_eq_norm_sq]
  simp only [combine, crossGram, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [real_inner_comm (s j) (s i)]; ring

/-- The actual rectangular synthesis norm is bounded by the square root of its Gram bound.
Use: the correction constant depends on normalized conditioning, never on raw step lengths.
Article: main_krylov, lem:projected-residual, ‖Tŵ‖≤√b‖ŵ‖.
Proof: Cauchy--Schwarz and the genuine Euclidean operator norm bound the exact synthesis energy. -/
theorem combine_norm_le (s : ι → E) (c : ι → ℝ) {b : ℝ}
    (hb : 0≤b) (hgram : ‖crossGram s s‖≤b) :
    ‖combine s c‖≤Real.sqrt b*‖WithLp.toLp 2 c‖ := by
  -- Compare nonnegative squared norms so that no physical synthesis operator needs an inverse.
  have hi := real_inner_le_norm (WithLp.toLp 2 c)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram s s) (WithLp.toLp 2 c))
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram s s)).le_opNorm (WithLp.toLp 2 c)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  have he : ‖combine s c‖^2≤b*‖WithLp.toLp 2 c‖^2 := by
    rw [combine_norm_sq]
    calc
      _ ≤ ‖WithLp.toLp 2 c‖*(‖crossGram s s‖*‖WithLp.toLp 2 c‖) :=
        hi.trans (mul_le_mul_of_nonneg_left ho (norm_nonneg _))
      _ ≤ b*‖WithLp.toLp 2 c‖^2 := by nlinarith [norm_nonneg (WithLp.toLp 2 c)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hb]

/-- The actual physical correction satisfies its normalized inverse/Gram bound.
Use: applies to any rectangular window after a genuine diagonal normalization.
Article: main_krylov, lem:projected-residual, ‖χ‖≤C‖ρ‖.
Proof: replace the physical correction by its rescaled solve, then bound synthesis and inverse action. -/
theorem normalizedCorrection_movement_bound (s : ι → E) (H : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : IsUnit (diagonal d).det) (g : E) {b : ℝ} (hb : 0≤b)
    (hgram : ‖crossGram (rescaleWindow s d) (rescaleWindow s d)‖≤b) :
    ‖combine s (modelCoefficients s H g)‖≤Real.sqrt b*‖(rescaleModel H d)⁻¹‖*
      ‖projectedResidual (rescaleWindow s d) g‖ := by
  -- The true physical movement is first rewritten as synthesis in the actual rescaled rectangular window.
  rw [← modelCorrection_rescale s H d hd g]
  have he : WithLp.toLp 2 (modelCoefficients (rescaleWindow s d) (rescaleModel H d) g)=
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) ((rescaleModel H d)⁻¹)
        (projectedResidual (rescaleWindow s d) g)) := by ext i; rfl
  have hc := combine_norm_le (rescaleWindow s d)
    (modelCoefficients (rescaleWindow s d) (rescaleModel H d) g) hb hgram
  rw [he, norm_neg] at hc
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) ((rescaleModel H d)⁻¹)).le_opNorm
    (projectedResidual (rescaleWindow s d) g)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  exact (hc.trans (mul_le_mul_of_nonneg_left ho (Real.sqrt_nonneg _))).trans_eq (by ring)

end
end krylov.Methods
