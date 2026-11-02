import krylov.Convergence.SS1FDiagonal
import krylov.Convergence.SecantWindowSource

/-!
Article: main_krylov, thm:ss1F.
Use: normalize the genuine corrected value model without changing its actual
executed query, and identify each real corrected diagonal exactly. The model
is still formed from actual values and first derivatives.
Source: exact observed-model rescaling and the proved anchored trapezoid
estimate, with the genuine gradient/differential chain rule.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Secant krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual observed value model after genuine column-length rescaling. -/
def ss1FNormalizedModel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  rescaleModel (valueCorrectedModel f (fun x=>innerSL ℝ (G x)) a s l) (fun i=>‖s i‖⁻¹)

/-- Its real normalized error against the limiting identity Gram matrix. -/
def ss1FNormalizedError {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ss1FNormalizedModel f G a s l-crossGram (unitWindow s) (unitWindow s)

/-- Normalization leaves the actual value-corrected physical query unchanged. -/
theorem ss1FPoint_normalized_model (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a s : Fin n → EuclideanSpace ℝ (Fin n)) (l : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hs : ∀ i,s i≠0)
    (hV : IsUnit (windowMatrix (unitWindow s)).det) :
    ss1FPoint f G a s l x=x-cgOperator
      (inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l))⁻¹ (G x) := by
  have he := modelCorrection_rescale s (valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l)
    (fun i=>‖s i‖⁻¹) (unitWindow_diagonal_unit s hs) (G x)
  rw [ss1FPoint,←he]
  change x+combine (unitWindow s) (modelCoefficients (unitWindow s)
    (ss1FNormalizedModel f G a s l) (G x))=_
  rw [square_model_correction _ _ _ hV,sub_eq_add_neg]

/-- The actual corrected physical model has exactly its computed normalized
error congruence; no model-error identity is assumed. -/
theorem ss1F_normalized_model_error (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a s : Fin n → EuclideanSpace ℝ (Fin n)) (l : Fin n → ℝ)
    (hV : IsUnit (windowMatrix (unitWindow s)).det) :
    inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)-1=
      inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedError f G a s l) := by
  rw [ss1FNormalizedError,crossGram_windowMatrix]
  simp only [inverseCongruence,Matrix.mul_sub,Matrix.sub_mul]
  change inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)-1=
    inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)-
      inverseCongruence (windowMatrix (unitWindow s))
        ((windowMatrix (unitWindow s))ᵀ*windowMatrix (unitWindow s))
  rw [inverseCongruence_gram _ hV]

/-- Every normalized observed diagonal is its actual scalar corrected
curvature divided by its actual squared step length. -/
theorem ss1FNormalizedModel_diagonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) (i : Fin n) :
    ss1FNormalizedModel f G a s l i i=
      ‖s i‖⁻¹*correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)*‖s i‖⁻¹ := by
  simp only [ss1FNormalizedModel,rescaleModel,diagonal_mul,mul_diagonal,
    valueCorrectedModel,Matrix.sub_apply,latest,min_self,max_self,diagonal_apply_eq,
    correctedValueDiagonal]

/-- The raw corrected matrix is exactly the genuine latest pair model plus
the measured diagonal correction; the image vectors are true differences
of endpoint gradients. -/
theorem valueCorrectedModel_eq_ss1Model {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) :
    valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l=
      ss1Model s (fun i=>G (a i+s i)-G (a i))-
      diagonal (fun i=>12*l i*segmentValueDefect f (fun z=>innerSL ℝ (G z)) (a i) (s i)) := by
  unfold valueCorrectedModel ss1Model
  congr 1
  congr 1
  ext i j
  change inner ℝ (G (a j+s j)) (s i)-inner ℝ (G (a j)) (s i)=
    inner ℝ (s i) (G (a j+s j)-G (a j))
  rw [inner_sub_right,real_inner_comm (s i),real_inner_comm (s i)]

/-- The complete normalized corrected-data matrix, including its actual
value-dependent diagonal, has an exact observed-data decomposition. -/
theorem ss1FNormalizedError_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) :
    ss1FNormalizedError f G a s l=
      windowDataError (unitWindow s)
        (unitWindowImages s (fun i=>G (a i+s i)-G (a i)))-
      diagonal (fun i=>‖s i‖⁻¹*(12*l i*
        segmentValueDefect f (fun z=>innerSL ℝ (G z)) (a i) (s i))*‖s i‖⁻¹) := by
  rw [ss1FNormalizedError,ss1FNormalizedModel,valueCorrectedModel_eq_ss1Model]
  have hraw := ss1Model_rescale s (fun i=>G (a i+s i)-G (a i)) (fun i=>‖s i‖⁻¹)
  unfold rescaleModel at hraw
  ext i j
  simp only [rescaleModel,Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_apply]
  rw [←hraw]
  simp only [unitWindow,unitWindowImages,windowDataError,Matrix.sub_apply,
    mul_diagonal,diagonal_apply]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    ring
  · simp only [hij,ite_false,zero_mul,sub_zero]

/-- The genuine scalar differential associated to an actual gradient. -/
def gradientDifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → E) (x : E) : E →L[ℝ] ℝ := innerSL ℝ (G x)

/-- The genuine Hessian bilinear form associated to its actual vector action. -/
def gradientHessian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E → E →L[ℝ] E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp (H x)

theorem gradientDifferential_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → E) (H : E → E →L[ℝ] E) (x : E) (hG : HasFDerivAt G (H x) x) :
    HasFDerivAt (gradientDifferential G) (gradientHessian H x) x :=
  (innerSL ℝ).hasFDerivAt.comp x hG

/-- Actual scalar diagonal budgets pass through genuine step normalization
without an inverse-step-length loss. -/
theorem ss1FNormalizedError_diagonal_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ)
    (hs : ∀ i,s i≠0) (i : Fin n) {B : ℝ}
    (hdiag : |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)-‖s i‖^2|≤
      B*‖s i‖^2) : |ss1FNormalizedError f G a s l i i|≤B := by
  change |ss1FNormalizedModel f G a s l i i-inner ℝ (unitWindow s i) (unitWindow s i)|≤B
  rw [real_inner_self_eq_norm_sq,unitWindow_norm s hs,one_pow,ss1FNormalizedModel_diagonal]
  have hn : ‖s i‖≠0 := norm_ne_zero_iff.mpr (hs i)
  have he : ‖s i‖⁻¹*correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)*‖s i‖⁻¹-1=
      ‖s i‖⁻¹*(correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)-‖s i‖^2)*‖s i‖⁻¹ := by
    field_simp
  rw [he,abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiag (inv_nonneg.mpr (norm_nonneg _)))
      (inv_nonneg.mpr (norm_nonneg _))).trans_eq (by field_simp)

/-- Actual normalized pair and corrected-diagonal budgets control the whole
genuine corrected matrix in its spectral norm. -/
theorem ss1FNormalizedError_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ)
    (hs : ∀ i,s i≠0) {ε : ℝ} (hε : 0≤ε)
    (hpair : ∀ i,‖unitWindowImages s (fun j=>G (a j+s j)-G (a j)) i-unitWindow s i‖≤ε)
    (hdiag : ∀ i,|correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)-‖s i‖^2|≤
      ε*‖s i‖^2) : ‖ss1FNormalizedError f G a s l‖≤n*ε := by
  apply (krylov.LinearAlgebra.spectral_le_hsNorm _).trans
  apply krylov.LinearAlgebra.hsNorm_le_dimension _ hε
  intro i j
  by_cases hij : i=j
  · subst j
    exact ss1FNormalizedError_diagonal_bound f G a s l hs i (hdiag i)
  · rw [ss1FNormalizedError_eq,Matrix.sub_apply,diagonal_apply_ne _ hij,sub_zero,
      windowDataError_entry]
    have hh := norm_inner_le_norm (𝕜:=ℝ) (unitWindow s (min i j))
      (unitWindowImages s (fun j=>G (a j+s j)-G (a j)) (max i j)-unitWindow s (max i j))
    rw [unitWindow_norm s hs,one_mul,Real.norm_eq_abs] at hh
    exact hh.trans (hpair _)

/-- Only newer image errors are needed off the diagonal. Consequently the
oldest raw secant error can disappear completely after its genuine value
diagonal correction. -/
theorem ss1FNormalizedError_newer_image_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin (n+1) → E) (l : Fin (n+1) → ℝ)
    (hs : ∀ i,s i≠0) {ε : ℝ} (hε : 0≤ε)
    (hpair : ∀ i,i≠0 →
      ‖unitWindowImages s (fun j=>G (a j+s j)-G (a j)) i-unitWindow s i‖≤ε)
    (hdiag : ∀ i,|correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) (a i) (s i) (l i)-‖s i‖^2|≤
      ε*‖s i‖^2) : ‖ss1FNormalizedError f G a s l‖≤((n+1:ℕ):ℝ)*ε := by
  apply (krylov.LinearAlgebra.spectral_le_hsNorm _).trans
  apply krylov.LinearAlgebra.hsNorm_le_dimension _ hε
  intro i j
  by_cases hij : i=j
  · subst j
    exact ss1FNormalizedError_diagonal_bound f G a s l hs i (hdiag i)
  · rw [ss1FNormalizedError_eq,Matrix.sub_apply,diagonal_apply_ne _ hij,sub_zero,
      windowDataError_entry]
    have hm : max i j≠0 := by
      intro hz
      have hi : i=0 := le_antisymm (hz ▸ le_max_left i j) (Fin.zero_le i)
      have hj : j=0 := le_antisymm (hz ▸ le_max_right i j) (Fin.zero_le j)
      exact hij (hi.trans hj.symm)
    have hh := norm_inner_le_norm (𝕜:=ℝ) (unitWindow s (min i j))
      (unitWindowImages s (fun j=>G (a j+s j)-G (a j)) (max i j)-unitWindow s (max i j))
    rw [unitWindow_norm s hs,one_mul,Real.norm_eq_abs] at hh
    exact hh.trans (hpair _ hm)

end
end krylov.Convergence
