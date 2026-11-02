import krylov.Methods.DirectionStaircase
import krylov.Stability.UniformConjugacy
import krylov.Stability.WeightedCGFlags

/-!
Article: main_krylov, apB:lem:UAsteps and thm:A, genuine full-cycle FC direction basis.
Use: derive a uniformly conditioned actual canonical direction basis from
real defined solves and spectral operator budgets, including zero final steps.
Source: the genuine direction staircase, actual old-image conjugacy and
proved dimension-only normalized Gram and inverse estimates.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual defined FC directions annihilate the real earlier direction images when the earlier step enters a later defined solve.
Use: no current or final line scalar is divided by.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual next solve forces the earlier retained step nonzero;
cancel its nonzero real line scalar in the genuine old-image conjugacy equation. -/
theorem fullFC_direction_image_conjugate (A : ℕ → E →L[ℝ] E) (g : E) {i k : ℕ} (hi : i<k)
    (hnext : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))).det)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det) :
    inner ℝ (fcDirection fullMemory A g k) (A i (fcDirection fullMemory A g i))=0 := by
  -- Only the genuinely retained earlier step is divided by; the current line scalar can be zero.
  have hn := fullFC_step_ne_of_next_solve A g i hnext
  have hα : lineLength (fcGradient fullMemory A g i) (fcDirection fullMemory A g i)
      (A i (fcDirection fullMemory A g i))≠0 := by
    intro hz
    apply hn
    simp only [fcStep,hz,zero_smul]
  have hc := fullFC_direction_conjugate A g hi hC
  rw [fcSecant,fcStep,map_smul,real_inner_smul_right] at hc
  exact (mul_eq_zero.mp hc).resolve_left hα

variable {n N : ℕ}

/-- True normalized canonical FC directions have their actual old-operator angle bound.
Use: the estimate includes a possible zero current line displacement and depends on no reference-step minimum.
Article: main_krylov, apB:lem:UAsteps.
Proof: transfer the proved real direction-image conjugacy through the actual
root pairing, then apply the normalized operator-deviation inequality. -/
theorem fullFC_canonical_direction_angle (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {i k : ℕ} (hi : i<k)
    (hnext : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))).det)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    {η : ℝ} (hA : ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    |inner ℝ (NormedSpace.normalize (R (fcDirection fullMemory A g k)))
      (NormedSpace.normalize (R (fcDirection fullMemory A g i)))|≤η := by
  apply normalized_conjugacy_bound _ _ (canonicalOperator base (A i)) hA
  rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
  exact fullFC_direction_image_conjugate A g hi hnext hC

/-- Every actual nonzero-curvature FC search has a nonzero genuine canonical direction.
Use: all normalized direction columns have true unit norm even if the actual line scalar is zero.
Article: main_krylov, apB:lem:UAsteps.
Proof: the real inverse root cancels the true positive root; a zero canonical
direction would give zero physical direction and hence zero actual curvature. -/
theorem fullFC_canonical_direction_ne (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hc : inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g i)≠0 := by
  intro hz
  have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
  rw [canonical_primal_dual_cancel base hb,map_zero] at he
  apply hc
  rw [he,inner_zero_left]

/-- The genuine unit-direction Gram matrix of an actual defined FC prefix has the dimension-times-budget spectral deviation bound.
Use: derive conditioning from real observed solves and true canonical operator budgets without lower bounds on actual or reference line lengths.
Article: main_krylov, apB:lem:UAsteps.
Proof: actual curvature gives unit canonical columns. For each distinct
pair, the real newer solve and the intervening defined solve give the true
normalized direction angle bound; apply the proved spectral Gram estimate. -/
theorem fullFC_direction_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {η : ℝ}
    (hsolve : ∀ k<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    (hcurv : ∀ k<N, inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0)
    (hA : ∀ k<N, ‖canonicalOperator base (A k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hη : 0≤η) :
    let t : Fin N → EuclideanSpace ℝ (Fin n) := fun i => NormedSpace.normalize
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g i.val))
    ‖crossGram t t-1‖≤(N : ℝ)*η := by
  -- Each true direction column is normalized after its actual nonzero-curvature domain is used.
  apply unitGram_deviation _ (fun i => NormedSpace.norm_normalize
    (fullFC_canonical_direction_ne base hb A g i.val (hcurv i.val i.isLt))) hη
  intro i j hij
  by_cases hi : i.val<j.val
  · rw [real_inner_comm]
    exact fullFC_canonical_direction_angle base hb A g hi (hsolve (i.val+1) (by omega))
      (hsolve j.val j.isLt) (hA i.val i.isLt)
  · have hj : j.val < i.val := by
      have hn : i.val≠j.val := fun he => hij (Fin.ext he)
      omega
    exact fullFC_canonical_direction_angle base hb A g hj (hsolve (j.val+1) (by omega))
      (hsolve i.val i.isLt) (hA j.val j.isLt)

/-- A true defined full FC cycle with a small dimension-times-budget has a genuine nonsingular square matrix of normalized canonical directions.
Use: exact reconstruction remains valid for a zero final line step; the source defined-cycle hypothesis is preserved.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: the proved actual direction-angle estimate bounds the genuine
square column Gram error by one half. The real near-identity Gram inverse
domain forces the actual square direction determinant nonzero. -/
theorem fullFC_direction_matrix_unit (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {η : ℝ}
    (hsolve : ∀ k<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    (hcurv : ∀ k<n, inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0)
    (hA : ∀ k<n, ‖canonicalOperator base (A k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hη : 0≤η) (hsmall : (n : ℝ)*η≤1/2) :
    let T : Matrix (Fin n) (Fin n) ℝ := fun i j => NormedSpace.normalize
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g j.val)) i
    IsUnit T.det := by
  let t : Fin n → EuclideanSpace ℝ (Fin n) := fun j => NormedSpace.normalize
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g j.val))
  let T : Matrix (Fin n) (Fin n) ℝ := fun i j => t j i
  change IsUnit T.det
  apply column_unit_of_near_gram T
  have he : Tᵀ*T=crossGram t t := transpose_mul_columnGram T
  rw [he]
  exact (fullFC_direction_gram base hb A g n hsolve hcurv hA hη).trans hsmall
end
end krylov.Stability
