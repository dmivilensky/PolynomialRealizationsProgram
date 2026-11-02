import krylov.Stability.CanonicalDirectionGeometry
import krylov.Variation.FCResponse
import krylov.Stability.UniformDirectionBasis

/-!
Article: main_krylov, thm:A and apB:lem:UAsteps, actual canonical FC perturbation operators.
Use: discharge the real canonical increment budgets and actual direction
matrix inverse domain for the true physical affine perturbation model.
Source: genuine positive-root congruence cancellation, real finite prefix
norm bounds and the proved actual normalized FC direction Gram estimate.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true physical Euclidean matrix operator has exactly the genuine canonical relative-congruence matrix.
Use: canonical operator budgets refer to the actual root and physical query operator.
Article: main_krylov, thm:A.
Proof: the actual matrix/operator algebra identification preserves products;
its real multiplication is the same true operator composition. -/
theorem canonicalOperator_matrix (base B : Matrix (Fin n) (Fin n) ℝ) :
    canonicalOperator base (Matrix.toEuclideanCLM (𝕜 := ℝ) B)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (relativeOperator base B) := by
  unfold canonicalOperator relativeOperator
  rw [map_mul,map_mul]
  ext v
  rfl

/-- The genuine canonical affine FC segment operator is identity plus the actual finite sum of its true canonical increments.
Use: the source perturbation variables have exactly their prescribed real operator meaning.
Article: main_krylov, thm:A and s2:eq:firstorder.
Proof: the true positive metric root cancels its genuine inverse on both
sides of the actual physical increment congruence. The real base becomes
identity, leaving precisely the actual canonical prefix sum. -/
theorem canonicalFCPath_canonicalOperator (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    canonicalOperator base (canonicalFCPath base E 1 k)=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈range k, E l) := by
  -- The actual metric and its real inverse are cancelled before any canonical budget is asserted.
  let R := metricRoot base
  let S := ∑ l∈range k, E l
  have hrel : relativeOperator base (base+R*S*R)=1+S := by
    unfold relativeOperator
    rw [Matrix.mul_add,Matrix.add_mul]
    change relativeOperator base base+R⁻¹*(R*S*R)*R⁻¹=1+S
    rw [relativeOperator_base base hb]
    congr 1
    calc
      R⁻¹*(R*S*R)*R⁻¹=(R⁻¹*R)*S*(R*R⁻¹) := by noncomm_ring
      _ = S := by
        rw [Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),
          Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),Matrix.one_mul,Matrix.mul_one]
  rw [canonicalFCPath,one_smul,cgOperator,cumulativeDrift,← map_add,canonicalOperator_matrix,hrel,map_add,map_one]
  rfl

/-- The actual canonical segment deviation is bounded by the genuine total finite spectral increment budget.
Use: discharge every true operator-budget premise in the global actual FC stability induction.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: use the proved exact real canonical prefix operator, the true
spectral matrix norm and finite prefix inclusion in the actual total budget. -/
theorem canonicalFCPath_budget_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N k : ℕ) (hk : k≤N) :
    ‖canonicalOperator base (canonicalFCPath base E 1 k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤
      ∑ l∈range N, ‖E l‖ := by
  rw [canonicalFCPath_canonicalOperator base hb,_root_.add_sub_cancel_left,Matrix.l2_opNorm_toEuclideanCLM]
  exact (norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg (range_mono hk)
    (fun l _ _ => norm_nonneg (E l)))

/-- The actual square matrix of true normalized canonical directions in the genuine executed full-memory FC cycle.
Use: remains a real basis when the last exact line scalar is zero, unlike a full step matrix.
Article: main_krylov, thm:A and apB:lem:UAsteps. -/
def canonicalFCDirectionMatrix (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => NormedSpace.normalize
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g j.val)) i

/-- The true actual normalized canonical direction matrix of the real FC perturbation path has dimension-times-total-budget Gram error.
Use: genuine basis conditioning follows from actual observed solves and searches, allowing a zero last step.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: real prefix canonical budgets and the proved actual direction
conjugacy theorem bound its genuine unit-column Gram matrix. -/
theorem canonicalFCPath_directionMatrix_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hsolve : ∀ i<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))).det)
    (hcurv : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath base E 1) g i)
      (canonicalFCPath base E 1 i (fcDirection fullMemory (canonicalFCPath base E 1) g i))≠0) :
    let T := canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g
    ‖Tᵀ*T-1‖≤(n : ℝ)*(∑ l∈range n, ‖E l‖) := by
  let T := canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g
  change ‖Tᵀ*T-1‖≤_
  rw [transpose_mul_columnGram T]
  exact fullFC_direction_gram base hb (canonicalFCPath base E 1) g n hsolve hcurv
    (fun i hi => canonicalFCPath_budget_bound base hb E n i hi.le) (sum_nonneg fun _ _ => norm_nonneg _)

/-- A true small-budget defined physical FC path has a genuinely nonsingular actual canonical direction matrix.
Use: the exact residual reconstruction uses a proved real inverse domain even with a zero final line step.
Article: main_krylov, thm:A.
Proof: the actual Gram deviation is at most one half, so the genuine near-identity Gram theorem gives a true nonsingular square direction basis. -/
theorem canonicalFCPath_directionMatrix_unit (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hsolve : ∀ i<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))).det)
    (hcurv : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath base E 1) g i)
      (canonicalFCPath base E 1 i (fcDirection fullMemory (canonicalFCPath base E 1) g i))≠0)
    (hsmall : (n : ℝ)*(∑ l∈range n, ‖E l‖)≤1/2) :
    IsUnit (canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g).det :=
  column_unit_of_near_gram _ ((canonicalFCPath_directionMatrix_gram base hb E g hsolve hcurv).trans hsmall)

end
end krylov.Stability
