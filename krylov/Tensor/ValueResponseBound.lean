import krylov.Tensor.ReferenceTails
import krylov.Functions.ValueModelDiagonal
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, prop:Fcycle(i), the corrected compatible coefficient.
Use: prove the printed 4 n^(3/2) two-error bound on the genuine computed
reference, with the original diagonal tensor budget two.
Source: Banach's identity, actual CG tail geometry and the reused genuine
spectral/Frobenius matrix-norm comparison.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation krylov.Functions krylov.LinearAlgebra Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual value-corrected tensor model in the genuine active CG frame.
Article: main_krylov, prop:Fcycle(i), zeta_a replaced by v_a on its diagonal. -/
def valueReferenceModel (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin (referenceAtomCount A hA g)) (Fin (referenceAtomCount A hA g)) ℝ :=
  fun i j => if i = j then T.form (remainingTail A g i.val)
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g i.val)
    else T.form (referenceAnchorDrift A g (max i.val j.val))
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g j.val)

/-- This is exactly the previously proved half-split correction of the actual original tensor model.
Article: main_krylov, prop:Fcycle(i), model identification.
Proof: instantiate the true diagonal replacement on the actual reference steps and tails. -/
theorem valueReferenceModel_eq_half_split (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    valueReferenceModel A hA g T =
      tensorWindowModel T (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
        (fun i => referenceAnchorDrift A g i.val) -
      diagonal (fun i : Fin (referenceAtomCount A hA g) =>
        T.form ((1/2 : ℝ) • canonicalCGStep A g i.val)
          (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g i.val)) := by
  symm
  exact tensorWindowModel_half_split T _ _ _

/-- Every corrected-model entry has the genuine first-tail bound two.
Article: main_krylov, prop:Fcycle(i).
Proof: the diagonal uses true remaining tails; every off-diagonal maximum
index is positive and its true anchor drift is bounded by the first post-search error. -/
theorem valueReferenceModel_entry_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ x, ‖x‖ = 1 → |T.form x x x| ≤ 2)
    (i j : Fin (referenceAtomCount A hA g)) :
    |valueReferenceModel A hA g T i j| ≤ 2 * ‖cgCanonicalError A g 1‖ := by
  have hm := reference_error_antitone A hA g
  have hi := (canonicalCG_frame A hA g).norm_eq_one i
  have hj := (canonicalCG_frame A hA g).norm_eq_one j
  unfold valueReferenceModel
  split_ifs with hij
  · have hb := cubic_diagonal_bound T 2 hT (remainingTail A g i.val)
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g i.val)
    rw [hi, mul_one, mul_one, remainingTail_norm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hm (by omega : 1 ≤ i.val+1)) (by norm_num))
  · have hmax : 1 ≤ max i.val j.val := by
      have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    have hb := cubic_diagonal_bound T 2 hT (referenceAnchorDrift A g (max i.val j.val))
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g j.val)
    rw [hi, hj, mul_one, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      ((reference_anchor_drift_le A hA g _).trans (hm hmax)) (by norm_num))

/-- The corrected genuine spectral model has the printed dimension factor.
Article: main_krylov, prop:Fcycle(i), norm L_F ≤ 2 n norm(e_1).
Proof: use actual entry bounds and the already proved spectral/Frobenius comparison. -/
theorem valueReferenceModel_norm_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ x, ‖x‖ = 1 → |T.form x x x| ≤ 2) :
    ‖valueReferenceModel A hA g T‖ ≤ 2 * referenceAtomCount A hA g * ‖cgCanonicalError A g 1‖ := by
  apply (spectral_le_hsNorm _).trans
  have hb := hsNorm_le_dimension (valueReferenceModel A hA g T) (by positivity)
    (valueReferenceModel_entry_bound A hA g T hT)
  convert hb using 1
  ring

/-- The actual fresh tensor defect in the true active CG coordinates.
Article: main_krylov, eq:tensor-product and prop:Fcycle(i). -/
def referenceTensorFresh (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin (referenceAtomCount A hA g)) :=
  WithLp.toLp 2 (fun i => T.form
    (referenceAnchorDrift A g i.val - referenceAnchorDrift A g (referenceAtomCount A hA g-1))
    (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)))

/-- The fresh tensor vector obeys its original error-scale bound on the genuine reference.
Article: main_krylov, prop:Fcycle(i).
Proof: bound the actual vector coordinate squares using the true midpoint
difference geometry and Banach's mixed estimate, then take the positive square root. -/
theorem referenceTensorFresh_norm_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ x, ‖x‖ = 1 → |T.form x x x| ≤ 2) :
    ‖referenceTensorFresh A hA g T‖ ≤
      2 * Real.sqrt (referenceAtomCount A hA g) * ‖cgCanonicalError A g 0‖ := by
  have hc (i : Fin (referenceAtomCount A hA g)) :
      |referenceTensorFresh A hA g T i| ≤ 2 * ‖cgCanonicalError A g 0‖ := by
    have hb := cubic_diagonal_bound T 2 hT
      (referenceAnchorDrift A g i.val - referenceAnchorDrift A g (referenceAtomCount A hA g-1))
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g (referenceAtomCount A hA g-1))
    rw [(canonicalCG_frame A hA g).norm_eq_one i,
      (canonicalCG_frame A hA g).norm_eq_one ⟨referenceAtomCount A hA g-1, by omega⟩,
      mul_one, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      ((reference_anchor_difference_le A hA g hN i).trans
        (reference_error_antitone A hA g (Nat.zero_le _))) (by norm_num))
  have hs : ‖referenceTensorFresh A hA g T‖ ^ 2 ≤
      (referenceAtomCount A hA g : ℝ) * (2 * ‖cgCanonicalError A g 0‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin (referenceAtomCount A hA g), (2 * ‖cgCanonicalError A g 0‖)^2 := by
        apply sum_le_sum
        intro i _
        have hi := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hc i)
        simpa only [sq_abs] using hi
      _ = _ := by simp
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (referenceAtomCount A hA g) : (0:ℝ) ≤ _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow, hsq]
  nlinarith only [hs]

/-- The actual corrected tensor coefficient in true CG coordinates.
Article: main_krylov, prop:Fcycle(i), Lambda_F. -/
def valueReferenceCoefficient (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin (referenceAtomCount A hA g)) :=
  Matrix.toEuclideanCLM (n := Fin (referenceAtomCount A hA g)) (𝕜 := ℝ)
    (valueReferenceModel A hA g T) (referenceTensorFresh A hA g T)

/-- The genuine value-corrected coefficient has the printed 4 n^(3/2) two-error bound.
Article: main_krylov, prop:Fcycle(i).
Proof: multiply the actual spectral corrected-model bound by the actual fresh-defect bound. -/
theorem valueReferenceCoefficient_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ x, ‖x‖ = 1 → |T.form x x x| ≤ 2) :
    ‖valueReferenceCoefficient A hA g T‖ ≤
      4 * referenceAtomCount A hA g * Real.sqrt (referenceAtomCount A hA g) *
        ‖cgCanonicalError A g 0‖ * ‖cgCanonicalError A g 1‖ := by
  have hb := (Matrix.toEuclideanCLM (n := Fin (referenceAtomCount A hA g)) (𝕜 := ℝ)
    (valueReferenceModel A hA g T)).le_opNorm (referenceTensorFresh A hA g T)
  rw [← Matrix.cstar_norm_def] at hb
  apply hb.trans
  have hm := valueReferenceModel_norm_bound A hA g T hT
  have hf := referenceTensorFresh_norm_bound A hA g hN T hT
  calc
    _ ≤ (2 * referenceAtomCount A hA g * ‖cgCanonicalError A g 1‖) *
        (2 * Real.sqrt (referenceAtomCount A hA g) * ‖cgCanonicalError A g 0‖) := by gcongr
    _ = _ := by ring

end
end krylov.Tensor
