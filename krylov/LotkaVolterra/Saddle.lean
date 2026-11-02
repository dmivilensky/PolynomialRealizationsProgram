import krylov.LotkaVolterra.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Constructions

/-!
Article: `main_krylov`, `apC:prop:LV` (the saddle and its stable direction).

The Jacobian is the actual Fréchet derivative of the concrete polynomial
field. The two real eigenvalues have opposite signs, and the stable
eigenvector has positive coordinates. These are the local algebraic inputs
to a stable-manifold argument; no existence of that manifold is assumed here.

Source: differentiation of `(LV_γ)` and the quadratic formula.
-/
namespace krylov.LotkaVolterra
noncomputable section

/-- Jacobian of the polynomial field as a continuous linear map. -/
def jacobian (γ : ℝ) (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (((4 * z.1 - 2 - 2 * γ * z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-2 * γ * z.1) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (z.1 + 1 - 2 * z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem jacobian_apply (γ : ℝ) (z v : ℝ × ℝ) :
    jacobian γ z v =
      ((4 * z.1 - 2 - 2 * γ * z.2) * v.1 - 2 * γ * z.1 * v.2,
       z.2 * v.1 + (z.1 + 1 - 2 * z.2) * v.2) := by
  simp [jacobian, sub_eq_add_neg]

/-- The displayed Jacobian is a genuine derivative, rather than a formal
matrix attached by definition to the equilibrium. -/
theorem hasFDerivAt_vectorField (γ : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (vectorField γ) (jacobian γ z) z := by
  have hs := hasFDerivAt_fst (𝕜 := ℝ) (p := z)
  have hU := hasFDerivAt_snd (𝕜 := ℝ) (p := z)
  have h₁ := ((hs.const_mul 2).mul ((hs.sub_const 1).sub (hU.const_mul γ)))
  have h₂ := hU.mul ((hs.add_const 1).sub hU)
  convert! h₁.prodMk h₂ using 1
  ext <;> simp [jacobian] <;> ring

/-- Polynomial regularity, available at every finite or infinite order. -/
theorem contDiff_vectorField (γ : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (vectorField γ) := by
  unfold vectorField sRate uRate
  fun_prop

/-- Real analyticity of the actual polynomial field. Analyticity of a
separating orbit is a separate assertion, not inferred from `C∞` regularity. -/
theorem analyticAt_vectorField (γ : ℝ) (z : ℝ × ℝ) :
    AnalyticAt ℝ (vectorField γ) z := by
  have hs : AnalyticAt ℝ (fun z : ℝ × ℝ ↦ z.1) z := analyticAt_fst
  have hU : AnalyticAt ℝ (fun z : ℝ × ℝ ↦ z.2) z := analyticAt_snd
  exact ((analyticAt_const.mul hs).mul
    ((hs.sub analyticAt_const).sub (analyticAt_const.mul hU))).prod
      (hU.mul ((hs.add analyticAt_const).sub hU))

/-- Actual Jacobian at the interior equilibrium, in the form used in the
article's characteristic polynomial. -/
theorem jacobian_saddle_apply {γ : ℝ} (hγ : γ ≠ 1) (v : ℝ × ℝ) :
    jacobian γ (saddlePoint γ) v =
      (2 * saddleS γ * v.1 - 2 * γ * saddleS γ * v.2,
       saddleU γ * v.1 - saddleU γ * v.2) := by
  rw [jacobian_apply]
  have hs := saddleS_eq_one_add_mul_saddleU hγ
  have hU := saddleU_eq_saddleS_add_one hγ
  apply Prod.ext
  all_goals dsimp only [saddlePoint, Prod.fst, Prod.snd]
  · have he : 4 * saddleS γ - 2 - 2 * γ * saddleU γ = 2 * saddleS γ := by
      linarith
    rw [he]
  · have he : saddleS γ + 1 - 2 * saddleU γ = -saddleU γ := by linarith
    rw [he]
    ring

/-- Trace of the actual equilibrium Jacobian. -/
def saddleTrace (γ : ℝ) : ℝ := 2 * saddleS γ - saddleU γ

/-- Determinant of the actual equilibrium Jacobian. -/
def saddleDeterminant (γ : ℝ) : ℝ := -2 * (1 - γ) * saddleS γ * saddleU γ

/-- Its characteristic polynomial evaluated at a real scalar. -/
def saddleCharacteristic (γ η : ℝ) : ℝ :=
  η ^ 2 - saddleTrace γ * η + saddleDeterminant γ

/-- Discriminant of the saddle characteristic polynomial. -/
def saddleDiscriminant (γ : ℝ) : ℝ :=
  saddleTrace γ ^ 2 - 4 * saddleDeterminant γ

/-- Stable eigenvalue, selected by the negative sign in the quadratic formula. -/
def stableEigenvalue (γ : ℝ) : ℝ :=
  (saddleTrace γ - Real.sqrt (saddleDiscriminant γ)) / 2

/-- Unstable eigenvalue, selected by the positive sign. -/
def unstableEigenvalue (γ : ℝ) : ℝ :=
  (saddleTrace γ + Real.sqrt (saddleDiscriminant γ)) / 2

theorem saddleDeterminant_neg {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    saddleDeterminant γ < 0 := by
  unfold saddleDeterminant
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by linarith))
      (saddleS_pos hγ hγ₁)) (saddleU_pos hγ₁)

theorem saddleDiscriminant_gt_trace_sq {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    saddleTrace γ ^ 2 < saddleDiscriminant γ := by
  have := saddleDeterminant_neg hγ hγ₁
  unfold saddleDiscriminant
  linarith

theorem saddleDiscriminant_pos {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    0 < saddleDiscriminant γ := by
  exact lt_of_le_of_lt (sq_nonneg _) (saddleDiscriminant_gt_trace_sq hγ hγ₁)

theorem stableEigenvalue_neg {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    stableEigenvalue γ < 0 := by
  have hd := saddleDiscriminant_gt_trace_sq hγ hγ₁
  have hr := Real.sqrt_nonneg (saddleDiscriminant γ)
  have hsq := Real.sq_sqrt (saddleDiscriminant_pos hγ hγ₁).le
  unfold stableEigenvalue
  nlinarith

theorem unstableEigenvalue_pos {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    0 < unstableEigenvalue γ := by
  have hd := saddleDiscriminant_gt_trace_sq hγ hγ₁
  have hr := Real.sqrt_nonneg (saddleDiscriminant γ)
  have hsq := Real.sq_sqrt (saddleDiscriminant_pos hγ hγ₁).le
  unfold unstableEigenvalue
  nlinarith

/-- Both roots solve exactly the characteristic equation printed in
Proposition `apC:prop:LV`. -/
theorem saddle_eigenvalues_characteristic {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    saddleCharacteristic γ (stableEigenvalue γ) = 0 ∧
    saddleCharacteristic γ (unstableEigenvalue γ) = 0 := by
  have hsq := Real.sq_sqrt (saddleDiscriminant_pos hγ hγ₁).le
  unfold saddleCharacteristic stableEigenvalue unstableEigenvalue
  unfold saddleDiscriminant at hsq ⊢
  constructor <;> nlinarith only [hsq]

/-- An eigenvector expression that does not divide by a possibly small
component. At the stable root, both coordinates are strictly positive. -/
def saddleEigenvector (γ η : ℝ) : ℝ × ℝ :=
  (2 * γ * saddleS γ, 2 * saddleS γ - η)

theorem jacobian_saddle_eigenvector {γ η : ℝ} (hγ : γ ≠ 1)
    (hη : saddleCharacteristic γ η = 0) :
    jacobian γ (saddlePoint γ) (saddleEigenvector γ η) =
      η • saddleEigenvector γ η := by
  rw [jacobian_saddle_apply hγ]
  unfold saddleEigenvector
  simp only [Prod.smul_mk, smul_eq_mul]
  apply Prod.ext
  · ring
  · unfold saddleCharacteristic saddleTrace saddleDeterminant at hη
    dsimp
    nlinarith only [hη]

theorem stableEigenvector_positive {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    saddleEigenvector γ (stableEigenvalue γ) ∈ positiveQuadrant := by
  have hs := saddleS_pos hγ hγ₁
  have hη := stableEigenvalue_neg hγ hγ₁
  change 0 < 2 * γ * saddleS γ ∧ 0 < 2 * saddleS γ - stableEigenvalue γ
  constructor
  · positivity
  · linarith

/-- The concrete benchmark saddle is `(3,4)`. -/
theorem saddle_half : saddlePoint (1 / 2 : ℝ) = (3, 4) := by
  norm_num [saddlePoint, saddleS, saddleU]

/-- The benchmark eigenvalues are precisely `1 ± sqrt 13`. -/
theorem eigenvalues_half :
    stableEigenvalue (1 / 2 : ℝ) = 1 - Real.sqrt 13 ∧
    unstableEigenvalue (1 / 2 : ℝ) = 1 + Real.sqrt 13 := by
  have h : Real.sqrt (52 : ℝ) = 2 * Real.sqrt 13 := by
    rw [show (52 : ℝ) = 4 * 13 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  norm_num [stableEigenvalue, unstableEigenvalue, saddleDiscriminant,
    saddleTrace, saddleDeterminant, saddleS, saddleU, h]
  constructor <;> ring

end
end krylov.LotkaVolterra
