import krylov.XR.LocalTrialEnergy
import krylov.XR.BacktrackingDescent

/-!
Article: main_krylov, apG:local(c), genuine curvature quotient comparison.
Use: bound the original measured XR quotient by the true new-direction
curvature ratio plus a source-only O(epsilon) term.
Source: actual weighted Taylor curvature, observed conjugacy, and the
positive block-model energy identity.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A dimension-only coefficient in the actual curvature error. -/
def curvatureErrorConstant (p : ℕ) : ℝ :=
  2 * (p : ℝ) + 1 + 2 * (frameBound p 1) ^ 2 + 2

/-- A normalized window bounds the actual trial norm by its two model
coordinate components, independently of the trial scalar. -/
theorem modelTrialStep_norm_sq (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (g : E) (c : ℝ) (hs : ∀ i, ‖s i‖ ≤ 1) :
    ‖modelTrialStep s y T g c‖ ^ 2 ≤
      2 * (frameBound p 1) ^ 2 * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ ^ 2 +
        2 * (modelTrialLength s y T g c) ^ 2 * ‖modelDirection s y T g‖ ^ 2 := by
  have hS := synthesis_norm_of_columns s 1 (by norm_num) hs (modelCoefficients s T g)
  have ht := norm_add_le (combine s (modelCoefficients s T g))
    (modelTrialLength s y T g c • modelDirection s y T g)
  rw [norm_smul, Real.norm_eq_abs] at ht
  change ‖modelTrialStep s y T g c‖ ≤ _ at ht
  have hb : ‖modelTrialStep s y T g c‖ ≤
      frameBound p 1 * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ +
        |modelTrialLength s y T g c| * ‖modelDirection s y T g‖ := by linarith
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by unfold frameBound; positivity)).2 hb
  nlinarith [sq_nonneg (frameBound p 1 * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ -
    |modelTrialLength s y T g c| * ‖modelDirection s y T g‖), sq_abs (modelTrialLength s y T g c)]

/-- The actual scalar weighted curvature has its uniform component-energy
error, derived from the true trial-segment Hessian allowance and genuine
observed secant errors. -/
theorem modelTrial_weighted_curvature_error (H : E → E →L[ℝ] E)
    (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (hinv : IsUnit (crossGram y s).det) (g x : E) (c epsilon : ℝ)
    (he : 0 ≤ epsilon) (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hH : ContinuousOn (fun t : ℝ => H (x + t • modelTrialStep s y
      (latest (crossGram s y)) g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H (x + t • modelTrialStep s y (latest (crossGram s y)) g c) - Hstar‖ ≤ epsilon) :
    let T := latest (crossGram s y)
    let w := modelCoefficients s T g
    let d := modelDirection s y T g
    let t := modelTrialLength s y T g c
    |weightedCurvature H x (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d)| ≤
      curvatureErrorConstant p * epsilon * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) := by
  dsimp only
  let T := latest (crossGram s y)
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  let u := modelTrialStep s y T g c
  have hW := weightedCurvature_error H Hstar x u epsilon he hH herror
  have hE := modelTrial_true_energy_error Hstar hHstar s y hs hinv g c epsilon he hy
  dsimp only at hE
  have hN := modelTrialStep_norm_sq s y T g c (fun i => (hs i).le)
  have ht := (abs_sub_le (weightedCurvature H x u) (inner ℝ (Hstar u) u)
    (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d)).trans (add_le_add hW hE)
  apply ht.trans
  have hm := mul_le_mul_of_nonneg_left hN he
  have ha : 0 ≤ ‖WithLp.toLp 2 w‖ ^ 2 := sq_nonneg _
  have hd : 0 ≤ t ^ 2 * ‖d‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hframe : 0 ≤ (frameBound p 1) ^ 2 := sq_nonneg _
  dsimp only [curvatureErrorConstant]
  nlinarith [mul_nonneg he ha, mul_nonneg he hd,
    mul_nonneg (mul_nonneg he hframe) ha, mul_nonneg (mul_nonneg he hframe) hd]

/-- Pure scalar block-model quotient comparison; the old model energy is
nonnegative, and the true new-direction ratio is the only leading factor. -/
theorem block_curvature_ratio (oldEnergy t curvature modelCurvature : ℝ)
    (hE : 0 ≤ oldEnergy) (hc : 0 < modelCurvature)
    (hden : 0 < oldEnergy + t ^ 2 * modelCurvature) :
    (oldEnergy + t ^ 2 * curvature) / (oldEnergy + t ^ 2 * modelCurvature) ≤
      max 1 (curvature / modelCurvature) := by
  let R := max 1 (curvature / modelCurvature)
  have h₁ : 1 ≤ R := le_max_left _ _
  have h₂ : curvature ≤ R * modelCurvature := (div_le_iff₀ hc).mp (le_max_right _ _)
  apply (div_le_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_right h₁ hE,
    mul_le_mul_of_nonneg_left h₂ (sq_nonneg t)]

end
end krylov.XR
