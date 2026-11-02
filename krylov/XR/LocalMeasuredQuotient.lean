import krylov.XR.LocalCurvatureQuotient

/-!
Article: main_krylov, lem:mm and apG:local(c), the measured XR quotient.
Use: identify the literal actual function-value test with its block-energy
curvature ratio, then derive the uniform O(epsilon) estimate from genuine
derivatives and physical secant/Hessian errors.
Source: the proved weighted Taylor identity and actual model slope identity.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual solved block-model energy. -/
def modelEnergy (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (c : ℝ) : ℝ :=
  modelCoefficients s T g ⬝ᵥ (T *ᵥ modelCoefficients s T g) +
    (modelTrialLength s y T g c) ^ 2 * c

/-- Literal model slope equals the negative actual block-model energy. -/
theorem modelEnergy_eq_neg_slope (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : IsUnit T.det) (g : E) (c : ℝ) (hc : 0 < c) :
    modelEnergy s y T g c = -inner ℝ g (modelTrialStep s y T g c) := by
  rw [modelTrialStep_slope s y T hT g c hc, neg_neg]
  rfl

/-- The actually tested value quotient is precisely the weighted true
Hessian curvature divided by the actual block-model energy. -/
theorem trialQuotient_model_energy (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det)
    (g x : E) (hcache : G x = g) (c : ℝ) (hc : 0 < c)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (innerSL ℝ (G (x + t • modelTrialStep s y T g c)))
        (x + t • modelTrialStep s y T g c))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt G (H (x + t • modelTrialStep s y T g c))
        (x + t • modelTrialStep s y T g c))
    (hH : ContinuousOn (fun t : ℝ => H (x + t • modelTrialStep s y T g c)) (Icc 0 1)) :
    trialQuotient f x g (modelTrialStep s y T g c) 1 =
      weightedCurvature H x (modelTrialStep s y T g c) / modelEnergy s y T g c := by
  rw [weightedCurvature_eq_values f G H x _ hF hG hH, hcache,
    modelEnergy_eq_neg_slope s y T hT g c hc]
  simp only [trialQuotient, one_smul, one_mul, neg_mul]

/-- The genuine measured unit-trial quotient satisfies the original
leading maximum-curvature estimate, with a source-only error coefficient.
Positive model energy is a domain condition discharged by the preceding
primitive local-step theorem at every nonstationary actual source point. -/
theorem measured_model_quotient_bound (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (hT : IsUnit (latest (crossGram s y)).det) (hinv : IsUnit (crossGram y s).det)
    (g x : E) (hcache : G x = g) (c coercivity ell epsilon : ℝ)
    (hc : 0 < c) (hcoercivity : 0 < coercivity) (hell : 0 < ell) (he : 0 ≤ epsilon)
    (hcoerc : ∀ w : Fin p → ℝ, coercivity * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (latest (crossGram s y) *ᵥ w))
    (hcurv : ell * ‖modelDirection s y (latest (crossGram s y)) g‖ ^ 2 ≤ c)
    (henergy : 0 < modelEnergy s y (latest (crossGram s y)) g c)
    (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (innerSL ℝ (G (x + t • modelTrialStep s y (latest (crossGram s y)) g c)))
        (x + t • modelTrialStep s y (latest (crossGram s y)) g c))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt G (H (x + t • modelTrialStep s y (latest (crossGram s y)) g c))
        (x + t • modelTrialStep s y (latest (crossGram s y)) g c))
    (hH : ContinuousOn (fun t : ℝ => H
      (x + t • modelTrialStep s y (latest (crossGram s y)) g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H (x + t • modelTrialStep s y (latest (crossGram s y)) g c) - Hstar‖ ≤ epsilon) :
    let T := latest (crossGram s y)
    let d := modelDirection s y T g
    trialQuotient f x g (modelTrialStep s y T g c) 1 ≤
      max 1 (inner ℝ (Hstar d) d / c) +
        (curvatureErrorConstant p / min coercivity ell) * epsilon := by
  dsimp only
  let T := latest (crossGram s y)
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  let u := modelTrialStep s y T g c
  let m := min coercivity ell
  let energy := modelEnergy s y T g c
  let ideal := w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d
  have hm : 0 < m := lt_min hcoercivity hell
  have hold := hcoerc w
  have hden : m * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) ≤ energy := by
    have h₁ := mul_le_mul_of_nonneg_right (min_le_left coercivity ell) (sq_nonneg ‖WithLp.toLp 2 w‖)
    have h₂ := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    have h₃ := mul_le_mul_of_nonneg_right (min_le_right coercivity ell)
      (mul_nonneg (sq_nonneg t) (sq_nonneg ‖d‖))
    dsimp only [energy, modelEnergy, m, w, d, t] at *
    nlinarith
  have herr := modelTrial_weighted_curvature_error H Hstar hHstar s y hs hinv g x c epsilon he hy hH herror
  dsimp only at herr
  have hC : 0 ≤ curvatureErrorConstant p := by unfold curvatureErrorConstant; positivity
  have hscale : 0 ≤ (curvatureErrorConstant p / m) * epsilon := mul_nonneg (div_nonneg hC hm.le) he
  have hallow : curvatureErrorConstant p * epsilon *
      (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) ≤
        ((curvatureErrorConstant p / m) * epsilon) * energy := by
    calc
      _ = ((curvatureErrorConstant p / m) * epsilon) *
          (m * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hden hscale
  have hnum : weightedCurvature H x u ≤ ideal +
      ((curvatureErrorConstant p / m) * epsilon) * energy := by
    have h := (abs_le.mp herr).2
    change weightedCurvature H x u - ideal ≤ _ at h
    nlinarith
  have hquot := div_le_div_of_nonneg_right hnum henergy.le
  have hdist : (ideal + ((curvatureErrorConstant p / m) * epsilon) * energy) / energy =
      ideal / energy + (curvatureErrorConstant p / m) * epsilon := by
    field_simp [show energy ≠ 0 from ne_of_gt henergy, ne_of_gt hm]
  rw [hdist] at hquot
  have hratio := block_curvature_ratio (w ⬝ᵥ (T *ᵥ w)) t (inner ℝ (Hstar d) d) c
    ((mul_nonneg hcoercivity.le (sq_nonneg _)).trans hold) hc henergy
  rw [trialQuotient_model_energy f G H s y T hT g x hcache c hc hF hG hH]
  change weightedCurvature H x u / energy ≤ _
  change ideal / energy ≤ _ at hratio
  nlinarith

end
end krylov.XR
