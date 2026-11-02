import krylov.XR.LocalMeasuredQuotient

/-!
Article: main_krylov, apG:local(c), full/zero-direction trials.
Use: prove the genuine function-value quotient of the window-only model
step is at most 1+O(epsilon). Thus the full-window case needs no new-trial
adequacy assumption. Source: true weighted Taylor curvature and the
derived observed Gram perturbation estimate.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Actual measured curvature for the pure window correction. -/
theorem measured_window_quotient_bound (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (hT : IsUnit (latest (crossGram s y)).det) (g x : E) (hcache : G x = g)
    (coercivity epsilon : ℝ) (hcoercivity : 0 < coercivity) (he : 0 ≤ epsilon)
    (hcoerc : ∀ w : Fin p → ℝ, coercivity * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (latest (crossGram s y) *ᵥ w))
    (henergy : 0 < modelCoefficients s (latest (crossGram s y)) g ⬝ᵥ
      (latest (crossGram s y) *ᵥ modelCoefficients s (latest (crossGram s y)) g))
    (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (innerSL ℝ (G (x + t • modelVirtualCorrection s (latest (crossGram s y)) g)))
        (x + t • modelVirtualCorrection s (latest (crossGram s y)) g))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt G (H (x + t • modelVirtualCorrection s (latest (crossGram s y)) g))
        (x + t • modelVirtualCorrection s (latest (crossGram s y)) g))
    (hH : ContinuousOn (fun t : ℝ => H
      (x + t • modelVirtualCorrection s (latest (crossGram s y)) g)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H (x + t • modelVirtualCorrection s (latest (crossGram s y)) g) - Hstar‖ ≤ epsilon) :
    trialQuotient f x g (modelVirtualCorrection s (latest (crossGram s y)) g) 1 ≤
      1 + (((p : ℝ) + (frameBound p 1) ^ 2) / coercivity) * epsilon := by
  let T := latest (crossGram s y)
  let w := modelCoefficients s T g
  let u := modelVirtualCorrection s T g
  let energy := w ⬝ᵥ (T *ᵥ w)
  have hnorm := synthesis_norm_of_columns s 1 (by norm_num) (fun i => (hs i).le) w
  have hsq : ‖u‖ ^ 2 ≤ (frameBound p 1) ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 := by
    change ‖combine s w‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (combine s w), norm_nonneg (WithLp.toLp 2 w)]
  have hGram := window_true_energy_error Hstar hHstar s y hs epsilon he hy w
  have hTaylor := weightedCurvature_error H Hstar x u epsilon he hH herror
  have hn : weightedCurvature H x u ≤ energy +
      ((p : ℝ) + (frameBound p 1) ^ 2) * epsilon * ‖WithLp.toLp 2 w‖ ^ 2 := by
    have ha := (abs_le.mp hGram).2
    have hb := (abs_le.mp hTaylor).2
    change inner ℝ (Hstar (combine s w)) (combine s w) - energy ≤ _ at ha
    change weightedCurvature H x u - inner ℝ (Hstar u) u ≤ _ at hb
    change weightedCurvature H x u ≤ _
    have hmul := mul_le_mul_of_nonneg_left hsq he
    dsimp only [u, modelVirtualCorrection] at *
    nlinarith
  have hc := hcoerc w
  have hallow : ((p : ℝ) + (frameBound p 1) ^ 2) * epsilon * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ((((p : ℝ) + (frameBound p 1) ^ 2) / coercivity) * epsilon) * energy := by
    have hscale : 0 ≤ (((p : ℝ) + (frameBound p 1) ^ 2) / coercivity) * epsilon := by positivity
    calc
      _ = ((((p : ℝ) + (frameBound p 1) ^ 2) / coercivity) * epsilon) *
          (coercivity * ‖WithLp.toLp 2 w‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hscale
  have hq : trialQuotient f x g u 1 = weightedCurvature H x u / energy := by
    rw [weightedCurvature_eq_values f G H x u hF hG hH, hcache]
    have hslope := modelVirtualCorrection_slope s T hT g
    change trialQuotient f x g u 1 = _
    simp only [trialQuotient, one_smul, one_mul, neg_mul]
    change _ / (-inner ℝ g u) = _
    rw [hslope, neg_neg]
  rw [hq]
  apply (div_le_iff₀ henergy).mpr
  change weightedCurvature H x u ≤ _
  nlinarith

end
end krylov.XR
