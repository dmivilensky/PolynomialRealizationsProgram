import krylov.XR.LocalDirection
import krylov.XR.LocalEnergyAlgebra

/-!
Article: main_krylov, apG:local(b), actual model-step geometry.
Use: bound the real trial movement and derive the positive uniform descent
constant from the actual normal/conjugacy solves and primitive conditioning.
Source: the proved slope-defect identity and scalar block-energy comparison.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual new-direction trial movement is bounded by the actual
extrapolated gradient divided by the lower trial-curvature constant. -/
theorem modelTrial_movement_bound (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hinv : IsUnit (crossGram y s).det)
    (g : E) (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell)
    (hcurv : ell * ‖modelDirection s y T g‖ ^ 2 ≤ c) :
    ‖modelTrialLength s y T g c • modelDirection s y T g‖ ≤
      ‖modelVirtualGradient s y T g‖ / ell := by
  have hb : |inner ℝ g (modelDirection s y T g)| ≤
      ‖modelVirtualGradient s y T g‖ * ‖modelDirection s y T g‖ := by
    rw [modelDirection_slope s y T hinv g]
    exact abs_real_inner_le_norm _ _
  rw [norm_smul, modelTrialLength, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hc]
  calc
    _ ≤ (‖modelVirtualGradient s y T g‖ * ‖modelDirection s y T g‖ / c) *
        ‖modelDirection s y T g‖ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hc.le) (norm_nonneg _)
    _ ≤ _ := by
      apply (le_div_iff₀ hell).2
      rw [show (‖modelVirtualGradient s y T g‖ * ‖modelDirection s y T g‖ / c) *
          ‖modelDirection s y T g‖ * ell =
          (‖modelVirtualGradient s y T g‖ * ell * ‖modelDirection s y T g‖ ^ 2) / c by ring]
      apply (div_le_iff₀ hc).2
      have hm := mul_le_mul_of_nonneg_left hcurv (norm_nonneg (modelVirtualGradient s y T g))
      nlinarith

/-- The actual virtual-gradient decomposition controls the full gradient
by the computed coefficients and the observed image-column bound. -/
theorem gradient_norm_virtual_decomposition (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (K : ℝ) (hK : 0 ≤ K)
    (hy : ∀ i, ‖y i‖ ≤ K) :
    ‖g‖ ≤ ‖modelVirtualGradient s y T g‖ +
      frameBound p K * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ := by
  have he : g = modelVirtualGradient s y T g - combine y (modelCoefficients s T g) := by
    rw [modelVirtualGradient, add_sub_cancel_right]
  calc
    _ = ‖modelVirtualGradient s y T g - combine y (modelCoefficients s T g)‖ := congrArg norm he
    _ ≤ ‖modelVirtualGradient s y T g‖ + ‖combine y (modelCoefficients s T g)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [synthesis_norm_of_columns y K hK hy (modelCoefficients s T g)]

/-- Every genuinely conditioned computed nonzero-direction model step has
a uniform positive descent constant. No direction angle, desired output,
or safeguard acceptance is assumed. -/
theorem modelTrialStep_descent_bound (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det)
    (hinv : IsUnit (crossGram y s).det) (g : E)
    (K C coercivity upper c : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcoercivity : 0 < coercivity) (hupper : 0 < upper) (hc : 0 < c)
    (hs : ∀ i, ‖s i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ K)
    (hA : ‖(crossGram y s)⁻¹‖ ≤ C)
    (hcoerc : ∀ w : Fin p → ℝ, coercivity * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (T *ᵥ w))
    (hdefect : C * frameBound p K * ‖crossGram s y - T‖ ≤ 1)
    (hcurv : c ≤ upper * ‖modelDirection s y T g‖ ^ 2) :
    let D := 1 + frameBound p 1 * C * frameBound p K
    let constant := blockEnergyConstant coercivity (frameBound p K) (upper * D ^ 2)
    0 < constant ∧ inner ℝ g (modelTrialStep s y T g c) ≤ -constant⁻¹ * ‖g‖ ^ 2 := by
  let a := ‖WithLp.toLp 2 (modelCoefficients s T g)‖
  let q := ‖modelVirtualGradient s y T g‖
  let b := inner ℝ g (modelDirection s y T g)
  let z := (modelTrialLength s y T g c) ^ 2 * c
  let D := 1 + frameBound p 1 * C * frameBound p K
  let energy := modelCoefficients s T g ⬝ᵥ (T *ᵥ modelCoefficients s T g) + z
  have ha : 0 ≤ a := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hz : 0 ≤ z := mul_nonneg (sq_nonneg _) hc.le
  have hD : 0 ≤ D := by dsimp only [D, frameBound]; positivity
  have hb := modelDirection_slope_defect_bound s y T hT g K C
    ‖crossGram s y - T‖ hK hC hy hA le_rfl
  rw [← modelDirection_slope s y T hinv g] at hb
  have hsmall : |b + q ^ 2| ≤ a * q := hb.trans (by
    change (C * frameBound p K * ‖crossGram s y - T‖) * a * q ≤ _
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdefect ha) hq])
  have hqdefect : q ^ 2 ≤ |b| + a * q := by
    have ht := (abs_le.mp hsmall).2
    nlinarith [neg_le_abs b]
  have hd := modelDirection_norm_bound s y T g K C hK hC hs hy hA
  have hd2 : ‖modelDirection s y T g‖ ^ 2 ≤ D ^ 2 * q ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hq)).2 hd
    simpa only [mul_pow] using hsq
  have hcupper : c ≤ (upper * D ^ 2) * q ^ 2 :=
    hcurv.trans (by nlinarith [mul_le_mul_of_nonneg_left hd2 hupper.le])
  have hcz : c * z = b ^ 2 := by
    dsimp only [z, b, modelTrialLength]
    field_simp
  have htrial : |b| ^ 2 ≤ (upper * D ^ 2) * q ^ 2 * z := by
    rw [sq_abs, ← hcz]
    exact mul_le_mul_of_nonneg_right hcupper hz
  have hg := gradient_norm_virtual_decomposition s y T g K hK hy
  have hfb : 0 ≤ frameBound p K := by unfold frameBound; positivity
  have hg2 : ‖g‖ ^ 2 ≤ 2 * q ^ 2 + 2 * (frameBound p K) ^ 2 * a ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg g) (add_nonneg hq (mul_nonneg hfb ha))).2 hg
    nlinarith [sq_nonneg (q - frameBound p K * a)]
  have hbound := block_energy_controls_gradient a q |b| z (upper * D ^ 2)
    (frameBound p K) energy ‖g‖ coercivity ha hq (abs_nonneg _) hz
    (mul_nonneg hupper.le (sq_nonneg _)) hcoercivity hqdefect htrial
    (by dsimp only [a, energy]; linarith [hcoerc (modelCoefficients s T g)]) hg2
  dsimp only
  refine ⟨hbound.1, ?_⟩
  rw [modelTrialStep_slope s y T hT g c hc]
  change -energy ≤ _
  nlinarith [hbound.2]

/-- The actual model-step norm has a uniform gradient bound, including
arbitrarily short nonzero trial directions. -/
theorem modelTrialStep_norm_bound (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hinv : IsUnit (crossGram y s).det)
    (g : E) (K C c ell : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : 0 < c) (hell : 0 < ell)
    (hs : ∀ i, ‖s i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ K) (hT : ‖T⁻¹‖ ≤ C)
    (hcurv : ell * ‖modelDirection s y T g‖ ^ 2 ≤ c) :
    ‖modelTrialStep s y T g c‖ ≤
      (frameBound p 1 * C * frameBound p 1 +
        (1 + frameBound p K * C * frameBound p 1) / ell) * ‖g‖ := by
  have hw := modelCoefficients_norm_bound s T 1 C (by norm_num) hC hs hT g
  have hsynth := synthesis_norm_of_columns s 1 (by norm_num) hs (modelCoefficients s T g)
  have hybound := synthesis_norm_of_columns y K hK hy (modelCoefficients s T g)
  have hq : ‖modelVirtualGradient s y T g‖ ≤
      (1 + frameBound p K * C * frameBound p 1) * ‖g‖ := by
    have ht := norm_add_le g (combine y (modelCoefficients s T g))
    change ‖modelVirtualGradient s y T g‖ ≤ _ at ht
    have hm := hybound.trans (mul_le_mul_of_nonneg_left hw (by unfold frameBound; positivity))
    nlinarith
  have hm := modelTrial_movement_bound s y T hinv g c ell hc hell hcurv
  have hqdiv := div_le_div_of_nonneg_right hq hell.le
  have hsbound := hsynth.trans
    (mul_le_mul_of_nonneg_left hw (by unfold frameBound; positivity))
  have ht := norm_add_le (combine s (modelCoefficients s T g))
    (modelTrialLength s y T g c • modelDirection s y T g)
  change ‖modelTrialStep s y T g c‖ ≤ _ at ht
  calc
    _ ≤ (frameBound p 1 * (C * frameBound p 1 * ‖g‖)) +
        ((1 + frameBound p K * C * frameBound p 1) * ‖g‖) / ell :=
      ht.trans (add_le_add hsbound (hm.trans hqdiv))
    _ = _ := by ring

/-- A zero computed direction is harmless: the actual old-window model
alone still gives a uniform descent constant. -/
theorem modelVirtualCorrection_zero_direction_descent (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (g : E)
    (K C coercivity : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : 0 < coercivity)
    (hy : ∀ i, ‖y i‖ ≤ K) (hA : ‖(crossGram y s)⁻¹‖ ≤ C)
    (hcoerc : ∀ w : Fin p → ℝ, coercivity * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (T *ᵥ w))
    (hdefect : C * frameBound p K * ‖crossGram s y - T‖ ≤ 1)
    (hd : modelDirection s y T g = 0) :
    inner ℝ g (modelVirtualCorrection s T g) ≤
      -(coercivity / (1 + frameBound p K) ^ 2) * ‖g‖ ^ 2 := by
  let a := ‖WithLp.toLp 2 (modelCoefficients s T g)‖
  let q := ‖modelVirtualGradient s y T g‖
  have ha : 0 ≤ a := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hb := modelDirection_slope_defect_bound s y T hT g K C
    ‖crossGram s y - T‖ hK hC hy hA le_rfl
  rw [hd, inner_zero_right, zero_add] at hb
  have hqa : q ≤ a := by
    have hsmall : q ^ 2 ≤ a * q := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdefect ha) hq
      exact (le_abs_self (q ^ 2)).trans (hb.trans (by simpa only [one_mul] using h))
    by_cases hz : q = 0
    · simpa only [hz] using ha
    · have hpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      exact (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [hsmall])
  have hfb : 0 ≤ frameBound p K := by unfold frameBound; positivity
  have hg := gradient_norm_virtual_decomposition s y T g K hK hy
  have hgsmall : ‖g‖ ≤ (1 + frameBound p K) * a := by nlinarith
  have hsq := (sq_le_sq₀ (norm_nonneg g)
    (mul_nonneg (by positivity : 0 ≤ 1 + frameBound p K) ha)).2 hgsmall
  have hden : 0 < (1 + frameBound p K) ^ 2 := by positivity
  have henergy : coercivity / (1 + frameBound p K) ^ 2 * ‖g‖ ^ 2 ≤
      modelCoefficients s T g ⬝ᵥ (T *ᵥ modelCoefficients s T g) := by
    calc
      _ ≤ coercivity / (1 + frameBound p K) ^ 2 * ((1 + frameBound p K) * a) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hc.le hden.le)
      _ = coercivity * a ^ 2 := by field_simp
      _ ≤ _ := hcoerc _
  rw [modelVirtualCorrection_slope s T hT g]
  nlinarith

end
end krylov.XR
