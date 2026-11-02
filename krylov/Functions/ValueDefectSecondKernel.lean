import krylov.Functions.TrapezoidAffine
import krylov.Functions.MidpointQuadratic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, prop:Fcycle(i), the actual value-defect jet.
Use: derive the cubic defect from the genuine derivative of the physical
Hessian at the minimizer. The second-derivative Peano kernel avoids requiring
a varying third derivative merely to prove the C3 little-o transfer.
Source: integration by parts on the actual unit segment and the genuine
Frechet derivative remainder. No value-defect expansion is a premise.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- The second-derivative Peano kernel computes the actual trapezoid defect.
Article: main_krylov, prop:Fcycle(i), a twice differentiated form of thm:Fexact. -/
theorem trapezoid_second_integral (f f₁ f₂ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hc : ContinuousOn f₂ (Icc 0 1)) :
    trapezoidDefect f f₁ = ∫ t in (0 : ℝ)..1, (1 / 2 - t) * f₂ t := by
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => (1 / 2 - t) * f₁ t + f t) ((1 / 2 - t) * f₂ t) t := by
    convert! ((((hasDerivAt_const t (1 / 2 : ℝ)).sub (hasDerivAt_id t)).mul
      (h₂ t ht)).add (h₁ t ht)) using 1
    simp only [Pi.sub_apply, id_eq]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 - t) * f₂ t) volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn).mul hc).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht)) hi
  simp only [trapezoidDefect]
  norm_num at he
  linarith only [he]

/-- Affine second derivatives have the exact cubic defect, with a quantitative perturbation bound.
Article: main_krylov, prop:Fcycle(i), the second-kernel stability estimate. -/
theorem trapezoid_second_affine_remainder (f f₁ f₂ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hc : ContinuousOn f₂ (Icc 0 1)) (A B ρ : ℝ)
    (hrem : ∀ t ∈ Icc (0 : ℝ) 1, |f₂ t - (A + t * B)| ≤ ρ) :
    |trapezoidDefect f f₁ + B / 12| ≤ ρ / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 - t) * (f₂ t - (A + t * B))) volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn).mul
      (hc.sub (by fun_prop : Continuous _).continuousOn)).intervalIntegrable_of_Icc
        (by norm_num : (0 : ℝ) ≤ 1)
  have he : trapezoidDefect f f₁ + B / 12 =
      ∫ t in (0 : ℝ)..1, (1 / 2 - t) * (f₂ t - (A + t * B)) := by
    rw [trapezoid_second_integral f f₁ f₂ h₁ h₂ hc]
    have hpoly : (∫ t in (0 : ℝ)..1, (1 / 2 - t) * (A + t * B)) = -B / 12 := by
      have hp t : HasDerivAt (fun t : ℝ => A * t / 2 + (B / 2 - A) * t ^ 2 / 2 - B * t ^ 3 / 3)
          ((1 / 2 - t) * (A + t * B)) t := by
        convert! ((((hasDerivAt_id t).const_mul A).div_const 2).add
          ((((hasDerivAt_id t).pow 2).const_mul (B / 2 - A)).div_const 2)).sub
          ((((hasDerivAt_id t).pow 3).const_mul B).div_const 3) using 1
        simp only [id_eq]
        ring
      have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hp t)
        ((by fun_prop : Continuous _).intervalIntegrable 0 1)
      norm_num at hh
      linarith only [hh]
    rw [show (fun t : ℝ => (1 / 2 - t) * (f₂ t - (A + t * B))) =
      (fun t : ℝ => (1 / 2 - t) * f₂ t - (1 / 2 - t) * (A + t * B)) from
      funext (fun _ => mul_sub _ _ _)]
    rw [intervalIntegral.integral_sub
      (f := fun t : ℝ => (1 / 2 - t) * f₂ t)
      (g := fun t : ℝ => (1 / 2 - t) * (A + t * B))
      ((((continuous_const.sub continuous_id).continuousOn).mul hc).intervalIntegrable_of_Icc
        (by norm_num : (0 : ℝ) ≤ 1))
      ((by fun_prop : Continuous _).intervalIntegrable 0 1), hpoly]
    ring
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => (1 / 2 - t) * (f₂ t - (A + t * B)))
    (g := fun _ : ℝ => ρ / 2)
    (Filter.Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hw : |(1 / 2 : ℝ) - t| ≤ 1 / 2 :=
        abs_le.mpr ⟨by linarith only [ht'.2], by linarith only [ht'.1]⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hrem t ht') (abs_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right hw ((abs_nonneg _).trans (hrem t ht'))).trans_eq (by ring)))
    intervalIntegrable_const
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine physical Hessian approximation controls the true observed value defect.
Article: main_krylov, prop:Fcycle(i), the native function/gradient defect identity.
All scalar derivatives are derived from the original physical derivatives. -/
theorem segmentValueDefect_affine_hessian (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (a s : E)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f (innerSL ℝ (G (a + t • s))) (a + t • s))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G (H (a + t • s)) (a + t • s))
    (hc : ContinuousOn (fun t : ℝ => H (a + t • s)) (Icc 0 1))
    (ρ : ℝ) (hrem : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (a + t • s) - H 0 - D (a + t • s)‖ ≤ ρ) :
    |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s + inner ℝ (D s s) s / 12| ≤
      ρ * ‖s‖ ^ 2 / 2 := by
  let f₀ := fun t : ℝ => f (a + t • s)
  let f₁ := fun t : ℝ => inner ℝ (G (a + t • s)) s
  let f₂ := fun t : ℝ => inner ℝ (H (a + t • s) s) s
  have hd₁ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₀ (f₁ t) t :=
    segment_hasDerivAt f (fun x => innerSL ℝ (G x)) a s t (hF t ht)
  have hd₂ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₁ (f₂ t) t := by
    simpa only [f₁, f₂, inner_zero_right, zero_add] using
      (segment_hasDerivAt G H a s t (hG t ht)).inner ℝ (hasDerivAt_const t s)
  have hc₂ : ContinuousOn f₂ (Icc 0 1) :=
    (hc.clm_apply continuousOn_const).inner continuousOn_const
  let A := inner ℝ (H 0 s + D a s) s
  let B := inner ℝ (D s s) s
  have hh t (ht : t ∈ Icc (0 : ℝ) 1) : |f₂ t - (A + t * B)| ≤ ρ * ‖s‖ ^ 2 := by
    have he : f₂ t - (A + t * B) = inner ℝ ((H (a + t • s) - H 0 - D (a + t • s)) s) s := by
      simp only [f₂, A, B, map_add, map_smul, add_apply,
        sub_apply, smul_apply, inner_sub_left,
        inner_add_left, real_inner_smul_left]
      ring
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right
        (((H (a + t • s) - H 0 - D (a + t • s)).le_opNorm s).trans
          (mul_le_mul_of_nonneg_right (hrem t ht) (norm_nonneg s))) (norm_nonneg s)).trans_eq
            (by ring))
  have hb := trapezoid_second_affine_remainder f₀ f₁ f₂ hd₁ hd₂ hc₂ A B (ρ * ‖s‖ ^ 2) hh
  simpa only [f₀, f₁, B, trapezoidDefect, segmentValueDefect, zero_smul, one_smul,
    add_zero, innerSL_apply_apply] using hb

/-- A genuine Hessian derivative gives the cubic defect uniformly on every shrinking actual segment.
Article: main_krylov, prop:Fcycle(i), the C3 function-value jet.
Only actual physical derivatives and continuity on their original ball are
assumed; the little-o remainder follows from Frechet differentiability. -/
theorem segmentValueDefect_cubic_expansion (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hD : HasFDerivAt H D 0)
    (hc : ContinuousOn H (Metric.ball 0 r))
    (hF : ∀ z ∈ Metric.ball (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ Metric.ball (0 : E) r, HasFDerivAt G (H z) z) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      ∀ R : ℝ, 0 ≤ R → R < δ → ∀ a s : E,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖a + t • s‖ ≤ R) →
      |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s + inner ℝ (D s s) s / 12| ≤
        η * R * ‖s‖ ^ 2 := by
  intro η hη
  have he : ∀ᶠ z : E in 𝓝 0, ‖H z - H 0 - D z‖ ≤ (2 * η) * ‖z‖ := by
    simpa only [zero_add] using
      Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD) (by positivity : 0 < 2 * η)
  obtain ⟨ρ, hρ, hrem⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ρ r, lt_min hρ hr, min_le_right _ _, ?_⟩
  intro R _ hR a s hseg
  have hball t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • s ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (hseg t ht).trans_lt (hR.trans_le (min_le_right _ _))
  have hb := segmentValueDefect_affine_hessian f G H D a s
    (fun t ht => hF _ (hball t ht)) (fun t ht => hG _ (hball t ht))
    (hc.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hball)
    (2 * η * R) (fun t ht => by
      have hz : dist (a + t • s) 0 < ρ := by
        rw [dist_zero_right]
        exact (hseg t ht).trans_lt (hR.trans_le (min_le_left _ _))
      exact (hrem hz).trans (mul_le_mul_of_nonneg_left (hseg t ht) (by positivity)))
  exact hb.trans_eq (by ring)

/-- Lipschitz variation of the original Hessian derivative gives a genuine fourth-order defect remainder.
Article: main_krylov, prop:Fcycle(i), the Lipschitz-third upgrade.
The bound is uniform over all real segments in a common convex source set. -/
theorem segmentValueDefect_quartic_bound (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (hz : (0 : E) ∈ S)
    (hF : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ S, HasFDerivAt G (H z) z)
    (hD : ∀ z ∈ S, HasFDerivAt H (D z) z)
    {L : NNReal} (hLip : LipschitzOnWith L D S)
    (a s : E) (R : ℝ) (hR : 0 ≤ R)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • s ∈ S ∧ ‖a + t • s‖ ≤ R) :
    |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s + inner ℝ (D 0 s s) s / 12| ≤
      (L : ℝ) * R ^ 2 * ‖s‖ ^ 2 / 2 := by
  have hc : ContinuousOn H S := fun z hz => (hD z hz).continuousAt.continuousWithinAt
  apply segmentValueDefect_affine_hessian f G H (D 0) a s
    (fun t ht => hF _ (hseg t ht).1) (fun t ht => hG _ (hseg t ht).1)
    (hc.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => (hseg t ht).1))
  intro t ht
  exact (genuine_first_order_quadratic H D S hS hz hD hLip _ (hseg t ht).1).trans
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hR).mpr (hseg t ht).2) L.coe_nonneg)

end
end krylov.Functions
