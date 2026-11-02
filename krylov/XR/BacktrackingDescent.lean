import krylov.XR.Safeguard
import krylov.Functions.SegmentTrapezoid

/-!
Article: main_krylov, thm:XR, genuine descent lemma and acceptance threshold.
Use: prove acceptance for small real tested steps directly from the actual
first derivative and the global Lipschitz gradient assumption.
Source: integrate the derivative on a real segment (the usual descent lemma).
-/

namespace krylov.XR
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual scalar quotient tested by XR. All values are real in this
exact-arithmetic formalization; the safeguard proves its denominator positive. -/
def trialQuotient (f : E → ℝ) (x g u : E) (t : ℝ) : ℝ :=
  2 * (f (x + t • u) - f x - t * inner ℝ g u) / (-t * inner ℝ g u)

/-- Exact acceptance predicate of the displayed XR backtracking. -/
def Accepted (f : E → ℝ) (sigma : ℝ) (x g u : E) (t : ℝ) : Prop :=
  trialQuotient f x g u t ≤ 2 * (1 - sigma)

/-- Genuine Lipschitz-gradient descent lemma, with the sharp factor one half.
No Taylor remainder bound is supplied as an assumption. -/
theorem descent_lemma (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hG : LipschitzWith L G) (x s : E) :
    |f (x + s) - f x - inner ℝ (G x) s| ≤ (L : ℝ) * ‖s‖ ^ 2 / 2 := by
  let F := fun t : ℝ => f (x + t • s) - t * inner ℝ (G x) s
  let d := fun t : ℝ => inner ℝ (G (x + t • s) - G x) s
  have hd t : HasDerivAt F (d t) t := by
    have hf := krylov.Functions.segment_hasDerivAt f
      (fun z => innerSL ℝ (G z)) x s t (hF _)
    convert hf.sub ((hasDerivAt_id t).mul_const (inner ℝ (G x) s)) using 1
    · rfl
    · simp [d, inner_sub_left]
  have hc : Continuous d :=
    ((hG.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
      continuous_const).inner continuous_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hd t) (hc.intervalIntegrable 0 1)
  have hb t (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖d t‖ ≤ t * ((L : ℝ) * ‖s‖ ^ 2) := by
    have hg := hG.norm_sub_le (x + t • s) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at hg
    calc
      ‖d t‖ ≤ ‖G (x + t • s) - G x‖ * ‖s‖ := norm_inner_le_norm _ _
      _ ≤ ((L : ℝ) * (t * ‖s‖)) * ‖s‖ :=
        mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (f := d)
    (g := fun t : ℝ => t * ((L : ℝ) * ‖s‖ ^ 2))
    (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
    ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
  rw [he] at hi
  have hid : F 1 - F 0 = f (x + s) - f x - inner ℝ (G x) s := by
    dsimp only [F]
    simp only [one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul]
    ring
  rw [hid, Real.norm_eq_abs] at hi
  norm_num [intervalIntegral.integral_mul_const] at hi
  convert hi using 1
  ring

/-- With positive step and negative slope the XR quotient is exactly the
usual Armijo test. -/
theorem accepted_iff_armijo (f : E → ℝ) (sigma : ℝ) (x g u : E)
    (t : ℝ) (ht : 0 < t) (hu : inner ℝ g u < 0) :
    Accepted f sigma x g u t ↔
      f (x + t • u) ≤ f x + sigma * t * inner ℝ g u := by
  have hd : 0 < -t * inner ℝ g u := mul_pos_of_neg_of_neg (neg_neg_of_pos ht) hu
  unfold Accepted trialQuotient
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- Every sufficiently small positive trial is accepted by the actual XR
test; the displayed threshold is derived from the actual gradient. -/
theorem accepted_of_step_le (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (c₁ c₂ sigma : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsigma : sigma < 1) (x u : E) (hg : G x ≠ 0)
    (hu : GradientRelated c₁ c₂ (G x) u) (t : ℝ) (ht : 0 < t)
    (hbound : t ≤ 2 * (1 - sigma) * c₁ / ((L : ℝ) * c₂ ^ 2)) :
    Accepted f sigma x (G x) u t := by
  have hn : 0 < ‖G x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hs : inner ℝ (G x) u < 0 := hu.1.trans_lt (by nlinarith)
  apply (accepted_iff_armijo f sigma x (G x) u t ht hs).2
  have hd := (abs_le.mp (descent_lemma f G hF L hG x (t • u))).2
  rw [inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le] at hd
  have hsq : ‖u‖ ^ 2 ≤ c₂ ^ 2 * ‖G x‖ ^ 2 := by
    nlinarith [hu.2, norm_nonneg u, norm_nonneg (G x),
      sq_nonneg (c₂ * ‖G x‖ - ‖u‖)]
  have htime : (L : ℝ) * c₂ ^ 2 * t ≤ 2 * (1 - sigma) * c₁ :=
    by simpa only [mul_comm] using
      (le_div_iff₀ (mul_pos hL (sq_pos_of_pos hc₂))).mp hbound
  have hcurv : (L : ℝ) * (t * ‖u‖) ^ 2 / 2 ≤
      (1 - sigma) * c₁ * t * ‖G x‖ ^ 2 := by
    calc
      (L : ℝ) * (t * ‖u‖) ^ 2 / 2 ≤
          (L : ℝ) * t ^ 2 * (c₂ ^ 2 * ‖G x‖ ^ 2) / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hL.le (sq_nonneg t))]
      _ ≤ (1 - sigma) * c₁ * t * ‖G x‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right htime (mul_nonneg ht.le hn.le)]
  have hgrad := mul_le_mul_of_nonneg_left hu.1 (mul_nonneg (sub_nonneg.mpr hsigma.le) ht.le)
  nlinarith

end
end krylov.XR
