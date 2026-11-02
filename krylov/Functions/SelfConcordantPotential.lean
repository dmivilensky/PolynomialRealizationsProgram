import krylov.Functions.SelfConcordantMetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: main_krylov, apG:sc(ii), the self-concordant potential comparison.
Use: obtain the actual lower and upper logarithmic barriers from the primitive
scalar self-concordance derivatives; these are the sublevel enclosure inputs.
Source: Nesterov18, inequalities (5.1.14) and (5.1.16). The proof compares the
actual second derivatives twice, so no potential bound is a hypothesis.
-/

namespace krylov.Functions
noncomputable section
open Set

/-- The standard lower self-concordant potential.
Article: main_krylov, apG:sc(ii). -/
def scOmega (t : ℝ) : ℝ := t - Real.log (1 + t)

/-- The standard upper self-concordant potential.
Article: main_krylov, apG:sc(ii). -/
def scOmegaStar (t : ℝ) : ℝ := -t - Real.log (1 - t)

/-- The actual first derivative of the lower potential.
Article: main_krylov, apG:sc(ii). Proof: the ordinary logarithm chain rule. -/
theorem scOmega_hasDerivAt {t : ℝ} (ht : -1 < t) :
    HasDerivAt scOmega (t / (1 + t)) t := by
  convert! (hasDerivAt_id t).sub (((hasDerivAt_const t (1 : ℝ)).add
    (hasDerivAt_id t)).log (by linarith : (1 : ℝ) + t ≠ 0)) using 1
  all_goals dsimp
  all_goals field_simp [show (1 : ℝ) + t ≠ 0 by linarith]
  all_goals ring

/-- The actual second derivative of the lower potential.
Article: main_krylov, apG:sc(ii). Proof: the quotient rule. -/
theorem scOmega_second_hasDerivAt {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun t : ℝ => t / (1 + t)) ((1 + t)⁻¹ ^ 2) t := by
  convert! (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t))
    (by linarith : (1 : ℝ) + t ≠ 0) using 1
  all_goals dsimp
  all_goals field_simp [show (1 : ℝ) + t ≠ 0 by linarith]
  all_goals ring

/-- The actual first derivative of the upper potential.
Article: main_krylov, apG:sc(ii). Proof: the ordinary logarithm chain rule. -/
theorem scOmegaStar_hasDerivAt {t : ℝ} (ht : t < 1) :
    HasDerivAt scOmegaStar (t / (1 - t)) t := by
  convert! (hasDerivAt_id t).neg.sub (((hasDerivAt_const t (1 : ℝ)).sub
    (hasDerivAt_id t)).log (by linarith : (1 : ℝ) - t ≠ 0)) using 1
  all_goals dsimp
  all_goals field_simp [show (1 : ℝ) - t ≠ 0 by linarith]
  all_goals ring

/-- The actual second derivative of the upper potential.
Article: main_krylov, apG:sc(ii). Proof: the quotient rule. -/
theorem scOmegaStar_second_hasDerivAt {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t : ℝ => t / (1 - t)) ((1 - t)⁻¹ ^ 2) t := by
  convert! (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    (by linarith : (1 : ℝ) - t ≠ 0) using 1
  all_goals dsimp
  all_goals field_simp [show (1 : ℝ) - t ≠ 0 by linarith]
  all_goals ring

/-- Comparing genuine second derivatives with equal initial slopes compares actual increments.
Article: main_krylov, apG:sc(ii).
Proof: apply scalar monotonicity first to the actual derivative difference,
then to the actual function difference. -/
theorem second_derivative_increment_comparison (f f₁ f₂ g g₁ g₂ : ℝ → ℝ)
    {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt f₁ (f₂ t) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt g (g₁ t) t)
    (hg₁ : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt g₁ (g₂ t) t)
    (h₀ : f₁ 0 = g₁ 0) (hb : ∀ t ∈ Icc (0 : ℝ) r, f₂ t ≤ g₂ t) :
    f r - f 0 ≤ g r - g 0 := by
  have hd₁ t (ht : t ∈ Icc (0 : ℝ) r) :
      HasDerivAt (fun t : ℝ => g₁ t - f₁ t) (g₂ t - f₂ t) t := (hg₁ t ht).sub (hf₁ t ht)
  have hm₁ : MonotoneOn (fun t : ℝ => g₁ t - f₁ t) (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hd₁ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd₁ t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => sub_nonneg.mpr (hb t (interior_subset ht)))
  have hb₁ t (ht : t ∈ Icc (0 : ℝ) r) : 0 ≤ g₁ t - f₁ t := by
    have h := hm₁ (left_mem_Icc.mpr hr) ht ht.1
    simpa only [h₀, sub_self] using h
  have hd₂ t (ht : t ∈ Icc (0 : ℝ) r) :
      HasDerivAt (fun t : ℝ => g t - f t) (g₁ t - f₁ t) t := (hg t ht).sub (hf t ht)
  have hm₂ : MonotoneOn (fun t : ℝ => g t - f t) (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hd₂ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd₂ t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hb₁ t (interior_subset ht))
  have h := hm₂ (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  linarith

/-- Genuine scalar self-concordance implies both exact logarithmic potential bounds.
Article: main_krylov, apG:sc(ii), scalar comparison.
Proof: positivity propagates from the normalized initial Hessian; the exact
radial second-derivative bounds compare with omega and omega-star twice. -/
theorem selfConcordant_scalar_potential (f f₁ p p' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt f₁ (p t) t)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt p (p' t) t)
    (hf₀ : f₁ 0 = 0) (hp₀ : p 0 = 1)
    (hp : ∀ t ∈ Icc (0 : ℝ) r, 0 ≤ p t)
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3) :
    scOmega r ≤ f r - f 0 ∧ (r < 1 → f r - f 0 ≤ scOmegaStar r) := by
  have hpos := selfConcordant_scalar_positive p p' hr (by rw [hp₀]; norm_num) hp hd hsc
  have hlow t (ht : t ∈ Icc (0 : ℝ) r) : (1 + t)⁻¹ ^ 2 ≤ p t :=
    selfConcordant_scalar_lower p p' ht.1 hp₀
      (fun s hs => hpos s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hd s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hsc s ⟨hs.1, hs.2.trans ht.2⟩)
  constructor
  · have h := second_derivative_increment_comparison scOmega (fun t => t / (1 + t))
      (fun t => (1 + t)⁻¹ ^ 2) f f₁ p hr
      (fun t ht => scOmega_hasDerivAt (by linarith [ht.1]))
      (fun t ht => scOmega_second_hasDerivAt (by linarith [ht.1])) hf hf₁
      (by simp [hf₀]) hlow
    simpa only [scOmega, Real.log_one, add_zero, sub_self, sub_zero] using h
  · intro hr1
    have hu t (ht : t ∈ Icc (0 : ℝ) r) : p t ≤ (1 - t)⁻¹ ^ 2 :=
      (selfConcordant_scalar_upper p p' ht.1 (ht.2.trans_lt hr1) hp₀
        (fun s hs => hpos s ⟨hs.1, hs.2.trans ht.2⟩)
        (fun s hs => hd s ⟨hs.1, hs.2.trans ht.2⟩)
        (fun s hs => hsc s ⟨hs.1, hs.2.trans ht.2⟩)).2
    have h := second_derivative_increment_comparison f f₁ p scOmegaStar
      (fun t => t / (1 - t)) (fun t => (1 - t)⁻¹ ^ 2) hr hf hf₁
      (fun t ht => scOmegaStar_hasDerivAt (ht.2.trans_lt hr1))
      (fun t ht => scOmegaStar_second_hasDerivAt (ht.2.trans_lt hr1)) (by simp [hf₀]) hu
    simpa only [scOmegaStar, neg_zero, sub_zero, Real.log_one, sub_self] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open scoped InnerProductSpace

/-- The logarithmic potential comparison holds on every genuine unit radial segment.
Article: main_krylov, apG:sc(ii), actual-function radial comparison.
Proof: the true gradient, Hessian and third derivative supply each scalar
derivative in the previously proved self-concordant comparison. -/
theorem standardSelfConcordant_unit_potential (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (hg₀ : gradient f (0 : E) = 0) (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E)
    (u : E) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hpath : ∀ t ∈ Icc (0 : ℝ) r, t • u ∈ U) :
    scOmega r ≤ f (r • u) - f 0 ∧
      (r < 1 → f (r • u) - f 0 ≤ scOmegaStar r) := by
  let F := fun t : ℝ => f (t • u)
  let F₁ := fun t : ℝ => inner ℝ (gradient f (t • u)) u
  let p := fun t : ℝ => inner ℝ u (D.hessian (t • u) u)
  let p' := fun t : ℝ => inner ℝ u (D.variation (t • u) u u)
  have hF t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt F (F₁ t) t := by
    have hf : HasFDerivAt f (innerSL ℝ (gradient f (t • u))) (t • u) :=
      (D.differentiable.differentiableAt (D.open_domain.mem_nhds (hpath t ht))).hasGradientAt.hasFDerivAt
    simpa only [F, F₁, zero_add] using!
      segment_hasDerivAt f (fun z => innerSL ℝ (gradient f z)) 0 u t (by simpa using hf)
  have hF₁ t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt F₁ (p t) t := by
    have h := segment_hasDerivAt (gradient f) D.hessian 0 u t
      (by simpa using D.gradient_derivative _ (hpath t ht))
    simpa [F₁, p, real_inner_comm] using h.inner ℝ (hasDerivAt_const t u)
  have hp t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt p (p' t) t := by
    have h := segment_hasDerivAt D.hessian D.variation 0 u t
      (by simpa using D.hessian_derivative _ (hpath t ht))
    simpa [p, p'] using (hasDerivAt_const t u).inner ℝ
      (h.clm_apply (hasDerivAt_const t u))
  have hsc t (ht : t ∈ Icc (0 : ℝ) r) : |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3 :=
    (D.mixed _ (hpath t ht) u u u).trans_eq (by dsimp [p]; ring)
  have hF₀ : F₁ 0 = 0 := by
    change inner ℝ (gradient f ((0 : ℝ) • u)) u = 0
    rw [zero_smul, hg₀, inner_zero_left]
  simpa only [F, zero_smul] using selfConcordant_scalar_potential F F₁ p p' hr hF hF₁ hp
    hF₀ (by simp [p, hH₀, hu])
    (fun t ht => D.hessian_nonnegative _ (hpath t ht) u) hsc

/-- Genuine canonically normalized self-concordant functions obey the two potential bounds.
Article: main_krylov, apG:sc(ii), actual-function potential comparison.
Proof: normalize the actual displacement and enclose its entire radial
segment in the original convex domain. The lower bound has no unit-radius
restriction; the upper bound applies below the Dikin radius. -/
theorem standardSelfConcordant_potential (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hg₀ : gradient f (0 : E) = 0)
    (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E) (y : E) (hy : y ∈ U) :
    scOmega ‖y‖ ≤ f y - f 0 ∧ (‖y‖ < 1 → f y - f 0 ≤ scOmegaStar ‖y‖) := by
  by_cases hy₀ : y = 0
  · simp [hy₀, scOmega, scOmegaStar]
  · let u := ‖y‖⁻¹ • y
    have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy₀
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
    have hpath t (ht : t ∈ Icc (0 : ℝ) ‖y‖) : t • u ∈ U := by
      have hs : t / ‖y‖ ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hnorm.le, (div_le_one hnorm).mpr ht.2⟩
      have h := D.convex_domain.add_smul_mem h₀ (by simpa using hy) hs
      simpa only [u, smul_smul, div_eq_mul_inv, zero_add] using h
    have h := standardSelfConcordant_unit_potential f U D hg₀ hH₀ u hu (norm_nonneg y) hpath
    simpa only [u, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul] using h

end
end krylov.Functions
