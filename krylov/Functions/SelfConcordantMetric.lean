import krylov.Functions.SelfConcordantScalar
import krylov.Functions.SegmentTrapezoid
import krylov.Nonlinear.SelfConcordantFunction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, apG:sc(i), sharp self-concordant Hessian comparison.
Use: derive the printed canonical quadratic-form sandwich directly from the
genuine mixed differential self-concordance hypotheses. Positivity away from
the centre is proved by scalar propagation, not assumed as a metric bound.
Source: Nesterov18, Theorem 5.1.7. We use the reciprocal square root of the
radial quadratic form and the two exact scalar integrating factors.
-/

/-!
Article: krylov, Lemma E.1 [apG:sc].

Canonical Hessian sandwich, sublevel-radius equation and expansion, sharp local Lipschitz bound
and endpoint secant comparison are for genuine scalar-function derivatives.
The Dikin-ball/domain assumptions in the article are essential; the C3 midpoint expansion and
tensor bound follow from the actual third derivative dictionaries.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The printed Hessian sandwich along any genuine unit radial segment.
Article: main_krylov, apG:sc(i).
Proof: propagate radial positivity from the identity Hessian, obtain its exact
inverse-square-root bound, and apply the mixed scalar integrating factors to
each actual quadratic form. -/
theorem selfConcordant_unit_metric (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    (hD : ∀ t ∈ Icc (0 : ℝ) r, HasFDerivAt H (D (t • u)) (t • u))
    (hn : ∀ t ∈ Icc (0 : ℝ) r, ∀ v : E, 0 ≤ inner ℝ v (H (t • u) v))
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, ∀ a b c : E,
      |inner ℝ b (D (t • u) a c)| ≤
        2 * Real.sqrt (inner ℝ a (H (t • u) a)) *
          Real.sqrt (inner ℝ b (H (t • u) b)) * Real.sqrt (inner ℝ c (H (t • u) c)))
    (v : E) :
    (1 - r) ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ v (H (r • u) v) ∧
      inner ℝ v (H (r • u) v) ≤ (1 - r)⁻¹ ^ 2 * ‖v‖ ^ 2 := by
  let q := fun t : ℝ => inner ℝ u (H (t • u) u)
  let q' := fun t : ℝ => inner ℝ u (D (t • u) u u)
  have hline t (ht : t ∈ Icc (0 : ℝ) r) :
      HasDerivAt (fun t : ℝ => H (t • u)) (D (t • u) u) t := by
    simpa only [zero_add] using segment_hasDerivAt H D 0 u t (by simpa using hD t ht)
  have hq t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt q (q' t) t := by
    simpa [q, q'] using (hasDerivAt_const t u).inner ℝ
      ((hline t ht).clm_apply (hasDerivAt_const t u))
  have hq₀ : q 0 = 1 := by simp [q, hH₀, hu]
  have hqsc t (ht : t ∈ Icc (0 : ℝ) r) : |q' t| ≤ 2 * (Real.sqrt (q t)) ^ 3 := by
    exact (hsc t ht u u u).trans_eq (by dsimp [q]; ring)
  have hqpos := selfConcordant_scalar_positive q q' hr (by rw [hq₀]; norm_num)
    (fun t ht => hn t ht u) hq hqsc
  have hqupper t (ht : t ∈ Icc (0 : ℝ) r) : Real.sqrt (q t) ≤ (1 - t)⁻¹ := by
    exact (selfConcordant_scalar_upper q q' ht.1 (ht.2.trans_lt hr1) hq₀
      (fun s hs => hqpos s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hq s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hqsc s ⟨hs.1, hs.2.trans ht.2⟩)).1
  let a := fun t : ℝ => inner ℝ v (H (t • u) v)
  let a' := fun t : ℝ => inner ℝ v (D (t • u) u v)
  have ha t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt a (a' t) t := by
    simpa [a, a'] using (hasDerivAt_const t v).inner ℝ
      ((hline t ht).clm_apply (hasDerivAt_const t v))
  have hab t (ht : t ∈ Icc (0 : ℝ) r) : |a' t| ≤ 2 * a t / (1 - t) := by
    have hasq : (Real.sqrt (a t)) ^ 2 = a t := Real.sq_sqrt (hn t ht v)
    calc
      |a' t| ≤ 2 * Real.sqrt (q t) * Real.sqrt (a t) * Real.sqrt (a t) := hsc t ht u v v
      _ = 2 * Real.sqrt (q t) * (Real.sqrt (a t)) ^ 2 := by ring
      _ = 2 * a t * Real.sqrt (q t) := by rw [hasq]; ring
      _ ≤ 2 * a t * (1 - t)⁻¹ :=
        mul_le_mul_of_nonneg_left (hqupper t ht) (mul_nonneg (by norm_num) (hn t ht v))
      _ = _ := by rw [div_eq_mul_inv]
  simpa [a, hH₀, real_inner_self_eq_norm_sq] using
    selfConcordant_mixed_scalar_sandwich a a' hr hr1 ha hab

/-- Every actual mixed self-concordant Hessian has the sharp canonical sandwich.
Article: main_krylov, apG:sc(i).
Proof: normalize the actual displacement to a unit radial direction and use
the proved scalar propagation on its entire enclosed radial segment. -/
theorem selfConcordant_metric_sandwich (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E) (U : Set E) (hU : Convex ℝ U)
    (h₀ : (0 : E) ∈ U) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    (hD : ∀ z ∈ U, HasFDerivAt H (D z) z)
    (hn : ∀ z ∈ U, ∀ v : E, 0 ≤ inner ℝ v (H z v))
    (hsc : ∀ z ∈ U, ∀ a b c : E, |inner ℝ b (D z a c)| ≤
      2 * Real.sqrt (inner ℝ a (H z a)) * Real.sqrt (inner ℝ b (H z b)) *
        Real.sqrt (inner ℝ c (H z c)))
    (y : E) (hy : y ∈ U) (hy1 : ‖y‖ < 1) (v : E) :
    (1 - ‖y‖) ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ v (H y v) ∧
      inner ℝ v (H y v) ≤ (1 - ‖y‖)⁻¹ ^ 2 * ‖v‖ ^ 2 := by
  by_cases hy₀ : y = 0
  · simp [hy₀, hH₀]
  · let u := ‖y‖⁻¹ • y
    have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy₀
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
    have hpath t (ht : t ∈ Icc (0 : ℝ) ‖y‖) : t • u ∈ U := by
      have hs : t / ‖y‖ ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hnorm.le, (div_le_one hnorm).mpr ht.2⟩
      have h := hU.add_smul_mem h₀ (by simpa using hy) hs
      simpa only [u, smul_smul, div_eq_mul_inv, zero_add] using h
    have h := selfConcordant_unit_metric H D u hu (norm_nonneg y) hy1 hH₀
      (fun t ht => hD _ (hpath t ht)) (fun t ht => hn _ (hpath t ht))
      (fun t ht => hsc _ (hpath t ht)) v
    simpa only [u, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul] using h

variable [CompleteSpace E]

/-- The sharp metric sandwich applies to genuine scalar self-concordant functions.
Article: main_krylov, apG:sc(i), actual-function statement.
Proof: all Hessian derivative, positivity and mixed bounds come from the
primitive genuine differential data, so no metric estimate is an input. -/
theorem standardSelfConcordant_metric (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E)
    (y : E) (hy : y ∈ U) (hy1 : ‖y‖ < 1) (v : E) :
    (1 - ‖y‖) ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ v (D.hessian y v) ∧
      inner ℝ v (D.hessian y v) ≤ (1 - ‖y‖)⁻¹ ^ 2 * ‖v‖ ^ 2 :=
  selfConcordant_metric_sandwich D.hessian D.variation U D.convex_domain h₀ hH₀
    D.hessian_derivative D.hessian_nonnegative D.mixed y hy hy1 v

end
end krylov.Functions
