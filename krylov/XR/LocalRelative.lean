import krylov.XR.LocalCoercivity
import krylov.XR.HermitianNorm

/-!
Article: main_krylov, apG:local(a), actual relative defect estimate.
Use: the primitive secant-error budget gives the printed relative bound
2 p epsilon / c_T and therefore the actual Hermitian gate eventually passes.
Source: the positive-root C*-norm identity and proved actual coefficient
coercivity, with no supplied acceptance certificate.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Squared inverse-root norm is exactly the norm of the actual inverse
model, including the vacuous zero-dimensional space. -/
theorem metricRoot_inverse_norm_sq (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    ‖(metricRoot T)⁻¹‖ ^ 2 = ‖T⁻¹‖ := by
  have hs : star ((metricRoot T)⁻¹) = (metricRoot T)⁻¹ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      transpose_nonsing_inv, (metricRoot_isSymm T).eq]
  calc
    _ = ‖star ((metricRoot T)⁻¹) * (metricRoot T)⁻¹‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖T⁻¹‖ := by
      rw [hs, ← Matrix.mul_inv_rev, metricRoot_square T hT]

/-- Arbitrary real observed errors, including skew errors, have the
original physical inverse-model relative norm estimate. -/
theorem relativeBudget_le_inverse_norm (T D : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) : relativeBudget T D ≤ ‖T⁻¹‖ * ‖D‖ := by
  change ‖(metricRoot T)⁻¹ * D * (metricRoot T)⁻¹‖ ≤ _
  calc
    _ ≤ (‖(metricRoot T)⁻¹‖ * ‖D‖) * ‖(metricRoot T)⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖(metricRoot T)⁻¹‖ ^ 2 * ‖D‖ := by ring
    _ = _ := by rw [metricRoot_inverse_norm_sq T hT]

/-- The genuine relative skew defect satisfies exactly the local bound
printed in the article, on arbitrary normalized independent p-column data. -/
theorem local_relative_defect_bound (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4) :
    relativeBudget (latest (crossGram s y)) (defect (crossGram s y)) ≤
      2 * (p : ℝ) * epsilon / localCoercivity mu sigma := by
  have hd := local_observed_domains H hH s y hs mu sigma epsilon hmu hsigma he
    hpositive hindependent hy hsmall
  have hc : 0 ≤ (localCoercivity mu sigma)⁻¹ := by unfold localCoercivity; positivity
  calc
    _ ≤ ‖(latest (crossGram s y))⁻¹‖ * ‖defect (crossGram s y)‖ :=
      relativeBudget_le_inverse_norm _ _ hd.1
    _ ≤ (localCoercivity mu sigma)⁻¹ * (2 * (p : ℝ) * epsilon) :=
      mul_le_mul hd.2.2.1 (local_defect_norm H hH s y hs he hy) (norm_nonneg _) hc
    _ = _ := by ring

/-- A small primitive actual secant-error allowance forces the actual
complex window test to pass. This discharges its algorithmic branch from
local source hypotheses rather than assuming eventual gate acceptance. -/
theorem local_windowUnrefuted (theta : ℝ) (htheta : 0 < theta)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * (p : ℝ) * epsilon / localCoercivity mu sigma < theta) :
    windowUnrefuted theta (crossGram s y) := by
  apply (windowUnrefuted_iff theta htheta _).2
  exact ⟨(local_observed_domains H hH s y hs mu sigma epsilon hmu hsigma he
    hpositive hindependent hy hsmall).1,
    (local_relative_defect_bound H hH s y hs mu sigma epsilon hmu hsigma he
      hpositive hindependent hy hsmall).trans_lt hgate⟩

end
end krylov.XR
