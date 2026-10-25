import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: chebyshev2, Lemma 16.
Closed-interval extension of a continuous classical derivative.
Use: `chebyshev2.Calculus.hasDerivWithinAt_Icc_of_continuous_derivative` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.defect_derivative` (defect derivative).
Proof chain: `chebyshev2.Primal.determinant_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
open Set Filter
open scoped Topology ContDiff

 /--
Establishes the uniform, quantified assertion `∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a
b) x`.

Use: `chebyshev2.Calculus.contDiffOn_Icc_of_smooth_derivative` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ f (Icc a b)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `x=a` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the asserted
relation at an arbitrary point in that intersection.
-/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x := by
  -- Separate `x=a` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  intro x hx
  by_cases hxa : x=a
  · subst x
    -- Record the convergence hlim with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hlim : Tendsto (deriv f) (𝓝[>] a) (𝓝 (g a)) := by
      apply ((continuousWithinAt_Icc_iff_Ici hab).mp (hg a ⟨le_rfl,hab.le⟩) |>.mono Ioi_subset_Ici_self).congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (hd t ht).deriv.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf a ⟨le_rfl,hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) hlim).mono
        Icc_subset_Ici_self
  · by_cases hxb : x=b
    · subst x
      have hlim : Tendsto (deriv f) (𝓝[<] b) (𝓝 (g b)) := by
        apply ((continuousWithinAt_Icc_iff_Iic hab).mp (hg b ⟨hab.le,le_rfl⟩) |>.mono Iio_subset_Iic_self).congr'
        filter_upwards [Ioo_mem_nhdsLT hab] with t ht
        exact (hd t ht).deriv.symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
        ((hf b ⟨hab.le,le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) hlim).mono
          Icc_subset_Iic_self
    · exact (hd x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),lt_of_le_of_ne hx.2 hxb⟩).hasDerivWithinAt

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ f (Icc a b)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedX (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`chebyshev2.Calculus.hasDerivWithinAt_Icc_of_continuous_derivative` with the arguments
shown in the proof.
-/
theorem contDiffOn_Icc_of_smooth_derivative {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hg : ContDiffOn ℝ ∞ g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) : ContDiffOn ℝ ∞ f (Icc a b) := by
  have h := hasDerivWithinAt_Icc_of_continuous_derivative hab hf hg.continuousOn hd
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun x hx => (h x hx).differentiableWithinAt,hg.congr ?_⟩
  intro x hx
  exact ((h x hx).derivWithin ((uniqueDiffOn_Icc hab) x hx))

end chebyshev2.Calculus
