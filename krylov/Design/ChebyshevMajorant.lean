import krylov.Design.Interval
import chebyshev1.Chebyshev.Polynomial

/-!
Article: main_krylov, lem:chebyshev-design, universal Chebyshev majorants.
Use: reuse the existing genuine normalized Chebyshev polynomial to bound the
all-probability-measures design objective, without a finite support premise.
Source: Greenbaum79 and HoelLevine64; polynomial normalization and uniform
interval bounds are imported from the earlier Chebyshev formalization.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory

/-- The already proved Chebyshev residual is an admissible physical design competitor.
Article: main_krylov, lem:chebyshev-design.
Proof: reuse its exact degree and normalization at the original exterior point zero. -/
def chebyshevCompetitor (I : chebyshev1.SpectralInterval) (m : ℕ) : Competitor m 0 :=
  ⟨I.residual m, (I.residual_natDegree m).le, by
    rw [I.residual_eval, show I.z 0 = I.eta by
      simp [chebyshev1.SpectralInterval.z, chebyshev1.SpectralInterval.eta]]
    exact div_self (I.den_ne m)⟩

/-- The original Chebyshev scale is strictly positive.
Article: main_krylov, lem:chebyshev-design. Proof: positivity of its exterior denominator. -/
theorem chebyshev_scale_pos (I : chebyshev1.SpectralInterval) (m : ℕ) : 0 < I.epsilon m :=
  one_div_pos.mpr (I.den_pos m)

/-- Every genuine probability design satisfies the single-degree Chebyshev upper bound.
Article: main_krylov, lem:chebyshev-design, the universal half of the sharp extremum.
Proof: integrate the existing pointwise residual bound and compare the actual variational infimum. -/
theorem christoffel_le_chebyshev (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    christoffel m 0 (spectralCoordinate I) ν ≤ (I.epsilon m) ^ 2 := by
  have hi : Integrable (fun t : Spectrum I => ((I.residual m).eval t.val) ^ 2) ν :=
    (((I.residual m).continuous.comp continuous_subtype_val).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (t : Spectrum I) : ((I.residual m).eval t.val) ^ 2 ≤ (I.epsilon m) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg ((I.residual m).eval t.val)) (chebyshev_scale_pos I m).le).mpr
      (I.residual_abs_le m t.property)
    simpa only [sq_abs] using h
  have hb := integral_mono hi (integrable_const ((I.epsilon m) ^ 2)) hp
  have h := christoffel_le m 0 (spectralCoordinate I) ν (chebyshevCompetitor I m)
  exact h.trans (by simpa only [polynomialEnergy, chebyshevCompetitor, spectralCoordinate,
    ContinuousMap.coe_mk, integral_const, probReal_univ, smul_eq_mul, one_mul] using hb)

/-- The energy-error form of the same all-measures Chebyshev bound.
Article: main_krylov, lem:chebyshev-design.
Proof: use the actual nonnegative Christoffel criterion and its squared polynomial majorant. -/
theorem sqrt_christoffel_le_chebyshev (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    Real.sqrt (christoffel m 0 (spectralCoordinate I) ν) ≤ I.epsilon m :=
  Real.sqrt_le_iff.mpr ⟨(chebyshev_scale_pos I m).le, christoffel_le_chebyshev I m ν⟩

/-- The original mixed FC design is bounded by the sum of the known Chebyshev scales.
Article: main_krylov, the upper Chebyshev majorant after thm:B.
Proof: apply the proved actual single-degree bound termwise, retaining zero weights. -/
theorem intervalObjective_half_majorant (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M w (1 / 2) ν ≤ ∑ i, w i * I.epsilon (i.val + 1) := by
  unfold intervalObjective mixedObjective
  apply Finset.sum_le_sum
  intro i _
  rw [← Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (sqrt_christoffel_le_chebyshev I (i.val + 1) ν) (hw i)

end
end krylov.Design
