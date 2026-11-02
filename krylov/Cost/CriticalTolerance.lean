import krylov.Design.FCDesignBridge
import krylov.Design.InfinitePowers

/-!
Article: main_krylov, cor:threshold.
Use: identify the actual uniform first-order FC contraction threshold,
including positivity and the inverse finite-bound and asymptotic rules.
Source: the proved actual FC/design equality and positive Lobatto witness.
-/

namespace krylov.Cost
noncomputable section
open Real Filter Set MeasureTheory krylov.Design krylov.Stability
open scoped Topology BigOperators

/-- The actual critical uniform FC tolerance on a finite spectral class. -/
def criticalTolerance (I : chebyshev1.SpectralInterval) (M : ℕ) : ℝ :=
  (optimalValue I M (fun _ ↦ 1) (1 / 2))⁻¹

/-- A nonempty degree budget has a strictly positive optimized FC coefficient. -/
theorem uniformHalfValue_pos (I : chebyshev1.SpectralInterval) {M : ℕ} (hM : 0 < M) :
    0 < optimalValue I M (fun _ ↦ 1) (1 / 2) := by
  have hl := optimalValue_half_lobatto_lower I M M (fun _ ↦ 1) (fun _ ↦ zero_le_one)
  have hf : Finset.univ.filter (fun i : Fin M ↦ i.val + 1 ≤ M) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    omega
  rw [hf] at hl
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hl
  exact (mul_pos (jacobi.Young.sech_pos _) (Nat.cast_pos.mpr hM)).trans_le hl

/-- The actual critical uniform tolerance is positive. -/
theorem criticalTolerance_pos (I : chebyshev1.SpectralInterval) {M : ℕ} (hM : 0 < M) :
    0 < criticalTolerance I M := inv_pos.mpr (uniformHalfValue_pos I hM)

/-- The true worst-reference first-order FC coefficient is below one
exactly below the stated critical tolerance. The contraction is uniform
over references, so it has a common strict margin. -/
theorem fc_uniform_contraction_iff (I : chebyshev1.SpectralInterval) {M : ℕ} (hM : 0 < M)
    {ω : ℝ} (hω : 0 ≤ ω) :
    fcWorstCoefficient (M + 1) I.mu I.kappa (fun _ ↦ ω) < 1 ↔
      ω < criticalTolerance I M := by
  rw [fcWorstCoefficient_uniform I M ω hω]
  unfold criticalTolerance
  rw [← one_div, lt_div_iff₀ (uniformHalfValue_pos I hM)]

/-- Every proved finite upper bound gives the corresponding explicit
lower bound on the actual critical tolerance. -/
theorem criticalTolerance_ge_of_upper (I : chebyshev1.SpectralInterval) {M : ℕ} (hM : 0 < M)
    {U : ℝ} (hU : optimalValue I M (fun _ ↦ 1) (1 / 2) ≤ U) :
    U⁻¹ ≤ criticalTolerance I M := by
  simpa only [criticalTolerance, one_div] using
    one_div_le_one_div_of_le (uniformHalfValue_pos I hM) hU

/-- The actual critical tolerance divided by the true spectral spacing
is the reciprocal of the actual scaled worst FC coefficient. -/
theorem criticalTolerance_div_spacing (I : chebyshev1.SpectralInterval) (M : ℕ) :
    criticalTolerance I M / designSpacing I =
      (designSpacing I * optimalValue I M (fun _ ↦ 1) (1 / 2))⁻¹ := by
  simp only [criticalTolerance, div_eq_mul_inv, mul_inv_rev]

/-- Inversion transfers a proved scaled continuum limit to the actual
critical tolerance, for arbitrary simultaneous spectral and degree regimes. -/
theorem criticalTolerance_scaled_tendsto {X : Type*} {l : Filter X}
    (I : X → chebyshev1.SpectralInterval) (M : X → ℕ) {a : ℝ} (ha : a ≠ 0)
    (h : Tendsto (fun x ↦ designSpacing (I x) *
      optimalValue (I x) (M x) (fun _ ↦ 1) (1 / 2)) l (𝓝 a)) :
    Tendsto (fun x ↦ criticalTolerance (I x) (M x) / designSpacing (I x)) l (𝓝 a⁻¹) := by
  simpa only [criticalTolerance_div_spacing] using h.inv₀ ha

end
end krylov.Cost
