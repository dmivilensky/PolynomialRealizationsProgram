import krylov.Numerics.HalfCertifiedBounds
import krylov.Certificates.EndpointCertifiedBounds
import krylov.Certificates.DerivedValues
import krylov.Strings.OptimizerRegularMaximum

/-!
Article: main_krylov, apC:prop:digits and thm:value.
Use: attach the exact rational certificates to the same actual unique maximizing
Stieltjes strings used by the analytic theory. Neither a computed crossing nor
an optimizer certificate is an input of the final existence theorem.
Source: the proved differential barriers, analytic shooting construction and
general BV optimality/uniqueness theorem; square-root and reciprocal arithmetic.
-/

namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra krylov.ContinuumControl krylov.Strings

/-- Strict half-last-unit bounds certify round-to-nearest values at the agreed
five significant decimal digits. These refer respectively to the two crossings,
the half-gamma optimum, its reciprocal square, the FC threshold coefficient,
the endpoint optimum and the physical Hilbert--Schmidt coefficient. -/
def FiveDigitValues (s t : ℝ) : Prop :=
    |s - 17654 / 10000| < 1 / 20000 ∧
    |t - 26467 / 10000| < 1 / 20000 ∧
    |Real.sqrt s - 13287 / 10000| < 1 / 20000 ∧
    |s⁻¹ - 56646 / 100000| < 1 / 200000 ∧
    |2 / Real.sqrt s - 15053 / 10000| < 1 / 20000 ∧
    |Real.sqrt t / 2 - 81343 / 100000| < 1 / 200000 ∧
    |Real.sqrt (Real.sqrt t / 8) - 45095 / 100000| < 1 / 200000

/-- Both certified constants are values of genuinely constructed unique
maximizing strings. All decimal bounds are conclusions, and the actual state,
analytic density, original all-string comparison and equality case concern
these same masses through `ActualRegularMaximum`. -/
theorem exists_certified_continuum_maxima :
    ∃ G : SubcriticalGraph (1 / 2), ∃ σ : ℝ → ℝ,
      ((176535 / 100000 : ℝ) < G.σ 1 ∧ G.σ 1 < 176536 / 100000) ∧
      ((264667 / 100000 : ℝ) < σ 1 ∧ σ 1 < 264668 / 100000) ∧
      FiveDigitValues (G.σ 1) (σ 1) ∧
      (∃ M : Mass, ∃ φ v : ℝ → ℝ, ActualRegularMaximum (1 / 2) G.σ M φ v) ∧
      (∃ N : Mass, ∃ ψ w : ℝ → ℝ, ActualRegularMaximum 1 σ N ψ w) := by
  obtain ⟨G⟩ := exists_subcriticalGraph
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hs := G.half_certified_five_digit_bounds
  obtain ⟨σ, ε, hε, ha, hb⟩ := exists_analytic_endpoint_graph
  have hcorr : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3 :=
    fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩
  have hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r :=
    fun r hr ↦ (ha r (by linarith)).2.2.2
  have ht := endpoint_certified_crossing_bounds (endpoint_gap_of_graph hcorr hd)
  have ht' : (264667 / 100000 : ℝ) < σ 1 ∧ σ 1 < 264668 / 100000 := by
    constructor <;> linarith [ht.1, ht.2]
  have hgraph : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt 1 σ r := by
    intro r hr
    have hh := ha r (by linarith)
    refine ⟨hh.1, hh.2.1, hh.1.differentiableAt, ?_⟩
    rw [hh.2.2.2.deriv]
    have hr₀ : r ≠ 0 := by linarith
    have hden : σ r + 1 - r ≠ 0 := hh.2.2.1.ne'
    field_simp
  refine ⟨G, σ, hs, ht', ?_, ?_, ?_⟩
  · exact five_significant_derived_values hs.1 hs.2 ht'.1 ht'.2
  · exact OptimizerQuadratures.exists_actual_subcritical_regular_maximum
      (by norm_num) (by norm_num) G
  · exact OptimizerQuadratures.exists_actual_endpoint_regular_maximum hgraph hcorr hd

end
end krylov.Certificates
