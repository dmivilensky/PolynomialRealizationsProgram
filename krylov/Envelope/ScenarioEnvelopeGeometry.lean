import krylov.Envelope.ScenarioRealizationMinimax
import krylov.Envelope.Geometry

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, actual realization envelope formula and bound.
Use: identify the genuine first-jet envelope with the printed orthogonal
square-root expression and bound the true RFC realization penalty by
the actual attained selection value.
Source: genuine source scenario first variations, actual CG orthogonality,
real Pythagoras and the proved exact orthogonal norm comparison.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The true common reference-plus-unexplored vector is orthogonal to every actual explored scenario variation.
Use: The true common reference-plus-unexplored vector is orthogonal to every actual explored scenario variation.
Article: main_krylov, thm:E and s3:cor:qn, actual realization envelope formula and bound.
Proof: Actual reference CG orthogonality and genuine complementary projection put the common vector in the true explored complement; the real variation is an actual explored projection. -/
theorem scenarioEnvelope_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (Θ : CanonicalScenario n N) :
    inner ℝ (cgCanonicalError base g N+scenarioUnexplored base g N Θ) (scenarioVariation m base g N Θ)=0 := by
  let P := exploredFlag base g N
  have he : cgCanonicalError base g N∈Pᗮ := exploredFlag_error_orthogonal base hb g hcount
  have hi : scenarioUnexplored base g N Θ∈Pᗮ := by
    rw [scenarioUnexplored_actual base hb g N hcount]
    exact P.sub_starProjection_mem_orthogonal _
  rw [real_inner_comm]
  exact (Pᗮ.add_mem he hi) _ (P.starProjection_apply_mem _)

/-- The actual first-jet scenario envelope equals exactly the printed square root of the genuine common norm squared plus the real explored variation norm squared.
Use: The actual first-jet scenario envelope equals exactly the printed square root of the genuine common norm squared plus the real explored variation norm squared.
Article: main_krylov, thm:E and s3:cor:qn, actual realization envelope formula and bound.
Proof: Apply genuine Pythagoras to the proved actual orthogonal decomposition. -/
theorem scenarioEnvelope_source_formula (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (Θ : CanonicalScenario n N) :
    scenarioEnvelope m base g N Θ=Real.sqrt
      (‖cgCanonicalError base g N+scenarioUnexplored base g N Θ‖^2+‖scenarioVariation m base g N Θ‖^2) := by
  simpa only [scenarioEnvelope,pow_two] using norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr
    (scenarioEnvelope_orthogonal base hb g N hcount m Θ)

/-- The actual RFC realization penalty on every genuine budget scenario is at most the true selection value squared divided by twice the actual positive common norm.
Use: The actual RFC realization penalty on every genuine budget scenario is at most the true selection value squared divided by twice the actual positive common norm.
Article: main_krylov, thm:E and s3:cor:qn, actual realization envelope formula and bound.
Proof: Use the genuine quadratic orthogonal comparison against zero explored variation and the real attained RFC selection norm bound, retaining the actual positive denominator. -/
theorem scenarioPenalty_rfc_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (Θ : CanonicalScenario n N) (hΘ : Θ∈scenarioBudget N ω)
    (hu : 0<‖cgCanonicalError base g N+scenarioUnexplored base g N Θ‖) :
    scenarioPenalty (rfcMethod fullMemory 1) base g N Θ≤
      (selectionValue base g N ω)^2/(2*‖cgCanonicalError base g N+scenarioUnexplored base g N Θ‖) := by
  -- The actual RFC explored norm is bounded by the true attained selection value; genuine orthogonal comparison keeps the real common denominator.
  let u := cgCanonicalError base g N+scenarioUnexplored base g N Θ
  let v := scenarioVariation (rfcMethod fullMemory 1) base g N Θ
  have ho : inner ℝ u v=0 := scenarioEnvelope_orthogonal base hb g N hcount _ Θ
  have hc := orthogonal_norm_comparison_quadratic u v 0 hu ho (by simp only [inner_zero_right])
  simp only [add_zero,_root_.norm_zero,zero_pow (by omega : 2≠0),add_zero] at hc
  have hv : ‖v‖≤selectionValue base g N ω :=
    (rfc_selection_value_attained base hb g N hN hcount ω).2 ⟨Θ,hΘ,rfl⟩
  have hs : ‖v‖^2≤(selectionValue base g N ω)^2 := by nlinarith [norm_nonneg v]
  exact (le_abs_self (‖u+v‖-‖u‖)).trans (hc.trans (by
    apply div_le_div_of_nonneg_right hs
    positivity))

end
end krylov.Envelope
