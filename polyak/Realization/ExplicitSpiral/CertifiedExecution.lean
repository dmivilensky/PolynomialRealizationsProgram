import polyak.Realization.ExplicitSpiral.Execution
import polyak.Realization.ExplicitSpiral.Certified

/-!
Article: (spirallower), the complete explicit Y=2 example for every condition number.
Use: the 44 exact signs and the analytic all-index bounds give one actual function
in R³ and the precise lower constant 1/sqrt(5), simultaneously for all horizons.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation Dynamics

/-- Article: the certified source inequalities give the complete actual infinite table. -/
theorem certified_tableFeasible {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) :
    TableFeasible (position (radialWave r) q) (gradient (radialWave r) (multiplier (radialWave r) q) q)
      (value (radialWave r) (multiplier (radialWave r) q) (physicalValueConstant r)) := by
  apply radial_tableFeasible hr hq hF _ (initialized_star_bound hr hq hq1 hF)
  intro k hk δ hδ
  exact (certified_initial_pair_pos hr hq hq1 hF δ hδ k hk).le

/-- Article: the original Polyak executor realizes the fixed Y=2 spiral for every horizon. -/
theorem exists_certified_execution {μ L r : ℝ} (hμ : 0<μ) (hL : μ<L) (hr : 0<r)
    (hF : Spiral.spiralPolynomial r (polyakQ μ L)=0) :
    ∃ ψ : WithLp 2 (ℂ × ℝ) → ℝ, NormalizedSmooth ψ ∧ ∀ N : ℕ,
      iterate (_root_.gradient (denormalizeFunction μ L ψ)) (polyakAlpha μ L) (polyakBeta μ L)
        (position (radialWave r) (polyakQ μ L) (some 0)) N=
          position (radialWave r) (polyakQ μ L) (some N) :=
  exists_execution_of_table hμ hL hr
    (certified_tableFeasible hr (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hF)

/-- Article: the exact quantitative spiral lower bound for one actual function in three dimensions. -/
theorem exists_spiral_lower {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, ‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧ ∀ N : ℕ,
        (1/Real.sqrt 5)*(Spiral.factor (polyakQ μ L))^N*‖x₀‖≤
          ‖iterate (_root_.gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  obtain ⟨hr,hF⟩ := Spiral.factor_spec (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL)
  exact exists_three_dimensional_of_table hμ hL hr
    (certified_tableFeasible hr (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hF)

end
end polyak.Realization.ExplicitSpiral
