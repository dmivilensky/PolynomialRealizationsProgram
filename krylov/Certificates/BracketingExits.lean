import krylov.Numerics.HalfCertifiedBounds
import krylov.Certificates.EndpointCertifiedBounds
import krylov.LotkaVolterra.ExitSide
import krylov.LotkaVolterra.EndpointOrbitClassification

/-!
Article: main_krylov, apC:prop:digits, the four actual bracketing trajectories.
Exact global differential barriers certify the initial sides. The already
proved complete LV exit classification then constructs the four original,
positive trajectories. This avoids trusting a floating-point time history;
all contacts and the whole intervening solution segments are mathematical
consequences of the certified sides. Source: differential comparison and
finite first-exit classification proved in the LotkaVolterra modules.
-/
namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra

/-- The lower rational half-gamma endpoint reaches the diagonal boundary
of the actual bounded phase region, staying strictly inside beforehand. -/
theorem half_lower_bracketing_exit (G : SubcriticalGraph (1 / 2)) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = ((176535 / 100000 : ℝ), 1) ∧ ∃ T > 0,
      IsSolutionOn (1 / 2) α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, α t ∈ lowerRegion (1 / 2)) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧ (α T).2 = (α T).1 + 1 := by
  have hs := G.half_certified_five_digit_bounds
  obtain ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, hlow, _⟩ :=
    exists_lower_classified_exit (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) G
      (by norm_num [saddleS] : (176535 / 100000 : ℝ) ∈ Ioo 0 (saddleS (1 / 2)))
      (ne_of_lt hs.1)
  exact ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, hlow hs.1⟩

/-- The upper rational half-gamma endpoint reaches the saddle-height boundary
of the actual bounded phase region, staying strictly inside beforehand. -/
theorem half_upper_bracketing_exit (G : SubcriticalGraph (1 / 2)) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = ((176536 / 100000 : ℝ), 1) ∧ ∃ T > 0,
      IsSolutionOn (1 / 2) α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, α t ∈ lowerRegion (1 / 2)) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧ (α T).1 = 3 := by
  have hs := G.half_certified_five_digit_bounds
  obtain ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, _, hhi⟩ :=
    exists_lower_classified_exit (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) G
      (by norm_num [saddleS] : (176536 / 100000 : ℝ) ∈ Ioo 0 (saddleS (1 / 2)))
      (ne_of_gt hs.2)
  refine ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, ?_⟩
  have hh := hhi hs.2
  norm_num [saddleS] at hh
  exact hh

/-- Article: Proposition D.14 [apC:prop:digits]. The lower endpoint of the
printed crossing bracket exits through `U = s + 1`. The stronger rational
barrier bounds, rather than their five-digit relaxation, select this trajectory. -/
theorem half_lower_crossing_bracket_exit (G : SubcriticalGraph (1 / 2)) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = ((1765356 / 1000000 : ℝ), 1) ∧ ∃ T > 0,
      IsSolutionOn (1 / 2) α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, α t ∈ lowerRegion (1 / 2)) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧ (α T).2 = (α T).1 + 1 := by
  have hs := G.half_certified_crossing_bounds
  obtain ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, hlow, _⟩ :=
    exists_lower_classified_exit (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) G
      (by norm_num [saddleS] : (1765356 / 1000000 : ℝ) ∈ Ioo 0 (saddleS (1 / 2)))
      (ne_of_lt hs.1)
  exact ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, hlow hs.1⟩

/-- Article: Proposition D.14 [apC:prop:digits]. The upper endpoint of the
printed crossing bracket exits through `s = 3`, with the whole trajectory
inside the lower phase region before its first contact. -/
theorem half_upper_crossing_bracket_exit (G : SubcriticalGraph (1 / 2)) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = ((1765358 / 1000000 : ℝ), 1) ∧ ∃ T > 0,
      IsSolutionOn (1 / 2) α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, α t ∈ lowerRegion (1 / 2)) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧ (α T).1 = 3 := by
  have hs := G.half_certified_crossing_bounds
  obtain ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, _, hhi⟩ :=
    exists_lower_classified_exit (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) G
      (by norm_num [saddleS] : (1765358 / 1000000 : ℝ) ∈ Ioo 0 (saddleS (1 / 2)))
      (ne_of_gt hs.2)
  refine ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, ?_⟩
  have hh := hhi hs.2
  norm_num [saddleS] at hh
  exact hh

/-- The lower endpoint rational belongs to the actual lower-exit orbit class. -/
theorem endpoint_lower_bracketing_exit {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    (264667 / 100000 : ℝ) ∈ endpointLowerOrbitSet := by
  rw [(endpoint_actual_orbit_sets_intervals he).1]
  exact ⟨by norm_num, (endpoint_certified_crossing_bounds he).1⟩

/-- The upper endpoint rational belongs to the actual escape-wedge orbit class. -/
theorem endpoint_upper_bracketing_exit {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    (264668 / 100000 : ℝ) ∈ endpointUpperOrbitSet := by
  rw [(endpoint_actual_orbit_sets_intervals he).2]
  exact (endpoint_certified_crossing_bounds he).2

/-- Both endpoint orbit exits are unconditional consequences for the literal
rational starting points, using the actual globally constructed graph. -/
theorem certified_endpoint_orbit_exits :
    (264667 / 100000 : ℝ) ∈ endpointLowerOrbitSet ∧
      (264668 / 100000 : ℝ) ∈ endpointUpperOrbitSet := by
  obtain ⟨e, he⟩ := exists_global_endpoint_graph_gap
  exact ⟨endpoint_lower_bracketing_exit he, endpoint_upper_bracketing_exit he⟩

end
end krylov.Certificates
