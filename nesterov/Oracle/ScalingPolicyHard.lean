import nesterov.Oracle.ScalingPolicy

/-! The actual finite oracle lower bound at arbitrary μ,L. The policy
receives exactly the original, unnormalized values and gradients. -/
namespace nesterov.Oracle.Geometric
noncomputable section

theorem finite_hard_scaled (N : ℕ) {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (A : Policy (EuclideanSpace ℝ (Fin (2*N+2)))) :
    ∃ (f : EuclideanSpace ℝ (Fin (2*N+2))→ℝ) (zstar : EuclideanSpace ℝ (Fin (2*N+2))),
      polyak.SmoothStronglyConvex μ L f ∧ gradient f zstar=0 ∧ ‖zstar‖≤1 ∧
      delta (Real.sqrt (μ/L)) N≤‖A.result (firstOrderOracle f) N-zstar‖ := by
  have hL : 0<L := hμ.trans hμL
  have hratio : 0<μ/L := div_pos hμ hL
  have hratio1 : μ/L<1 := (div_lt_one hL).mpr hμL
  have hs : 0<Real.sqrt (μ/L) := Real.sqrt_pos.mpr hratio
  have hs1 : Real.sqrt (μ/L)<1 := by
    have h := Real.sqrt_lt_sqrt hratio.le hratio1
    simpa only [Real.sqrt_one] using h
  obtain ⟨g,z,hg,hz,hn,hl⟩ := finite_hard_instance N hs hs1 (A.rescale L)
  have hclass := scaleObjective_class hL hg
  have hμeq : L*(Real.sqrt (μ/L))^2=μ := by rw [Real.sq_sqrt hratio.le];field_simp
  rw [hμeq] at hclass
  refine ⟨scaleObjective L g,z,hclass,?_,hn,?_⟩
  · rw [scaleObjective_gradient hg.differentiable,hz,smul_zero]
  · rwa [A.rescale_result_actual hg.differentiable] at hl

end
end nesterov.Oracle.Geometric
