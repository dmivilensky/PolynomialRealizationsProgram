import polyak.GapEdges.Junction.SourceCurvature
import polyak.FareyPlateau.Edge.Adjacent

/-! Above the half-period strip the genuine adjacent symbol has positive
curvature. The two fixed lags 1-k and 1 are not used outside their strip. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set

theorem junction_phase_curvature (q : Tuning) {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    Real.sin c*deriv^[2] (Geometry.shiftedAngle q 0) (2*c)=
      2*junctionG a (Real.cos (2*c)) t₂ c*
        (junctionG a (Real.cos (2*c)) t₂ c-1)*Real.cos c+
      (a*Real.sin c^2)*(2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)/(2*Real.cos c) := by
  obtain ⟨_,hf,hs⟩ := junction_angle_jets q hc hXi
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hd : deriv (Geometry.shiftedAngle q 0) (2*c)=
      1/2-junctionG a (Real.cos (2*c)) t₂ c := by
    unfold junctionG
    linarith
  rw [hs,hd]
  field_simp
  ring

theorem junction_phase_curvature_gt (q : Tuning) {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) (ht : 0≤Real.cos (2*c))
    (hd : t₂<Real.cos (2*c)) (ha : 0<a)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    2*junctionG a (Real.cos (2*c)) t₂ c*
      (junctionG a (Real.cos (2*c)) t₂ c-1)*Real.cos c <
      Real.sin c*deriv^[2] (Geometry.shiftedAngle q 0) (2*c) := by
  rw [junction_phase_curvature q hc hXi]
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have ht1 : Real.cos (2*c)<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0:ℝ)≤0 by rfl) (by linarith [hc.2] : 2*c≤Real.pi) (by linarith [hc.1])
  have hprod : Real.cos (2*c)*t₂≤Real.cos (2*c)^2 := by nlinarith
  have hnum : 0<2-Real.cos (2*c)^2-Real.cos (2*c)*t₂ := by nlinarith
  have hterm : 0<(a*Real.sin c^2)*(2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)/
      (2*Real.cos c) := by positivity
  linarith

theorem half_period_tail_positive {m g : ℝ} (hm : 4≤m) (hg : m/2<g) :
    0<2*g*(g-1)-m^2/8 := by
  have hfac : 0<(g-m/2)*(g+m/2-1) := mul_pos (by linarith) (by linarith)
  have hbase : 0<m*(3*m-8) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem adjacent_curvature_tail_positive {F m g u v t c : ℝ}
    (hm : 4≤m) (hg : m/2<g) (hc : 0<c)
    (hphase : 2*g*(g-1)*c<u*v)
    (hsecond : F=u*v-(1/2:ℝ)*c*m^2*(t-t^2)) : 0<F := by
  have hp := half_period_tail_positive hm hg
  have hvar : t-t^2≤(1/4:ℝ) := by nlinarith [sq_nonneg (t-1/2)]
  have hh : 0≤c*m^2*(1/4-(t-t^2)) := by positivity
  nlinarith

end polyak.GapEdges.Junction
