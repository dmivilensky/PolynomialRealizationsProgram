import polyak.FareyPlateau.Domain.Recovery

/-! The polynomial coordinates really lie on the tongue edge, with phase
exactly π/k. This is independent of the four gap inequalities. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set

theorem source_edge_phase (q : Tuning) {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    q.angle (Regions.rationalAngle j k)=Real.pi/k := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hk⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hx : q.Xi (Chart.rationalCosine j k)=Chart.rationalHeight j k := by
    rw [←Chart.eval_coefficients,he,edgeCoefficients_center]
  have hle := (Regions.angle_le_iff_Xi q hω hγ).mpr hx.ge
  apply le_antisymm hle
  by_contra hbad
  have hlt : q.angle (Regions.rationalAngle j k)<Real.pi/k := lt_of_not_ge hbad
  have hcot := (cot_strictAnti hγ (q.angle_mem hω)).mpr hlt
  rw [q.cot_angle hω] at hcot
  change Real.cos (Real.pi/k)/Real.sin (Real.pi/k)<
    q.Xi (Chart.rationalCosine j k)/Real.sin (Regions.rationalAngle j k) at hcot
  rw [hx] at hcot
  unfold Chart.rationalHeight at hcot
  rw [mul_div_cancel_right₀ _ hs.ne'] at hcot
  exact lt_irrefl _ hcot

end polyak.FareyPlateau
