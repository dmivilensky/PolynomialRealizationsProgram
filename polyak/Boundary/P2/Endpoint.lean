import polyak.Certificates.P2Endpoints
import polyak.Boundary.P2.Physical

/-! Article: (p2endpoint), exact coordinate agreement with the spiral at G₁. -/
namespace polyak.Boundary.P2
noncomputable section

/-- Article: the P₂ twist equals the spiral twist at the cubic endpoint. -/
theorem u_zeta1 : u zeta1=1-1/(2*Boundary.G1) := by
  have h:=touching_spiral (rMinus_pos zeta1_mem).ne'
  rw [endpointCubic_zeta1,zero_pow (by omega),mul_zero,zero_div,G_zeta1] at h
  linarith

/-- Article: the negative root agrees with the spiral frequency. -/
theorem x_zeta1 : x zeta1= -1/(2*Boundary.G1) := by
  have hc:=lowerCandidate_at_zeta1
  rw [atomPolynomial_factor zeta1_mem,mul_eq_zero] at hc
  have hp : (0 : ℝ)<2*G zeta1 := by have h:=one_lt_G zeta1_mem; linarith
  have hn : -1/(2*G zeta1)<0 := div_neg_of_neg_of_pos (by norm_num) hp
  rcases hc with hc|hc
  · rw [sub_eq_zero] at hc
    rw [G_zeta1] at hc
    exact hc.symm
  · have hr:=roots_order zeta1_mem
    rw [sub_eq_zero] at hc
    linarith [hr.2.1]

/-- Article: the positive zero agrees with the unused second endpoint frequency. -/
theorem y_zeta1 : y zeta1=(2*Boundary.G1-1)/(4*Boundary.G1) := by
  have hc:=upperCandidate_at_zeta1
  rw [atomPolynomial_factor zeta1_mem,mul_eq_zero] at hc
  have hg:=one_lt_G zeta1_mem
  have hp : 0<(2*G zeta1-1)/(4*G zeta1) := div_pos (by linarith) (by linarith)
  rcases hc with hc|hc
  · have hr:=roots_order zeta1_mem
    rw [sub_eq_zero] at hc
    linarith [hr.1]
  · rw [sub_eq_zero] at hc
    rw [G_zeta1] at hc
    exact hc.symm

/-- Article: the second atom has zero mass exactly at the spiral endpoint. -/
theorem p_zeta1 : p zeta1=0 := (p_eq_zero_iff zeta1_mem le_rfl).mpr rfl

/-- Article: the affine minimizer agrees with the spiral value. -/
theorem d_zeta1 : d zeta1=(2*Boundary.G1-1)*(Boundary.G1^2-1)/(2*Boundary.G1^3) := by
  have h:=valueEndpoint_at_zeta1
  rw [G_zeta1] at h
  linarith

/-- Article: the dual weight agrees with the spiral weight. -/
theorem W_zeta1 : W zeta1=Boundary.spiralWeight Boundary.G1 := by
  have h:=weightEndpoint_at_zeta1
  rw [G_zeta1] at h
  linarith

/-- Article: P₂ and the spiral have exactly the same tangent in the physical G coordinate. -/
theorem slope_zeta1 : slope zeta1=1/(2*Boundary.G1^2) := by
  have h:=derivativeEndpoint_at_zeta1
  rw [G_zeta1] at h
  linarith

/-- Article: the rational P₂ curve lies above the spiral everywhere on the verified interval. -/
theorem spiral_le {z : ℝ} (hz : z∈parameterInterval) : 1-1/(2*G z) ≤ u z := by
  have h:=touching_spiral (rMinus_pos hz).ne'
  have hd : 0<rMinus z*rPlus z*qMinus z*qPlus z := by
    exact mul_pos (mul_pos (mul_pos (rMinus_pos hz) (rPlus_pos z)) (qMinus_pos z)) (qPlus_pos z)
  have hp : 0 ≤ 8*endpointCubic z^2/(rMinus z*rPlus z*qMinus z*qPlus z) :=
    div_nonneg (by positivity) hd.le
  linarith

end
end polyak.Boundary.P2
