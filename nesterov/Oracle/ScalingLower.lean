import nesterov.Oracle.ScalingPolicyHard
import nesterov.Oracle.ScalingEnvelope
import nesterov.Robust.Scaling

/-! The unrestricted first-order optimum on the original F_{μ,L} class,
with exact oracle transport and actual scaled TMM attainment. -/
namespace nesterov.Oracle
noncomputable section

theorem first_order_literal_rate_lower_at (A : Algorithm) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) :
    ENNReal.ofReal (1-Real.sqrt (μ/L))≤literalRateAt A μ L := by
  have hL : 0<L := hμ.trans hμL
  have hq : 0<μ/L := div_pos hμ hL
  have hq1 : μ/L<1 := (div_lt_one hL).mpr hμL
  have hs : 0<Real.sqrt (μ/L) := Real.sqrt_pos.mpr hq
  have hs1 : Real.sqrt (μ/L)<1 := by
    have h := Real.sqrt_lt_sqrt hq.le hq1
    simpa only [Real.sqrt_one] using h
  have hρ : 0<1-Real.sqrt (μ/L) := sub_pos.mpr hs1
  have hC : 0<Real.sqrt (1-(1-Real.sqrt (μ/L))^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  apply literalRateAt_ge_of_hard_instances A hC hρ
  intro N
  obtain ⟨f,z,hf,hz,hn,hl⟩ := Geometric.finite_hard_scaled N hμ hμL (A N (2*N+2))
  exact ⟨2*N+2,f,z,⟨hf,hz,hn⟩,hl⟩

def tmmAlgorithmAt (μ L : ℝ) (hμ : 0<μ) (hμL : μ<L) : Algorithm :=
  let D := Robust.tmmDesign (L/μ) ((one_lt_div hμ).mpr hμL)
  momentumAlgorithm D.beta D.tau (D.step/L)

theorem tmm_oracle_rate_at (μ L : ℝ) (hμ : 0<μ) (hμL : μ<L) :
    literalRateAt (tmmAlgorithmAt μ L hμ hμL) μ L=ENNReal.ofReal (1-Real.sqrt (μ/L)) := by
  have hL : 0<L := hμ.trans hμL
  let D := Robust.tmmDesign (L/μ) ((one_lt_div hμ).mpr hμL)
  have hμeq : L/D.kappa=μ := by
    change L/(L/μ)=μ
    field_simp
  have hρ : D.rho=1-Real.sqrt (μ/L) := by
    change 1-1/Real.sqrt (L/μ)=1-Real.sqrt (μ/L)
    have he : μ/L=1/(L/μ) := by field_simp
    rw [he,Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
  have hfull := (D.scaled_exact_rates hL).1
  rw [hμeq] at hfull
  have hu := momentum_literalRateAt_le (D.scaledTuning hL) hμ hμL
  change literalRateAt (momentumAlgorithm D.beta D.tau (D.step/L)) μ L≤
    ENNReal.ofReal (Momentum.momentumRate D.beta D.tau (D.step/L)
      (div_pos D.step_pos hL).ne' μ L) at hu
  rw [hfull,hρ] at hu
  exact le_antisymm hu (first_order_literal_rate_lower_at _ hμ hμL)

theorem tmm_oracle_optimal_at (μ L : ℝ) (hμ : 0<μ) (hμL : μ<L) (A : Algorithm) :
    literalRateAt (tmmAlgorithmAt μ L hμ hμL) μ L≤literalRateAt A μ L := by
  rw [tmm_oracle_rate_at μ L hμ hμL]
  exact first_order_literal_rate_lower_at A hμ hμL

end
end nesterov.Oracle
