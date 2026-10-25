import polyak.Spiral.Factor
import polyak.Threshold.Parameters

/-!
Article: Appendix B, the unique spiral root crosses one exactly at q=φ⁻¹.
Use: exact monotonicity and signs before the full spectral classification.
-/

noncomputable section

open scoped goldenRatio

namespace polyak.Spiral

/-- Article: F(1,q)=2(1-q-q²). -/
theorem spiralPolynomial_one (q : ℝ) : spiralPolynomial 1 q = 2*(1-q-q^2) := by
  unfold spiralPolynomial
  ring

/-- Article: exact threshold factorization of the quadratic sign. -/
theorem threshold_quadratic_factor (q : ℝ) :
    1-q-q^2 = (Threshold.criticalQ-q)*(q+Threshold.criticalQ+1) := by
  nlinarith [Threshold.criticalQ_sq_add]

/-- Article: the spiral factor is below one below q_c. -/
theorem factor_lt_one {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hcritical : q < Threshold.criticalQ) : factor q < 1 := by
  have hsign : 0 < spiralPolynomial 1 q := by
    rw [spiralPolynomial_one, threshold_quadratic_factor]
    have hc := Threshold.criticalQ_pos
    positivity
  have hmono := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
  by_contra hh
  have h := hmono hq1.le (q_lt_factor hq hq1).le (le_of_not_gt hh)
  dsimp only at h
  rw [(factor_spec hq hq1).2] at h
  linarith

/-- Article: the spiral factor equals one at q_c. -/
theorem factor_critical : factor Threshold.criticalQ = 1 := by
  have hq := Threshold.criticalQ_pos
  have hq1 := Threshold.criticalQ_lt_one
  have hu := (Classical.choose_spec (existsUnique_spiral_root hq hq1)).2
  have hroot : spiralPolynomial 1 Threshold.criticalQ = 0 := by
    rw [spiralPolynomial_one]
    nlinarith [Threshold.criticalQ_sq_add]
  have h₁ := hu 1 ⟨by norm_num,hroot⟩
  have h₂ := hu (factor Threshold.criticalQ) (factor_spec hq hq1)
  exact h₂.trans h₁.symm

/-- Article: the spiral factor exceeds one above q_c. -/
theorem one_lt_factor {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hcritical : Threshold.criticalQ < q) : 1 < factor q := by
  have hsign : spiralPolynomial 1 q < 0 := by
    rw [spiralPolynomial_one, threshold_quadratic_factor]
    have hc := Threshold.criticalQ_pos
    have hm : (Threshold.criticalQ-q)*(q+Threshold.criticalQ+1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  have hmono := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
  by_contra hh
  have h := hmono (q_lt_factor hq hq1).le hq1.le (le_of_not_gt hh)
  dsimp only at h
  rw [(factor_spec hq hq1).2] at h
  linarith

/-- Article: the exact equality case of the spiral threshold. -/
theorem factor_eq_one_iff {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    factor q = 1 ↔ q = Threshold.criticalQ := by
  constructor
  · intro hh
    have h := (factor_spec hq hq1).2
    rw [hh,spiralPolynomial_one,threshold_quadratic_factor] at h
    have hc := Threshold.criticalQ_pos
    have hp : 0 < q+Threshold.criticalQ+1 := by positivity
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num)) with h | h
    · linarith
    · exact (hp.ne' h).elim
  · rintro rfl
    exact factor_critical

/-- Article: F decreases strictly as q increases. -/
theorem spiralPolynomial_parameter_lt {ρ q₁ q₂ : ℝ} (hρ : 0 < ρ)
    (hq₁ : 0 < q₁) (hqq : q₁ < q₂) :
    spiralPolynomial ρ q₂ < spiralPolynomial ρ q₁ := by
  have hs : 0 < ρ^2-ρ+1 := by nlinarith [sq_nonneg (ρ-1/2)]
  have hq₂ : 0 < q₂ := hq₁.trans hqq
  have h₁ : 0 < 2*ρ*(q₂-q₁)*(ρ^2-ρ+1) := by positivity
  have h₂ : 0 < (q₂-q₁)*(q₂+q₁)*(ρ^2+1) := by positivity
  unfold spiralPolynomial
  nlinarith [h₁,h₂]

/-- Article: the positive spiral root is strictly increasing in q. -/
theorem factor_strictMonoOn : StrictMonoOn factor (Set.Ioo (0 : ℝ) 1) := by
  intro q₁ hq₁ q₂ hq₂ hqq
  have hsign := spiralPolynomial_parameter_lt (factor_spec hq₁.1 hq₁.2).1 hq₁.1 hqq
  rw [(factor_spec hq₁.1 hq₁.2).2] at hsign
  by_contra hh
  have hf₂ := q_lt_factor hq₂.1 hq₂.2
  have hf₁ : q₂ ≤ factor q₁ := hf₂.le.trans (le_of_not_gt hh)
  have hm := (spiralPolynomial_strictMonoOn hq₂.1 hq₂.2).monotoneOn
    hf₂.le hf₁ (le_of_not_gt hh)
  rw [(factor_spec hq₂.1 hq₂.2).2] at hm
  linarith

/-- Article: the original condition-number spiral threshold is exactly κ_c. -/
theorem condition_factor_lt_one {κ : ℝ} (hκ : 1 < κ) (hcrit : κ < Threshold.criticalKappa) :
    factor (Dynamics.conditionQ κ) < 1 := by
  have hq := Threshold.conditionQ_mem hκ
  exact factor_lt_one hq.1 hq.2 ((Threshold.conditionQ_lt_critical_iff hκ).mpr hcrit)

/-- Article: supercritical spiral divergence factor in the original condition number. -/
theorem one_lt_condition_factor {κ : ℝ} (hκ : 1 < κ) (hcrit : Threshold.criticalKappa < κ) :
    1 < factor (Dynamics.conditionQ κ) := by
  have hq := Threshold.conditionQ_mem hκ
  exact one_lt_factor hq.1 hq.2 ((Threshold.critical_lt_conditionQ_iff hκ).mpr hcrit)

end polyak.Spiral
