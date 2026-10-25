import polyak.CertifiedExamples.Exact313.Contacts
import polyak.CertifiedExamples.Exact313.Factor

/-! Exact polynomial reduction of the fixed-frequency double contacts. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag

abbrev contactPolynomial : ℝ→ℝ := Factor.quintic rStar CStar.c2 CStar.c1 CStar.c0

theorem contactPolynomial_identity (c : ℝ) :
    contactPolynomial c=CStar.eval c*denominator rStar c-numerator rStar c := by
  dsimp [contactPolynomial,Factor.quintic,Chart.Coefficients.eval,denominator,numerator]
  ring

theorem contactPolynomial_hasDerivAt (c : ℝ) : HasDerivAt contactPolynomial
    ((CStar.c1+2*CStar.c2*c)*denominator rStar c+
      CStar.eval c*denominatorD rStar c-numeratorD rStar c) c := by
  have h := ((coefficients_hasDerivAt CStar c).mul (denominator_hasDerivAt rStar c)).sub
    (numerator_hasDerivAt rStar c)
  have he : contactPolynomial=(fun c=>CStar.eval c*denominator rStar c-numerator rStar c) :=
    funext contactPolynomial_identity
  change HasDerivAt (fun c=>CStar.eval c*denominator rStar c-numerator rStar c) _ c at h
  rwa [←he] at h

theorem contactPolynomial_value {c : ℝ} (hc : c∈Set.Icc (-1:ℝ) 1)
    (hv : CStar.eval c=Psi 4 rStar c) : contactPolynomial c=0 := by
  rw [contactPolynomial_identity,hv,psi_four]
  field_simp [(denominator_pos scalarRoot_positive.le hc).ne']
  ring

theorem contactPolynomial_slope {c : ℝ} (hc : c∈Set.Icc (-1:ℝ) 1)
    (hv : CStar.eval c=Psi 4 rStar c)
    (hd : deriv CStar.eval c=deriv (Psi 4 rStar) c) : deriv contactPolynomial c=0 := by
  rw [(contactPolynomial_hasDerivAt c).deriv,←(coefficients_hasDerivAt CStar c).deriv,
    hd,psi_four_deriv (denominator_pos scalarRoot_positive.le hc).ne',hv,psi_four]
  dsimp [derivativeNumerator]
  field_simp [(denominator_pos scalarRoot_positive.le hc).ne']
  ring

theorem contactPolynomial_factor (c : ℝ) :
    contactPolynomial c=(c-c₁)^2*(c-c₂)^2*
      (8*rStar*CStar.c2*c+8*rStar*(CStar.c1+CStar.c2+1+2*CStar.c2*(c₁+c₂))) := by
  apply Factor.quintic_factor
  · exact c₁_lt_c₂.ne
  · exact contactPolynomial_value ⟨c₁_mem.1.le,c₁_mem.2.le⟩
      (hermiteQuadratic_first 4 rStar c₁ c₂).1
  · exact contactPolynomial_value ⟨c₂_mem.1.le,c₂_mem.2.le⟩
      (hermiteQuadratic_second_value 4 rStar c₁_lt_c₂.ne)
  · exact contactPolynomial_slope ⟨c₁_mem.1.le,c₁_mem.2.le⟩
      (hermiteQuadratic_first 4 rStar c₁ c₂).1 contact_slopes_first
  · exact contactPolynomial_slope ⟨c₂_mem.1.le,c₂_mem.2.le⟩
      (hermiteQuadratic_second_value 4 rStar c₁_lt_c₂.ne) contact_slopes_second

def contactLine (c : ℝ) : ℝ :=
  8*rStar*CStar.c2*c+8*rStar*(CStar.c1+CStar.c2+1+2*CStar.c2*(c₁+c₂))

theorem contactLine_negative {c : ℝ} (hc : -1≤c) : contactLine c<0 := by
  have ha := coefficients_mem_domain.1
  have h := mul_nonpos_of_nonpos_of_nonneg ha.le (show 0≤c+1 by linarith)
  have hsum : CStar.c2*(c+1)+(CStar.c1+1+2*CStar.c2*(c₁+c₂))<0 :=
    add_neg_of_nonpos_of_neg h quotient_bound
  have hp : 0<8*rStar := by positivity [scalarRoot_positive]
  have hn := mul_neg_of_pos_of_neg hp hsum
  convert hn using 1
  dsimp [contactLine]
  ring

theorem contactPolynomial_negative {c : ℝ} (hc : -1≤c) (h₁ : c≠c₁) (h₂ : c≠c₂) :
    contactPolynomial c<0 := by
  rw [contactPolynomial_factor]
  exact mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr h₂))) (contactLine_negative hc)

end polyak.CertifiedExamples.Exact313
