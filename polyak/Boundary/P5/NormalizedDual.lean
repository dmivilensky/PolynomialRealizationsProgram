import polyak.Boundary.P5.DualReal
import polyak.Boundary.P2.Weights

/-!
Article: the P5 dual simplex and its exact normalized symbol.
Use: positivity of the true source polynomial is transported to the universal
primal–dual optimality theorem, including its numerical normalization.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Polynomial

/-- Article: the selected upper lags {2,3,5} with their actual simplex weights. -/
def weights235 (w₂ w₃ : ℝ) (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) : DualWeights where
  lags := {2,3,5}
  positive_lag n hn := by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega
  weight n := if n=2 then w₂ else if n=3 then w₃ else 1-w₂-w₃
  nonneg n hn := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num <;> linarith
  sum_one := by norm_num

/-- Article: the exact finite sum defining the actual central dual symbol. -/
theorem dualSymbol_weights235 (w₂ w₃ : ℝ) (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃)
    (u G c : ℝ) :
    dualSymbol (weights235 w₂ w₃ h₂ h₃ h₅) u G c=
      normalizedLower u G 1 c+w₂*normalizedUpper u G 2 c+
        w₃*normalizedUpper u G 3 c+(1-w₂-w₃)*normalizedUpper u G 5 c := by
  norm_num [dualSymbol,weights235,Finset.sum_insert]
  ring

/-- Article: the normalized upper lag-five functional in its actual real source formula. -/
theorem normalizedUpper_five (u G c : ℝ) :
    normalizedUpper u G 5 c=
      ((1-c^2-u^2)*(16*G^5-20*G^3+5*G-(16*c^5-20*c^3+5*c))+
        2*u*(1-c^2)*(16*c^4-12*c^2+1))/(16*G^4-12*G^2+1) := by
  rw [normalizedUpper,chebT_five,chebT_five]
  norm_num [lagDenominator,lagB,g,chebU_four]

/-- Article: the source common denominator is strictly positive for G≥1. -/
theorem commonDenominator_pos {G : ℝ} (hG : 1≤G) :
    0<G*(4*G^2-1)*(16*G^4-12*G^2+1) := by
  have h2 := lagDenominator_pos hG 3 (by omega)
  have h4 := lagDenominator_pos hG 5 (by omega)
  norm_num [lagDenominator,chebU,Polynomial.Chebyshev.U_two] at h2
  rw [lagDenominator,chebU_four] at h4
  exact mul_pos (mul_pos (by linarith) (by linarith : 0<4*G^2-1)) h4

private theorem clear_three_normalized {G U V : ℝ} (hG : G≠0) (hU : U≠0) (hV : V≠0)
    (L N₂ N₃ N₅ w₂ w₃ : ℝ) :
    G*U*V*(L+w₂*(N₂/(2*G))+w₃*(N₃/U)+(1-w₂-w₃)*(N₅/V))=
      G*U*V*L+(w₂*(U*V*(1/2)))*N₂+(w₃*(G*V))*N₃+
        ((1-w₂-w₃)*(G*U))*N₅ := by
  field_simp [hG,hU,hV]

/-- Article: exact normalization of the actual scalar central dual, before simplex assumptions. -/
theorem dualClosed_normalization {G : ℝ} (hG : 1≤G) (u w₂ w₃ c : ℝ) :
    G*(4*G^2-1)*(16*G^4-12*G^2+1)*
      (normalizedLower u G 1 c+w₂*normalizedUpper u G 2 c+
        w₃*normalizedUpper u G 3 c+(1-w₂-w₃)*normalizedUpper u G 5 c)=
      -(G-c)*(dualClosed u G w₂ w₃).eval c := by
  have h0 : G≠0 := by linarith
  have h2 : 4*G^2-1≠0 := by nlinarith
  have h4 : 16*G^4-12*G^2+1≠0 := by
    have hp := commonDenominator_pos hG
    intro hz
    rw [hz,mul_zero] at hp
    exact (lt_irrefl 0) hp
  rw [normalizedLower_one,normalizedUpper_two,normalizedUpper_three,normalizedUpper_five]
  rw [clear_three_normalized h0 h2 h4]
  simp only [dualClosed,eval_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat,eval_one]
  unfold g
  ring

/-- Article: the source polynomial and the actual normalized dual agree with their positive scale. -/
theorem dualPolynomial_eq_source {G : ℝ} (hG : 1<G) (u w₂ w₃ : ℝ)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) (c : Frequency) :
    (dualPolynomial (weights235 w₂ w₃ h₂ h₃ h₅) u G).eval (c : ℝ)=
      (dualClosed u G w₂ w₃).eval (c : ℝ)/
        (G*(4*G^2-1)*(16*G^4-12*G^2+1)) := by
  have he := dualClosed_normalization hG.le u w₂ w₃ c
  rw [← dualSymbol_weights235 w₂ w₃ h₂ h₃ h₅,dualPolynomial_factor _ _ hG.le] at he
  have hg : G-(c : ℝ)≠0 := by linarith [c.property.2]
  have hd := (commonDenominator_pos hG.le).ne'
  apply (eq_div_iff hd).mpr
  apply mul_left_cancel₀ (neg_ne_zero.mpr hg)
  nlinarith only [he]

/-- Article: the source normalization is a true polynomial identity, including G=c=1. -/
theorem dualPolynomial_source_polynomial {G : ℝ} (hG : 1≤G) (u w₂ w₃ : ℝ)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) :
    Polynomial.C (G*(4*G^2-1)*(16*G^4-12*G^2+1))*
      dualPolynomial (weights235 w₂ w₃ h₂ h₃ h₅) u G=dualClosed u G w₂ w₃ := by
  apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero G)
  apply Polynomial.funext
  intro c
  have he := dualClosed_normalization hG u w₂ w₃ c
  rw [← dualSymbol_weights235 w₂ w₃ h₂ h₃ h₅,dualPolynomial_factor _ _ hG] at he
  simp only [eval_mul,eval_sub,eval_X,eval_C]
  linear_combination he

/-- Article: exact normalized source evaluation on every frequency, including the critical endpoints. -/
theorem dualPolynomial_eq_source_of_le {G : ℝ} (hG : 1≤G) (u w₂ w₃ : ℝ)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) (c : ℝ) :
    (dualPolynomial (weights235 w₂ w₃ h₂ h₃ h₅) u G).eval c=
      (dualClosed u G w₂ w₃).eval c/(G*(4*G^2-1)*(16*G^4-12*G^2+1)) := by
  have he := congrArg (fun P : ℝ[X] => P.eval c)
    (dualPolynomial_source_polynomial hG u w₂ w₃ h₂ h₃ h₅)
  simp only [eval_mul,eval_C] at he
  apply (eq_div_iff (commonDenominator_pos hG).ne').mpr
  linear_combination he

end polyak.Boundary.P5
