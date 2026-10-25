import polyak.Boundary.P2.Source
import polyak.Spiral.Feasibility

/-!
Article: the normalized lag-two/lag-three dual family.
Use: one exact symbol formula serves the spiral and the rational P₂ arc.
-/

namespace polyak.Boundary
noncomputable section
open Spectral

/-- Article: J={2,3}, with the actual nonnegative simplex weights W,1−W. -/
def weights23 (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : DualWeights where
  lags := {2,3}
  positive_lag n hn := by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega
  weight n := if n=2 then w else 1-w
  nonneg n hn := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> simp only [ite_true,show (3 : ℕ)≠2 by decide,ite_false]
    · exact hw0
    · exact sub_nonneg.mpr hw1
  sum_one := by norm_num

/-- Article: the first selected normalized upper functional. -/
theorem normalizedUpper_two (u G c : ℝ) :
    normalizedUpper u G 2 c=
      ((1-c^2-u^2)*(2*G^2-2*c^2)+4*u*c*(1-c^2))/(2*G) := by
  norm_num [normalizedUpper,lagDenominator,lagB,g,chebT,chebU,
    Polynomial.Chebyshev.T_two]
  ring

/-- Article: the second selected normalized upper functional. -/
theorem normalizedUpper_three (u G c : ℝ) :
    normalizedUpper u G 3 c=
      ((1-c^2-u^2)*(4*G^3-3*G-(4*c^3-3*c))+2*u*(1-c^2)*(4*c^2-1))/(4*G^2-1) := by
  rw [normalizedUpper,Spiral.chebT_three,Spiral.chebT_three]
  norm_num [lagDenominator,lagB,g,chebU,Polynomial.Chebyshev.U_two]

/-- Article: exact finite-sum form of the actual dual symbol. -/
theorem dualSymbol_weights23 (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (u G c : ℝ) :
    dualSymbol (weights23 w hw0 hw1) u G c=
      normalizedLower u G 1 c+w*normalizedUpper u G 2 c+(1-w)*normalizedUpper u G 3 c := by
  norm_num [dualSymbol,weights23,Finset.sum_insert]
  ring

/-- Article: G(4G²−1)α for J={2,3}. -/
def cubicAlpha (G w c : ℝ) : ℝ :=
  8*G^3+4*G^2*c+4*G*c^2-4*G-w*(4*G*c^2-2*G+c)

/-- Article: G(4G²−1)β for J={2,3}. -/
def quadraticBeta (G w c : ℝ) : ℝ := 4*G^2+4*G*c-w*(4*G*c+1)

/-- Article: the quartic polynomial form of the selected dual family.
Use: the only denominators are positive whenever G≥1. -/
theorem dualSymbol_weights23_factor (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {G : ℝ} (hG : 1 ≤ G) (u c : ℝ) :
    dualSymbol (weights23 w hw0 hw1) u G c=
      (G-c)*((1-c^2-u^2)*cubicAlpha G w c-2*u*(1-c^2)*quadraticBeta G w c)/
        (G*(4*G^2-1)) := by
  have h0 : G≠0 := by linarith
  have hD : 4*G^2-1≠0 := by nlinarith
  have hD' : -1+G^2*4≠0 := by nlinarith
  have hD'' : G^2*4-1≠0 := by nlinarith
  rw [dualSymbol_weights23,normalizedLower_one,normalizedUpper_two,normalizedUpper_three]
  unfold cubicAlpha quadraticBeta g
  field_simp [h0,hD,hD',hD'']
  ring

end
end polyak.Boundary
