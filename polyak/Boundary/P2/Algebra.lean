import polyak.Boundary.P2.Weights

/-!
Article: Lemmas p2curve and p2ids, exact rational identities.
Use: identities refer to the original mathematical sources, with every necessary
nonzero denominator explicit. The arc sign theorems discharge these hypotheses.
-/

namespace polyak.Boundary.P2
noncomputable section

/-- Article: both q factors are positive for every real parameter. -/
theorem qMinus_pos (z : ℝ) : 0 < qMinus z := by unfold qMinus; nlinarith [sq_nonneg (z-1)]

/-- Article: the positive q₊ factor. -/
theorem qPlus_pos (z : ℝ) : 0 < qPlus z := by unfold qPlus; nlinarith [sq_nonneg (z+1)]

/-- Article: r₊ never vanishes. -/
theorem rPlus_pos (z : ℝ) : 0 < rPlus z := by unfold rPlus; positivity

/-- Article: exact sum-of-squares identity for the dual denominator. -/
theorem K6_sum_squares (z : ℝ) : K6 z=z^4*(z-2)^2+8*(z-1)^2 := by unfold K6; ring

/-- Article: the two squared terms cannot vanish simultaneously. -/
theorem K6_pos (z : ℝ) : 0 < K6 z := by
  rw [K6_sum_squares]
  by_cases h : z=1
  · subst z
    norm_num
  · have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    have hq : 0 ≤ z^4*(z-2)^2 := by positivity
    linarith

/-- Article: the rational P₂ parametrization lies on its implicit curve. -/
theorem curve_identity {z : ℝ} (hz : z≠0) (hr : rMinus z≠0) (hp : rPlus z≠0) :
    curvePolynomial (G z) (u z)=0 := by
  have hf : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
  unfold curvePolynomial G u
  rw [hf]
  unfold qMinus rMinus rPlus at *
  field_simp
  ring

/-- Article: the exact ratio u/G in Lemma p2curve. -/
theorem twist_ratio {z : ℝ} (hz : z≠0) (hr : rMinus z≠0) :
    u z/G z=8*z*qMinus z/(rPlus z*qPlus z) := by
  have hf : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
  have hf' : z^4+4=qMinus z*qPlus z := by unfold qMinus qPlus; ring
  have hqm := (qMinus_pos z).ne'
  have hqp := (qPlus_pos z).ne'
  have hrp := (rPlus_pos z).ne'
  unfold G u
  rw [hf,hf']
  field_simp

/-- Article: exact complement of the dual weight. -/
theorem one_sub_weight (z : ℝ) :
    1-W z=eMinus z^2*ePlus z^2/(8*rPlus z*K6 z) := by
  have hk := (K6_pos z).ne'
  have hrp := (rPlus_pos z).ne'
  unfold W
  field_simp
  unfold qMinus qPlus rPlus eMinus ePlus K6
  ring

/-- Article: the rational curve touches the spiral at the cubic endpoint. -/
theorem touching_spiral {z : ℝ} (hr : rMinus z≠0) :
    u z-1+1/(2*G z)=8*endpointCubic z^2/(rMinus z*rPlus z*qMinus z*qPlus z) := by
  have hf : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
  have hf' : z^4+4=qMinus z*qPlus z := by unfold qMinus qPlus; ring
  have hqm := (qMinus_pos z).ne'
  have hqp := (qPlus_pos z).ne'
  have hrp := (rPlus_pos z).ne'
  unfold G u
  rw [hf,hf']
  field_simp
  unfold qMinus qPlus rMinus rPlus endpointCubic
  ring

end
end polyak.Boundary.P2
