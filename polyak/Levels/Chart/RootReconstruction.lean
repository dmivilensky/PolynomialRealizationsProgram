import polyak.Levels.Chart.RealRoots

/-! Algebraic recovery from a strictly positive quadratic discriminant. -/
noncomputable section
namespace polyak.Levels.Chart

 theorem leftRoot_lt_rightRoot (C : Coefficients) (hc : C.c2<0)
    (hΔ : 0<gapDiscriminant C) : leftRoot C<rightRoot C := by
  unfold leftRoot rightRoot
  apply (div_lt_div_iff_of_pos_right (by linarith : 0< -2*C.c2)).mpr
  linarith [Real.sqrt_pos.mpr hΔ]

 theorem reconstruct_gapPolynomial (C : Coefficients) (hc : C.c2≠0)
    (hΔ : 0≤gapDiscriminant C) :
    C=gapPolynomial (-C.c2) (leftRoot C) (rightRoot C) := by
  have hs := Real.sq_sqrt hΔ
  apply Coefficients.ext
  · dsimp [gapPolynomial,leftRoot,rightRoot]
    field_simp
    dsimp [gapDiscriminant] at hs ⊢
    nlinarith [hs]
  · dsimp [gapPolynomial,leftRoot,rightRoot]
    field_simp
    ring
  · dsimp [gapPolynomial]
    ring

end polyak.Levels.Chart
