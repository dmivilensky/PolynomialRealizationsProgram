import jacobi.Rearrangement.ReflectionOrbit

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Simultaneously polarizing two actual densities increases their exponential
kernel pairing. In particular it increases the actual second spectral moment.
The two-point inequality is proved here; convergence of polarizations to the
symmetric decreasing rearrangement remains a separate theorem.
Source: the two-point proof of the Riesz rearrangement inequality, Lieb and Loss, Analysis.
Use: the only finite algebra required for the Riesz two-point inequality.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory Real Set jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- Sorting two pairs increases their interaction when same-side interactions have larger weight.
Use: the only finite algebra required for the Riesz two-point inequality.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: split the two orders. In each mixed case the difference is
(A-B) times the product of the two nonnegative value gaps. -/
theorem sorted_pair_interaction (a b c d A B : ℝ) (hAB : B ≤ A) :
    A*(a*c+b*d)+B*(a*d+b*c) ≤
      A*(max a b*max c d+min a b*min c d)+B*(max a b*min c d+min a b*max c d) := by
  -- Equal pair orientations give equality; opposite orientations give a nonnegative triple product.
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · rw [max_eq_right hab,min_eq_left hab,max_eq_right hcd,min_eq_left hcd]
      ring_nf
      exact le_rfl
    · rw [max_eq_right hab,min_eq_left hab,max_eq_left hdc,min_eq_right hdc]
      nlinarith [mul_nonneg (sub_nonneg.mpr hAB)
        (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdc))]
  · rcases le_total c d with hcd | hdc
    · rw [max_eq_left hba,min_eq_right hba,max_eq_right hcd,min_eq_left hcd]
      nlinarith [mul_nonneg (sub_nonneg.mpr hAB)
        (mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcd))]
    · rw [max_eq_left hba,min_eq_right hba,max_eq_left hdc,min_eq_right hdc]

/-- Two points on the preferred half-line are closer than their cross-reflected pair.
Use: the exponential kernel assigns the larger coefficient to same-side interactions.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the cross distance is 2a-x-y and bounds both signs of x-y. -/
theorem reflection_distance {a x y : ℝ} (hx : x ≤ a) (hy : y ≤ a) :
    |x-y| ≤ |x-reflect a y| := by
  dsimp [reflect]
  rw [abs_of_nonpos (by linarith : x-(2*a-y) ≤ 0)]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The literal integrand of the signed second-moment pairing.
Use: reflects and compares the same product-space integrand already used by the actual spectrum.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def pairIntegrand (m q : ℝ → ℝ) (z : ℝ × ℝ) : ℝ := m z.1*q z.2*exp (-2*|z.1-z.2|)

/-- The four reflected kernel terms reduce to two interaction coefficients.
Use: identifies the geometric orbit with the finite sorted-pair inequality.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: simultaneous reflection preserves distance, and the two cross distances agree. -/
theorem pairIntegrand_orbit (a : ℝ) (m q : ℝ → ℝ) (x y : ℝ) :
    orbitFour (pairIntegrand m q) a x y =
      exp (-2*|x-y|)*(m x*q y+m (reflect a x)*q (reflect a y))+
      exp (-2*|x-reflect a y|)*(m x*q (reflect a y)+m (reflect a x)*q y) := by
  -- Reflection gives exactly two distinct distances among the four pairs.
  have hs : |reflect a x-reflect a y|=|x-y| := by
    rw [show reflect a x-reflect a y=-(x-y) by dsimp [reflect]; ring,abs_neg]
  have hc : |reflect a x-y|=|x-reflect a y| := by
    rw [show reflect a x-y=-(x-reflect a y) by dsimp [reflect]; ring,abs_neg]
  simp only [orbitFour,pairIntegrand,hs,hc]
  ring

/-- Pointwise orbit inequality for the actual exponential kernel on the preferred half-line.
Use: the global Riesz polarization comparison after reflecting arbitrary coordinates into that half-line.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use the exact orbit formula, the sorted reflected values, and the proved distance ordering. -/
theorem riesz_orbit_left (a : ℝ) (m q : ℝ → ℝ) {x y : ℝ} (hx : x ≤ a) (hy : y ≤ a) :
    orbitFour (pairIntegrand m q) a x y ≤
      orbitFour (pairIntegrand (polarize a m) (polarize a q)) a x y := by
  -- Both density pairs are sorted in the same direction, toward the same half-line.
  rw [pairIntegrand_orbit,pairIntegrand_orbit,
    (polarize_left_pair a m hx).1,(polarize_left_pair a m hx).2,
    (polarize_left_pair a q hy).1,(polarize_left_pair a q hy).2]
  have he : exp (-2*|x-reflect a y|) ≤ exp (-2*|x-y|) :=
    exp_le_exp.mpr (by linarith [reflection_distance hx hy])
  convert sorted_pair_interaction (m x) (m (reflect a x)) (q y) (q (reflect a y))
    (exp (-2*|x-y|)) (exp (-2*|x-reflect a y|)) he using 1

/-- The pointwise Riesz orbit comparison holds on the entire integration plane.
Use: licenses monotone integration without restricting or duplicating the physical domain.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflect each coordinate into the preferred half-line; its orbit is unchanged. -/
theorem riesz_orbit (a : ℝ) (m q : ℝ → ℝ) (x y : ℝ) :
    orbitFour (pairIntegrand m q) a x y ≤
      orbitFour (pairIntegrand (polarize a m) (polarize a q)) a x y := by
  -- No density monotonicity is assumed: only the reflection orbits are symmetric.
  by_cases hx : x ≤ a
  · by_cases hy : y ≤ a
    · exact riesz_orbit_left a m q hx hy
    · have hyr : reflect a y ≤ a := by dsimp [reflect]; linarith
      simpa only [orbitFour_reflect_right] using riesz_orbit_left a m q hx hyr
  · have hxr : reflect a x ≤ a := by dsimp [reflect]; linarith
    by_cases hy : y ≤ a
    · simpa only [orbitFour_reflect_left] using riesz_orbit_left a m q hxr hy
    · have hyr : reflect a y ≤ a := by dsimp [reflect]; linarith
      simpa only [orbitFour_reflect_left,orbitFour_reflect_right] using riesz_orbit_left a m q hxr hyr

/-- Simultaneous polarization increases the actual bilinear exponential-kernel pairing.
Use: the p=2 rearrangement step for two arbitrary finite-energy densities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the pointwise four-point inequality using proved absolute
integrability, identify both orbit integrals with four times the original pairing, and cancel four. -/
theorem secondPairing_polarize (m q : Density) (a : ℝ) :
    secondPairing m.value q.value ≤ secondPairing (m.polarize a).value (q.polarize a).value := by
  -- All four functions live on the same product Lebesgue space as the original spectral moment.
  have hm := second_integrand_integrable m.integrable q.integrable m.measurable q.measurable
  have hp := second_integrand_integrable (m.polarize a).integrable (q.polarize a).integrable
    (m.polarize a).measurable (q.polarize a).measurable
  have h := integral_mono (orbitFour_integrable hm a) (orbitFour_integrable hp a)
    (fun z => riesz_orbit a m.value q.value z.1 z.2)
  rw [integral_orbitFour hm a,integral_orbitFour hp a] at h
  change 4*secondPairing m.value q.value ≤
    4*secondPairing (m.polarize a).value (q.polarize a).value at h
  linarith

/-- The actual second spectral moment cannot decrease under polarization.
Use: the elementary p=2 operation in the symmetric decreasing rearrangement theorem.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the kernel square-trace identity equates the actual spectral moment with the self-pairing. -/
theorem second_polarize (m : Density) (a : ℝ) :
    observe m .second ≤ observe (m.polarize a) .second := by
  rw [← m.secondPairing_self,← (m.polarize a).secondPairing_self]
  exact secondPairing_polarize m m a

end
end jacobi.Rearrangement
