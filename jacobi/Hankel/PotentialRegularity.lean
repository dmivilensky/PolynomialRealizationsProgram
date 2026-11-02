import jacobi.Hankel.Potential

/-!
Article: jacobi, Lemma E.1.
Use: the actual outgoing Fourier tails satisfy the measurability premise of the improper FTC.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The original truncated inverse-square potential is genuinely measurable.
Use: the actual outgoing Fourier tails satisfy the measurability premise of the improper FTC.
Article: jacobi, Lemma E.1.
Proof: the original integer power equals the square of the inverse, a measurable real function; its actual open-ray indicator is measurable. -/
theorem inverseSquare_measurable (R : ℝ) : Measurable (inverseSquare R) := by
  unfold inverseSquare
  have he (x : ℝ) : x^(-2:ℝ)=x⁻¹^2 := by
    simpa only [Real.rpow_two] using Real.rpow_neg_eq_inv_rpow x 2
  simp_rw [he]
  exact (measurable_inv.pow_const 2).indicator measurableSet_Ioi

/-- The original inverse-square potential equals its true rational value at every point above the cutoff.
Use: the genuine outgoing amplitude ODE has exactly the original Bessel Liouville coefficient.
Article: jacobi, Lemma E.1.
Proof: evaluate the actual open-ray indicator and the community integer real-power identity. -/
theorem inverseSquare_eq {R x : ℝ} (hx : R<x) : inverseSquare R x=1/x^2 := by
  rw [inverseSquare,indicator_of_mem (show x∈Ioi R from hx),
    Real.rpow_neg_eq_inv_rpow]
  simp only [Real.rpow_two,inv_pow,one_div]

/-- The original truncated inverse-square potential is continuous at every point on its genuine positive outgoing ray.
Use: all spatial derivatives of the true Jost amplitude have their local FTC continuity premises discharged.
Article: jacobi, Lemma E.1.
Proof: on an actual neighborhood above the fixed cutoff the source equals 1/x^2; the original spatial point is nonzero by positivity of that cutoff. -/
theorem inverseSquare_continuousAt {R x : ℝ} (hR : 0<R) (hx : R<x) :
    ContinuousAt (inverseSquare R) x := by
  have he : inverseSquare R=ᶠ[𝓝 x] (fun y : ℝ => 1/y^2) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact inverseSquare_eq hy
  exact ((continuousAt_const.div (continuousAt_id.pow 2)
    (pow_ne_zero 2 (hR.trans hx).ne'))).congr he.symm

end
end jacobi.Hankel
