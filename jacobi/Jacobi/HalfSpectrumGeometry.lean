import jacobi.Jacobi.HalfSpectrumComparison
import jacobi.Bessel.ZeroGeometry

/-!
Article: jacobi, Proposition B.1.
The actual growing first-half zero range has uniform positive linear
angular bounds. All frequency-window premises have been discharged;
these constants depend only on the two fixed source parameters.
Use: reflection supplies both endpoint distances in Proposition B.1 (c); the extreme distances also bound the actual restoring coefficient for a uniform gap estimate.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual first-half Jacobi zero has its correct positive endpoint scale uniformly in the growing index range.
Use: reflection supplies both endpoint distances in Proposition B.1 (c); the extreme distances also bound the actual restoring coefficient for a uniform gap estimate.
Article: jacobi, Proposition B.1.
Proof: the unconditional frequency comparison makes N*theta differ from
the genuine Bessel zero by at most one half that zero at large degree.
Combine with the proved uniform positive linear Bessel zero bounds. -/
theorem firstHalf_angle_bounds {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k,2*k<n → c*(k+1:ℝ)/frequency a b n≤finiteAngleAt a b ha hb n k ∧
        finiteAngleAt a b ha hb n k≤C*(k+1:ℝ)/frequency a b n := by
  -- The comparison is uniform over the complete source first half, so the constants are independent of the actual index as well as the degree.
  obtain ⟨Q,hQ,hcomp⟩ := firstHalf_bessel_comparison ha hb
  obtain ⟨d,D,hd,hD,hlinear⟩ := positiveZero_linear_bounds ha
  refine ⟨d/2,2*D,by positivity,by positivity,?_⟩
  have he := (frequency_tendsto a b).eventually (eventually_ge_atTop (2*Q+1))
  filter_upwards [hcomp,he] with n hn hlarge
  have hN : 0<frequency a b n := hn.1
  have hN2 : 2*Q≤(frequency a b n)^2 := by nlinarith [sq_nonneg (frequency a b n-1)]
  have hsmall : Q/(frequency a b n)^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos hN)).mpr (by linarith)
  refine ⟨hN,?_⟩
  intro k hk
  have hj := (positiveZero_properties ha k).1
  have herr := hn.2 k hk
  have hehalf : Q*positiveZero a ha k/(frequency a b n)^2≤positiveZero a ha k/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hj.le
    convert hh using 1 <;> ring
  have hlow := (abs_le.mp herr).1
  have hupp := (abs_le.mp herr).2
  refine ⟨(div_le_iff₀ hN).mpr ?_,(le_div_iff₀ hN).mpr ?_⟩
  · nlinarith [(hlinear k).1]
  · nlinarith [(hlinear k).2]

end
end jacobi.Jacobi
