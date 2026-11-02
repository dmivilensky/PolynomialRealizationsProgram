import jacobi.GelfandLevitan.NegativePointBounds

/-!
Article: jacobi, Theorem 2.1.
The actual GL-transformed midpoint value is asymptotic to its original
reference midpoint value at shifted negative energy. The relative error
has an explicit inverse-y bound. Only the already constructed bounded
kernel and the proved original negative-energy estimates are used;
the later differentiability and boundary closure assertions are separate.
Use: fixes the endpoint used by all transformed midpoint values and the negative-energy comparison.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference _root_.Complex
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformedSolution solution transformationKernel

/-- The genuine midpoint of the physical half interval on which the original GL transformation is constructed.
Use: fixes the endpoint used by all transformed midpoint values and the negative-energy comparison.
Article: jacobi, Proposition C.2.
-/
def halfMidpoint : HalfInterval := ⟨1/2,by norm_num⟩

/-- The actual GL correction at the midpoint has the sharper negative-energy bound with one extra inverse-frequency factor.
Use: proves transformed_midpoint_relative_bound after division by the genuine positive reference lower bound.
Article: jacobi, Proposition C.2.
Proof: specialize the already proved original all-point negative-energy
correction estimate to the physical midpoint and simplify t*y=y/2. -/
theorem transformed_negative_midpoint_correction (a : ℝ) (ha : -1<a) :
    ∃ D : ℝ,0<D ∧ ∀ y : ℝ,1≤y →
      ‖transformedSolution a ha halfMidpoint ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖≤
          D*y^(-gamma a)*Real.exp (y/2)/y := by
  simpa only [halfMidpoint,show (1/2:ℝ)*_=_/2 by ring] using
    transformed_negative_correction a ha halfMidpoint

/-- The actual transformed midpoint divided by the original reference midpoint differs from one by at most a fixed constant over y.
Use: proves transformed_midpoint_negative_limit, fixing the actual relative negative-energy normalization needed by the midpoint closure argument.
Article: jacobi, Proposition C.2.
Proof: divide the proved original transformation correction by the
actual reference midpoint value. Its real part is positive and has
the genuine matching lower bound c*y^(-gamma)*exp(y/2); this lower
bound also bounds its complex norm, so every cancellation is legitimate. -/
theorem transformed_midpoint_relative_bound (a : ℝ) (ha : -1<a) :
    ∃ C Y : ℝ,0<C ∧ 1≤Y ∧ ∀ y : ℝ,Y≤y →
      ‖transformedSolution a ha halfMidpoint ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)-1‖≤C/y := by
  -- The constructed u and original f are used unchanged in numerator and denominator.
  obtain ⟨D,hD,hdiff⟩ := transformed_negative_midpoint_correction a ha
  obtain ⟨c,Y,hc,hY,hlower⟩ := solution_negative_lower ha (A := (1/2:ℝ)) (by norm_num)
  refine ⟨D/c,Y,by positivity,hY,fun y hy => ?_⟩
  have hy1 : 1≤y := hY.trans hy
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy1
  have hp := Real.rpow_pos_of_pos hyp (-gamma a)
  have hl := (hlower y hy (1/2:ℝ) (by norm_num)).trans (Complex.re_le_norm _)
  rw [show (1/2:ℝ)*y=y/2 by ring] at hl
  have hl' : c*y^(-gamma a)*Real.exp (y/2)≤
      ‖solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖ := by nlinarith [hl]
  have hnorm : 0<‖solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖ :=
    (mul_pos (mul_pos hc hp) (Real.exp_pos _)).trans_le hl'
  have hneq := norm_pos_iff.mp hnorm
  have he : transformedSolution a ha halfMidpoint ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)-1=
        (transformedSolution a ha halfMidpoint ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
          solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))/
            solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2) := by field_simp [hneq]
  rw [he,norm_div]
  apply (div_le_iff₀ hnorm).mpr
  calc
    _ ≤ D*y^(-gamma a)*Real.exp (y/2)/y := hdiff y hy1
    _ = ((D/c)/y)*(c*y^(-gamma a)*Real.exp (y/2)) := by field_simp [hc.ne',hyp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hl' (by positivity)

/-- The actual transformed midpoint and reference midpoint have relative normalization one at shifted negative energy.
Use: supplies the original a/a_0->1 comparison for the final characteristic and midpoint normalization in Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the fully proved inverse-y relative error tends to zero by the elementary reciprocal limit; the norm characterization gives convergence to one in the complex field. -/
theorem transformed_midpoint_negative_limit (a : ℝ) (ha : -1<a) :
    Tendsto (fun y : ℝ => transformedSolution a ha halfMidpoint ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)) atTop (𝓝 1) := by
  obtain ⟨C,Y,_,_,hbound⟩ := transformed_midpoint_relative_bound a ha
  have hz : Tendsto (fun y : ℝ => C/y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hz
  filter_upwards [eventually_ge_atTop Y] with y hy using hbound y hy

end
end jacobi.GelfandLevitan
