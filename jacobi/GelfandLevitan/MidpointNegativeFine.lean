import jacobi.GelfandLevitan.MidpointLaplace
import jacobi.GelfandLevitan.NegativeRowBounds
import jacobi.GelfandLevitan.SeparatedNegative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The true midpoint diagonal zero improves the original value correction
to y*(a/a_0-1) to zero. The actual continuous derivative row contributes
o(1) to (b-b_0)/a_0. These are the genuine fine asymptotics needed to
remove the last Robin parameter in the exact mixed characteristic identity.
Use: midpointValue_negative_scaled_error applies the genuine continuous-row negative-energy bound to the original transformed value correction.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The true original midpoint inverse row is exactly the physical prefix vector of its actual continuous K row.
Use: midpointValue_negative_scaled_error applies the genuine continuous-row negative-energy bound to the original transformed value correction.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: both genuine L2 vectors have the independently proved same prefix-indicator K representative. -/
theorem midpoint_solutionRow_candidate (a : ℝ) (ha : -1<a) :
    candidateVector halfMidpoint (transformationRows a ha halfMidpoint)=solutionRow a ha halfMidpoint := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [candidateVector_ae halfMidpoint (transformationRows a ha halfMidpoint),
    solutionRow_representative a ha halfMidpoint] with r hc hs
  rw [hc,hs]
  rfl

/-- The actual transformed midpoint value has zero first-order reference-normalized correction on the shifted negative axis.
Use: midpointRobinParameter_zero excludes the genuine residual Robin parameter from the original exact mixed characteristic product.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the true coefficient correction is bounded by the original reference envelope times the exponentially weighted absolute K row. Divide by the original positive reference midpoint lower bound. The remaining normalized absolute row integral tends to zero by the independently proved endpoint Laplace theorem and actual midpoint diagonal zero. -/
theorem midpointValue_negative_scaled_error (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => (y:ℂ)*(midpointValue a ha (shiftedNegativeEnergy a y)/
      solution a (shiftedNegativeEnergy a y) (1/2)-1)) atTop (𝓝 0) := by
  -- The improved order follows from the actual endpoint value of K, not from replacing its original integral by an assumed expansion.
  obtain ⟨B,hB,hbound⟩ := midpointRow_negative_weighted_bound a ha
  obtain ⟨c,Y,hc,hY,hlower⟩ := solution_negative_lower ha (A := (1/2:ℝ)) (by norm_num)
  let g := transformationRows a ha halfMidpoint
  have hlim := (midpoint_kernel_laplace_zero a ha).const_mul (B/c)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop Y] with y hy
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one (hY.trans hy)
  have hp := Real.rpow_pos_of_pos hyp (-gamma a)
  have hl := (hlower y hy (1/2:ℝ) (by norm_num)).trans (Complex.re_le_norm _)
  rw [show (1/2:ℝ)*y=y/2 by ring,mul_right_comm c (Real.exp (y/2))] at hl
  have hpos : 0<c*y^(-gamma a)*Real.exp (y/2) := by positivity
  have ha0 : solution a (shiftedNegativeEnergy a y) (1/2)≠0 := norm_pos_iff.mp (hpos.trans_le hl)
  have he : midpointValue a ha (shiftedNegativeEnergy a y)-solution a (shiftedNegativeEnergy a y) (1/2)=
      coefficientFunctional (candidateVector halfMidpoint g:Space) (halfSolution a ha (shiftedNegativeEnergy a y)) := by
    rw [midpointValue,transformedSolution_reference_form]
    change solution a (shiftedNegativeEnergy a y) (1/2)+
      coefficientFunctional (solutionRow a ha halfMidpoint:Space) (halfSolution a ha (shiftedNegativeEnergy a y))-
      solution a (shiftedNegativeEnergy a y) (1/2)=_
    rw [add_sub_cancel_left]
    exact congrArg (fun v:halfSubspace => coefficientFunctional (v:Space) (halfSolution a ha (shiftedNegativeEnergy a y)))
      (midpoint_solutionRow_candidate a ha).symm
  have hI : (∫ r:Interval in prefixSet (1/2),|g r| * Real.exp ((r:ℝ)*y))=
      ∫ s in (0:ℝ)..(1/2:ℝ),|transformationKernel a ha halfMidpoint (halfParameterClamp s)| * Real.exp (s*y) := by
    rw [← prefix_integral (fun s:ℝ => |transformationKernel a ha halfMidpoint (halfParameterClamp s)| * Real.exp (s*y))
      (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) 1)]
    apply setIntegral_congr_fun (prefixSet_measurable (1/2))
    intro r _
    dsimp only
    rw [halfParameterClamp_unit]
    rfl
  have hi : 0≤∫ r:Interval in prefixSet (1/2),|g r| * Real.exp ((r:ℝ)*y) :=
    integral_nonneg (fun _ => by positivity)
  have hb := hbound g y (hY.trans hy)
  change ‖coefficientFunctional (candidateVector halfMidpoint g:Space)
    (halfSolution a ha (shiftedNegativeEnergy a y))‖≤_ at hb
  rw [div_sub_one ha0,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp,norm_div]
  have hd := div_le_div₀ (mul_nonneg (mul_nonneg hB.le hp.le) hi) hb hpos hl
  apply (mul_le_mul_of_nonneg_left hd hyp.le).trans_eq
  rw [hI,show -y/2= -(y/2) by ring,Real.exp_neg]
  field_simp [hc.ne',hp.ne',(Real.exp_pos (y/2)).ne']

/-- The true derivative-row contribution gives a vanishing reference-normalized original slope correction at shifted negative energy.
Use: midpointRobinParameter_zero combines this actual slope correction with the improved original value correction and the normalized relative characteristic error.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual slope formula loses its diagonal term by the proved original midpoint zero. Its remaining coefficient is the actual continuous derivative row, whose genuine normalized integral is O(1/y) by the original continuous-row bound. -/
theorem midpointSlope_negative_difference (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => midpointSlope a ha (shiftedNegativeEnergy a y)/
      solution a (shiftedNegativeEnergy a y) (1/2)-
      solutionSlope a (shiftedNegativeEnergy a y) (1/2)/solution a (shiftedNegativeEnergy a y) (1/2))
      atTop (𝓝 0) := by
  -- The row is the already identified genuine partial_t K, on the fixed original positive strip reaching the actual midpoint.
  let g := derivativeCandidateRows ha (d := 1/4) (by norm_num) ⟨1/2,by norm_num⟩
  obtain ⟨C,Y,_,_,hbound⟩ := midpointRow_negative_relative_bound a ha
  apply squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop (C*‖g‖))
  filter_upwards [eventually_ge_atTop Y] with y hy
  rw [← sub_div,midpointSlope_reference,kernelDiagonal_midpoint_zero,Complex.ofReal_zero,
    zero_mul,add_zero,add_sub_cancel_left]
  exact hbound g y hy

end
end jacobi.GelfandLevitan
