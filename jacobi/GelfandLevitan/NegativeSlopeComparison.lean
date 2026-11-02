import jacobi.GelfandLevitan.MidpointCharacteristics
import jacobi.Reference.CharacteristicComparison

/-!
Article: jacobi, Proposition C.2.
The actual derivative characteristic has leading negative-energy
normalization b/(y*a_0) to one. The original GL row functional gives
an inverse-y relative correction. Together with the already proved
a/a_0 to one this fixes the leading normalization used in the boundary
classification and the separated-product scalar comparison.
Use: midpointSlope_negative_correction bounds the actual derivative row coefficient functional in the same source uniform norm.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine continuous reference wave at shifted negative energy has its original uniform inverse-frequency envelope.
Use: midpointSlope_negative_correction bounds the actual derivative row coefficient functional in the same source uniform norm.
Article: jacobi, Proposition C.2.
Proof: specialize the independently proved full high-frequency wave estimate to i*y and bound its spatial exponential by its physical midpoint value. -/
theorem halfSolution_negative_norm_bound (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ y:ℝ,1≤y →
      ‖halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)‖≤
        B*y^(-gamma a)*Real.exp (y/2) := by
  -- The half-domain function is the actual source wave used in every original coefficient functional.
  obtain ⟨B,hB,hbound⟩ := wave_uniform_high_frequency ha
  refine ⟨B,hB,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  apply ((halfSolution a ha _).norm_le (by positivity)).mpr
  intro t
  have h := hbound (Complex.I*(y:ℂ)) (by rwa [hn]) (halfTime t) (halfTime_mem t)
  rw [halfSolution_apply,solution_negative_eq_wave]
  simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,zero_add,abs_of_pos hyp] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by nlinarith [(halfTime_mem t).2])) (by positivity))

/-- The original midpoint slope correction is at most a fixed multiple of the original negative-frequency amplitude.
Use: midpointSlope_negative_relative_bound divides by the actual positive y*a_0 lower bound to obtain the leading derivative normalization.
Article: jacobi, Proposition C.2.
Proof: the exact actual slope formula has the original diagonal times a_0 and the genuine bounded derivative-row coefficient functional. The uniform original halfSolution norm bounds both terms. -/
theorem midpointSlope_negative_correction (a : ℝ) (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ y:ℝ,1≤y →
      ‖midpointSlope a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
        solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖≤
          D*y^(-gamma a)*Real.exp (y/2) := by
  -- No bound on an independently chosen candidate derivative is used: the original midpointDerivativeVector is the proved true derivative row.
  obtain ⟨B,hB,hbound⟩ := halfSolution_negative_norm_bound a ha
  let L := |kernelDiagonal a ha halfMidpoint|+‖coefficientFunctional (midpointDerivativeVector a ha)‖
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨(L+1)*B,by positivity,fun y hy => ?_⟩
  let W := halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)
  have hW := hbound y hy
  have hf : ‖solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖≤‖W‖ := by
    have h := W.norm_coe_le_norm (halfInclusion halfMidpoint)
    rw [halfSolution_apply] at h
    change ‖solution a _ (min (1/2) (1/2))‖≤‖W‖ at h
    simpa only [min_self] using h
  rw [midpointSlope_reference,add_assoc,add_sub_cancel_left]
  calc
    _ ≤ ‖(kernelDiagonal a ha halfMidpoint:ℂ)*solution a
        ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖+
        ‖coefficientFunctional (midpointDerivativeVector a ha) W‖ := norm_add_le _ _
    _ ≤ L*‖W‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
        ((coefficientFunctional (midpointDerivativeVector a ha)).le_opNorm W)).trans_eq (by dsimp [L]; ring)
    _ ≤ (L+1)*(B*y^(-gamma a)*Real.exp (y/2)) :=
      mul_le_mul (by linarith) hW (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The original derivative correction divided by the true reference y*a_0 is O(1/y) on the shifted negative axis.
Use: midpointSlope_negative_leading proves the actual normalized derivative limit without a boundary-condition premise.
Article: jacobi, Proposition C.2.
Proof: divide the true derivative correction bound by the independently proved original positive reference midpoint lower bound times y. The matching original power and exponential cancel exactly. -/
theorem midpointSlope_negative_relative_bound (a : ℝ) (ha : -1<a) :
    ∃ C Y:ℝ,0<C ∧ 1≤Y ∧ ∀ y:ℝ,Y≤y →
      ‖(midpointSlope a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
        solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))/
        ((y:ℂ)*solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))‖≤C/y := by
  -- Positivity of the actual lower bound is proved before dividing by the original midpoint value.
  obtain ⟨D,hD,hbound⟩ := midpointSlope_negative_correction a ha
  obtain ⟨c,Y,hc,hY,hlower⟩ := solution_negative_lower ha (A := (1/2:ℝ)) (by norm_num)
  refine ⟨D/c,Y,by positivity,hY,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one (hY.trans hy)
  have hl := (hlower y hy (1/2:ℝ) (by norm_num)).trans (Complex.re_le_norm _)
  rw [show (1/2:ℝ)*y=y/2 by ring,mul_right_comm c (Real.exp (y/2))] at hl
  have hp := Real.rpow_pos_of_pos hyp (-gamma a)
  have hden : 0<c*y^(-gamma a)*Real.exp (y/2) := by positivity
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  have h := div_le_div₀ (by positivity : 0≤D*y^(-gamma a)*Real.exp (y/2))
    (hbound y (hY.trans hy)) (mul_pos hyp hden) (mul_le_mul_of_nonneg_left hl hyp.le)
  apply h.trans_eq
  field_simp [hyp.ne',hc.ne',hp.ne',(Real.exp_pos (y/2)).ne']

/-- The original reference slope has normalized leading quotient b_0/(y*a_0) tending to one at shifted negative energy.
Use: midpointSlope_negative_leading transfers the reference normalization to the actual original derivative characteristic.
Article: jacobi, Proposition C.2.
Proof: the proved original logarithmic slope differs from y by O(1/y). Division by the genuine positive y gives O(1/y^2), which tends to zero. Reality transfers the actual real quotient estimate to the unchanged original complex quotient. -/
theorem reference_midpointSlope_negative_leading (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)/
      ((y:ℂ)*solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))) atTop (𝓝 1) := by
  -- Both real parts are the actual real-energy reference values, so no complex-frequency branch is differentiated.
  obtain ⟨C,_,hbound⟩ := solution_negative_midpoint_asymptotic ha
  obtain ⟨c,Y,hc,_,hlower⟩ := solution_negative_lower ha (A := (1/2:ℝ)) (by norm_num)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun y:ℝ => C/y/y) atTop (𝓝 0) :=
    (tendsto_id.const_div_atTop C).div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hz
  filter_upwards [hbound,eventually_ge_atTop Y,eventually_gt_atTop (0:ℝ)] with y hy hY hyp
  have ha0 : solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)≠0 := by
    have hl := hlower y hY (1/2:ℝ) (by norm_num)
    intro h
    rw [h,Complex.zero_re] at hl
    exact not_le_of_gt (by positivity : 0<c*Real.exp ((1/2)*y)*y^(-gamma a)) hl
  have he : solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)/
      ((y:ℂ)*solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))-1=
      (solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)/
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)-(y:ℂ))/(y:ℂ) := by
    field_simp [ha0,Complex.ofReal_ne_zero.mpr hyp.ne']
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  apply div_le_div_of_nonneg_right ?_ hyp.le
  rw [← solution_real a (jacobi.Jacobi.endpointCorrection a-y^2) (1/2),
    ← solutionSlope_real a (jacobi.Jacobi.endpointCorrection a-y^2) (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1),
    ← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact hy

/-- The actual original derivative characteristic has the correct leading negative-energy normalization b/(y*a_0) tending to one.
Use: the actual separated-product factorization and boundary classification use this normalized original b, without assuming any target midpoint condition.
Article: jacobi, Proposition C.2.
Proof: its difference from the original reference normalized slope is the proved O(1/y) genuine GL derivative correction. Add its zero limit to the independently proved reference limit. -/
theorem midpointSlope_negative_leading (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => midpointSlope a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      ((y:ℂ)*solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))) atTop (𝓝 1) := by
  -- Only the actual original slope correction is sent to zero; the original reference normalization is kept separately until the final sum.
  obtain ⟨C,Y,_,_,hbound⟩ := midpointSlope_negative_relative_bound a ha
  have hdiff : Tendsto (fun y:ℝ => (midpointSlope a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
      solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))/
      ((y:ℂ)*solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop C)
    filter_upwards [eventually_ge_atTop Y] with y hy using hbound y hy
  have h := (reference_midpointSlope_negative_leading a ha).add hdiff
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with y
  ring

end
end jacobi.GelfandLevitan
