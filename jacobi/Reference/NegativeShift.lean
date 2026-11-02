import jacobi.Reference.CharacteristicSigmaNegative
import jacobi.Reference.CharacteristicNormalization

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Both original characteristic functions are compared at the same shifted
negative energy c_0-y^2. The square-root change of radial variable is
proved to preserve the actual leading exponential and real-power
normalization. Thus the two already proved integral-derived constants
refer to precisely the same original energy path.
Use: preserves the exponential normalization in negative_shift_limit and the original characteristic comparison.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A fixed energy shift changes the true large negative radial frequency by a quantity tending to zero.
Use: preserves the exponential normalization in negative_shift_limit and the original characteristic comparison.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: rationalize the exact square-root square. For large positive
y, the true sum sqrt(y^2-c)+y is at least y, so the radial difference
has norm at most |c|/y. The latter tends to zero. -/
theorem negative_frequency_shift (c : ℝ) :
    Tendsto (fun y : ℝ => Real.sqrt (y^2-c)-y) atTop (𝓝 0) := by
  -- The actual square root has a positive argument eventually; no formal square-root expansion is used.
  apply squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop |c|)
  filter_upwards [eventually_ge_atTop (|c|+1)] with y hy
  have hyp : 0<y := by linarith [abs_nonneg c]
  have harg : 0≤y^2-c := by nlinarith [le_abs_self c,abs_nonneg c]
  have hs := Real.sq_sqrt harg
  have hp : 0≤Real.sqrt (y^2-c) := Real.sqrt_nonneg _
  have he : (Real.sqrt (y^2-c)-y)*(Real.sqrt (y^2-c)+y)= -c := by
    nlinarith [hs]
  have hab := congrArg abs he
  rw [abs_mul,abs_of_nonneg (show 0≤Real.sqrt (y^2-c)+y by positivity),abs_neg] at hab
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hyp).mpr
  nlinarith [mul_nonneg (abs_nonneg (Real.sqrt (y^2-c)-y)) hp]

/-- A fixed real spectral shift preserves the exact leading power-exponential negative-axis limit of an actual real-valued function.
Use: moves the proved original Bessel characteristic asymptotic to the same c_0-y^2 path as the original reference characteristic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: put Y=sqrt(y^2-c). Its exact square gives -Y^2=c-y^2
eventually. The proved radial difference tends to zero, Y/y tends
to one and Y tends to infinity. The extra factors (y/Y)^p and
exp(Y-y) therefore both tend to one in the original normalized limit. -/
theorem negative_shift_limit {p L : ℝ} {F : ℝ → ℝ}
    (hF : Tendsto (fun y : ℝ => y^p*Real.exp (-y)*F (-y^2)) atTop (𝓝 L)) (c : ℝ) :
    Tendsto (fun y : ℝ => y^p*Real.exp (-y)*F (c-y^2)) atTop (𝓝 L) := by
  -- The genuine radial change is evaluated on the already fixed function, so the spectral energy is never redefined.
  let Y : ℝ → ℝ := fun y => Real.sqrt (y^2-c)
  have hquad : Tendsto (fun y : ℝ => y^2-c) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (max 1 (M+c+1))] with y hy
    have hy1 : (1:ℝ)≤y := (le_max_left _ _).trans hy
    have hyM : M+c+1≤y := (le_max_right _ _).trans hy
    nlinarith
  have hY : Tendsto Y atTop atTop := Real.tendsto_sqrt_atTop.comp hquad
  have hdiff : Tendsto (fun y => Y y-y) atTop (𝓝 0) := negative_frequency_shift c
  have hrel : Tendsto (fun y => Y y/y) atTop (𝓝 1) := by
    have hh := (hdiff.div_atTop tendsto_id).add_const 1
    norm_num only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have he : (Y y-y)/y+1=Y y/y := by field_simp; ring
    exact he
  have hrat : Tendsto (fun y => y/Y y) atTop (𝓝 1) := by
    simpa only [inv_div,inv_one] using hrel.inv₀ (by norm_num : (1:ℝ)≠0)
  have hp := hrat.rpow_const (p := p) (Or.inl (by norm_num : (1:ℝ)≠0))
  have he : Tendsto (fun y => Real.exp (Y y-y)) atTop (𝓝 1) := by
    convert! Real.continuous_exp.continuousAt.tendsto.comp hdiff using 1
    simp
  have hh := (hp.mul he).mul (hF.comp hY)
  simp only [Real.one_rpow,one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),hY.eventually (eventually_gt_atTop (0:ℝ))] with y hy hYp
  have harg : 0≤y^2-c := Real.sqrt_pos.mp hYp |>.le
  have hs : -(Y y)^2=c-y^2 := by dsimp [Y]; rw [Real.sq_sqrt harg]; ring
  dsimp only [Function.comp_apply]
  rw [hs,Real.div_rpow hy.le hYp.le,div_eq_mul_inv]
  have hr : (y^p*((Y y)^p)⁻¹)*Real.exp (Y y-y)*((Y y)^p*Real.exp (-Y y))=
      y^p*Real.exp (-y) := by
    have heq : Real.exp (Y y-y)*Real.exp (-Y y)=Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = y^p*(((Y y)^p)⁻¹*(Y y)^p)*(Real.exp (Y y-y)*Real.exp (-Y y)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (Real.rpow_pos_of_pos hYp p).ne',mul_one,heq]
  linear_combination F (c-y^2)*hr

/-- The original Bessel characteristic has the same exact printed leading limit as Delta_tau on the identical original shifted negative-energy path.
Use: fixes their relative normalization from the two genuine characteristic asymptotics in Appendix C.2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: apply the proved genuine fixed-shift limit to the actual Bessel characteristic's already proved full-order negative-axis asymptotic. -/
theorem characteristicSigma_shifted_negative_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*
      (characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.pi^a/(2*Real.sqrt Real.pi))) :=
  negative_shift_limit (F := fun E => (characteristicSigma a (E:ℂ)).re)
    (characteristicSigma_negative_asymptotic ha) (jacobi.Jacobi.endpointCorrection a)

/-- The original reference characteristic has the article's exact printed leading limit also on the unshifted negative axis.
Use: records the displayed Delta_tau(-y^2) asymptotic in the original energy variable, in addition to the common shifted path used in the normalization proof.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: apply the proved fixed-shift theorem to the actual translated
reference characteristic with the opposite original potential shift.
The translated energy then equals exactly -y^2 by finite algebra. -/
theorem characteristicTau_unshifted_negative_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*(characteristicTau a ((-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.pi^a/(2*Real.sqrt Real.pi))) := by
  -- Translate the already fixed actual characteristic, apply the opposite original energy shift, and simplify its true argument.
  let F : ℝ → ℝ := fun E => (characteristicTau a ((jacobi.Jacobi.endpointCorrection a+E:ℝ):ℂ)).re
  have hf : Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*F (-y^2)) atTop
      (𝓝 (Real.pi^a/(2*Real.sqrt Real.pi))) := by
    simpa only [F,sub_eq_add_neg] using characteristicTau_negative_asymptotic ha
  have hh := negative_shift_limit hf (- jacobi.Jacobi.endpointCorrection a)
  convert! hh using 1
  funext y
  dsimp only [F]
  rw [show jacobi.Jacobi.endpointCorrection a+(- jacobi.Jacobi.endpointCorrection a-y^2)= -y^2 by ring]

end
end jacobi.Reference
