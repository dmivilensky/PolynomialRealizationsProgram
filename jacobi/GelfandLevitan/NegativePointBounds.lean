import jacobi.GelfandLevitan.SelectedEndpoint
import jacobi.GelfandLevitan.PrefixIntegral
import jacobi.Reference.NegativeQuotient

/-!
Article: jacobi, Proposition 2.2.
The actual negative-energy GL correction gains one inverse frequency on
its entire physical half interval. The original midpoint estimate is a
special case; every fixed positive physical point consequently has a
strictly positive transformed value at sufficiently negative energy.
Use: transformed_negative_eventually_pos excludes an identically zero spectral-frequency transform; the original midpoint comparison reuses the same bound.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformedSolution solution transformationKernel

/-- The actual GL correction has a uniform extra inverse-frequency bound at every physical half-interval point.
Use: transformed_negative_eventually_pos excludes an identically zero spectral-frequency transform; the original midpoint comparison reuses the same bound.
Article: jacobi, Proposition 2.2.
Proof: bound the original K row uniformly and insert the proved reference
imaginary-frequency envelope. The genuine physical prefix integral of
exp(s*y) is (exp(t*y)-1)/y, bounded by exp(t*y)/y. -/
theorem transformed_negative_correction (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    ∃ D : ℝ,0<D ∧ ∀ y : ℝ,1≤y →
      ‖transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (t:ℝ)‖≤
          D*y^(-gamma a)*Real.exp ((t:ℝ)*y)/y := by
  -- The norm estimate is for the literal original GL integral and the actual reference solution.
  obtain ⟨M,hM,hK⟩ := transformationKernel_bounded a ha
  obtain ⟨B,hB,hf⟩ := wave_uniform_high_frequency ha
  refine ⟨M*B,by positivity,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  let J : Interval → ℝ := fun r => (M*B*y^(-gamma a))*Real.exp ((r:ℝ)*y)
  have hc : Continuous J := by dsimp [J]; fun_prop
  have hj : IntegrableOn J (prefixSet (t:ℝ)) volume :=
    hc.continuousOn.integrableOn_compact ((isClosed_le continuous_subtype_val continuous_const).isCompact)
  have hb := norm_integral_le_of_norm_le hj (ae_restrict_of_forall_mem (prefixSet_measurable (t:ℝ)) (fun r hr => by
    have hrprefix : (r:ℝ)∈Icc (0:ℝ) (t:ℝ) := ⟨r.property.1,hr⟩
    have href := hf (Complex.I*(y:ℂ)) (by rw [hn]; exact hy) (halfTime r) (halfTime_mem r)
    rw [← solution_negative_eq_wave a y] at href
    simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add,abs_of_pos hyp] at href
    have hrtime : halfTime r=(r:ℝ) := min_eq_left (hrprefix.2.trans t.property.2)
    change ‖(transformationKernel a ha t (halfClamp r):ℂ)*
      solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (halfTime r)‖≤J r
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul (hK _ _) href (norm_nonneg _) hM.le).trans_eq
    dsimp [J]
    rw [hrtime]
    ring))
  rw [transformedSolution_integral,add_sub_cancel_left]
  change ‖∫ r : Interval in prefixSet (t:ℝ),
    (transformationKernel a ha t (halfClamp r):ℂ)*
      solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (halfTime r)‖≤_
  apply hb.trans
  change (∫ r : Interval in prefixSet (t:ℝ),(M*B*y^(-gamma a))*Real.exp ((r:ℝ)*y))≤_
  rw [prefix_integral (fun s : ℝ => (M*B*y^(-gamma a))*Real.exp (s*y))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,t.property.2.trans (by norm_num)⟩),intervalIntegral.integral_const_mul]
  have he : (∫ s in (0:ℝ)..(t:ℝ),Real.exp (s*y))=(Real.exp ((t:ℝ)*y)-1)/y := by
    rw [intervalIntegral.integral_comp_mul_right Real.exp hyp.ne',integral_exp]
    simp only [zero_mul,Real.exp_zero,smul_eq_mul]
    ring
  rw [he]
  have hExp : (Real.exp ((t:ℝ)*y)-1)/y≤Real.exp ((t:ℝ)*y)/y :=
    div_le_div_of_nonneg_right (by linarith) hyp.le
  exact (mul_le_mul_of_nonneg_left hExp (by positivity)).trans_eq (by ring)

/-- At every positive physical point the genuine transformed solution is eventually strictly positive on the shifted negative axis.
Use: persymmetricProfile_pos excludes the zero entire-frequency function forced by simultaneous vanishing of all original spectral waves.
Article: jacobi, Proposition 2.2.
Proof: the original reference solution is bounded below by
c*exp(t*y)*y^(-gamma). The actual GL correction is bounded by the
same positive scale times D/y, which is eventually smaller than c. -/
theorem transformed_negative_eventually_pos (a:ℝ) (ha:-1<a)
    (t:HalfInterval) (ht:0<(t:ℝ)) :
    ∀ᶠ y:ℝ in atTop,
      0<(transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re := by
  -- All estimates belong to the same original selected solution and its literal GL transform.
  obtain ⟨D,hD,hcorr⟩ := transformed_negative_correction a ha t
  obtain ⟨c,Y,hc,hY,hlower⟩ := solution_negative_lower ha ⟨ht,t.property.2⟩
  have hsmall : ∀ᶠ y:ℝ in atTop,D/y<c := by
    have hzero : Tendsto (fun y:ℝ=>D/y) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul D
    exact hzero.eventually_lt_const hc
  filter_upwards [eventually_ge_atTop Y,hsmall] with y hy hdy
  have hyp : 0<y := zero_lt_one.trans_le (hY.trans hy)
  have hp : 0<y^(-gamma a)*Real.exp ((t:ℝ)*y) := by positivity
  have hdiff := (Complex.abs_re_le_norm
    (transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-
      solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (t:ℝ))).trans
        (hcorr y (hY.trans hy))
  have hlow := hlower y hy (t:ℝ) ⟨le_rfl,t.property.2⟩
  have hstrict := mul_lt_mul_of_pos_right hdy hp
  simp only [Complex.sub_re] at hdiff
  have heq : (D/y)*(y^(-gamma a)*Real.exp ((t:ℝ)*y))=
      D*y^(-gamma a)*Real.exp ((t:ℝ)*y)/y := by ring
  rw [heq] at hstrict
  nlinarith [neg_le_abs
    ((transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re-
      (solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (t:ℝ)).re)]

end
end jacobi.GelfandLevitan
