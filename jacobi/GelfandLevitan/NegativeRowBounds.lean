import jacobi.GelfandLevitan.NegativeSlopeComparison
import jacobi.GelfandLevitan.PrefixPairing

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Actual continuous midpoint rows paired with the original negative-energy
reference solution gain one inverse frequency. The estimate retains
the weighted absolute row integral, so a zero midpoint value yields
the stronger little-o bound through the actual endpoint Laplace theorem.
Use: midpointRow_negative_bound gains 1/y in every actual continuous-row coefficient estimate.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine physical half-prefix exponential integral has its exact elementary inverse-frequency bound.
Use: midpointRow_negative_bound gains 1/y in every actual continuous-row coefficient estimate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: transfer the original subtype prefix integral to the physical half interval, integrate exp(s*y), and bound exp(y/2)-1 by exp(y/2). -/
theorem prefix_exponential_integral_le {y : ℝ} (hy : 0<y) :
    (∫ r:Interval in prefixSet (1/2),Real.exp ((r:ℝ)*y))≤Real.exp (y/2)/y := by
  rw [prefix_integral (fun s:ℝ => Real.exp (s*y)) (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) 1),
    intervalIntegral.integral_comp_mul_right Real.exp hy.ne',integral_exp]
  simp only [zero_mul,Real.exp_zero,smul_eq_mul]
  rw [show (1/2:ℝ)*y=y/2 by ring]
  have h : (Real.exp (y/2)-1)/y≤Real.exp (y/2)/y :=
    div_le_div_of_nonneg_right (by linarith) hy.le
  exact (show y⁻¹*(Real.exp (y/2)-1)=(Real.exp (y/2)-1)/y by ring).trans_le h

/-- The actual coefficient of any continuous physical midpoint row is bounded by its genuine exponentially weighted absolute row integral.
Use: midpointRow_negative_bound and the sharpened actual midpoint value comparison use the same original source coefficient integral, retaining spatial endpoint cancellation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the true candidate vector has its original prefix-indicator representative. The genuine reference solution satisfies the proved imaginary-frequency envelope. Dominate its actual Bochner integral by that envelope times the unchanged continuous row. -/
theorem midpointRow_negative_weighted_bound (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ g:C(Interval,ℝ),∀ y:ℝ,1≤y →
      ‖coefficientFunctional (candidateVector halfMidpoint g:Space)
        (halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))‖≤
      B*y^(-gamma a)*(∫ r:Interval in prefixSet (1/2),|g r| * Real.exp ((r:ℝ)*y)) := by
  -- The original moving-prefix representative is used only under its actual integral, where it is legitimate for arbitrary L2 data.
  obtain ⟨B,hB,hbound⟩ := wave_uniform_high_frequency ha
  refine ⟨B,hB,fun g y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  let J := fun r:Interval => B*y^(-gamma a)*(|g r| * Real.exp ((r:ℝ)*y))
  have hJ : IntegrableOn J (prefixSet (1/2)) volume :=
    (show Continuous J by dsimp [J]; fun_prop).continuousOn.integrableOn_compact
      ((isClosed_le continuous_subtype_val continuous_const).isCompact)
  change ‖prefixPairing halfMidpoint (halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)) g‖≤_
  rw [prefixPairing_apply]
  change ‖∫ r:Interval in prefixSet (1/2),(g r:ℂ)*halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) r‖≤_
  have h := norm_integral_le_of_norm_le
    (f := fun r:Interval => (g r:ℂ)*halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) r)
    hJ (ae_restrict_of_forall_mem (prefixSet_measurable (1/2)) (fun r hr => by
    have hf := hbound (Complex.I*(y:ℂ)) (by rwa [hn]) (halfTime r) (halfTime_mem r)
    rw [halfSolution_apply,solution_negative_eq_wave]
    simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,one_mul,zero_add,abs_of_pos hyp] at hf
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have he : halfTime r=(r:ℝ) := min_eq_left hr
    rw [he] at hf ⊢
    exact (mul_le_mul_of_nonneg_left hf (abs_nonneg (g r))).trans_eq (by dsimp only [J]; ring)))
  exact h.trans_eq (integral_const_mul _ _)

/-- Every genuine continuous midpoint-row coefficient has the actual reference amplitude times a uniform inverse-frequency bound.
Use: midpointRow_negative_relative_bound controls the true derivative-row correction in the final Neumann comparison.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: retain the original weighted-row estimate, bound the actual row by its true supremum norm, and use the proved physical prefix exponential integral. -/
theorem midpointRow_negative_bound (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ g:C(Interval,ℝ),∀ y:ℝ,1≤y →
      ‖coefficientFunctional (candidateVector halfMidpoint g:Space)
        (halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))‖≤
      B*‖g‖*y^(-gamma a)*Real.exp (y/2)/y := by
  -- All rows share the same actual source reference constant; only their genuine continuous supremum norm remains.
  obtain ⟨B,hB,hbound⟩ := midpointRow_negative_weighted_bound a ha
  refine ⟨B,hB,fun g y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  apply (hbound g y hy).trans
  have hrow : (∫ r:Interval in prefixSet (1/2),|g r| * Real.exp ((r:ℝ)*y))≤
      ‖g‖*(∫ r:Interval in prefixSet (1/2),Real.exp ((r:ℝ)*y)) := by
    rw [← integral_const_mul]
    apply integral_mono
      ((g.continuous.abs.mul (by fun_prop : Continuous (fun r:Interval => Real.exp ((r:ℝ)*y)))).continuousOn.integrableOn_compact
        ((isClosed_le continuous_subtype_val continuous_const).isCompact))
      ((show Continuous (fun r:Interval => ‖g‖*Real.exp ((r:ℝ)*y)) by fun_prop).continuousOn.integrableOn_compact
        ((isClosed_le continuous_subtype_val continuous_const).isCompact))
    intro r
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm r) (Real.exp_pos _).le
  have htot := hrow.trans (mul_le_mul_of_nonneg_left (prefix_exponential_integral_le hyp) (norm_nonneg g))
  exact (mul_le_mul_of_nonneg_left htot (by positivity)).trans_eq (by ring)

/-- The actual continuous midpoint-row coefficient divided by the genuine reference midpoint value is O(norm(g)/y).
Use: the true partial_t K row gives a vanishing original slope correction once the independently proved original diagonal is zero.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: divide the genuine inverse-frequency row estimate by the independently proved strictly positive original reference midpoint lower bound; its actual power and exponential cancel. -/
theorem midpointRow_negative_relative_bound (a : ℝ) (ha : -1<a) :
    ∃ C Y:ℝ,0<C ∧ 1≤Y ∧ ∀ g:C(Interval,ℝ),∀ y:ℝ,Y≤y →
      ‖coefficientFunctional (candidateVector halfMidpoint g:Space)
        (halfSolution a ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))/
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)‖≤C*‖g‖/y := by
  -- The denominator is the actual selected reference midpoint, with its genuine nonzero lower bound checked before cancellation.
  obtain ⟨B,hB,hbound⟩ := midpointRow_negative_bound a ha
  obtain ⟨c,Y,hc,hY,hlower⟩ := solution_negative_lower ha (A := (1/2:ℝ)) (by norm_num)
  refine ⟨B/c,Y,by positivity,hY,fun g y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one (hY.trans hy)
  have hl := (hlower y hy (1/2:ℝ) (by norm_num)).trans (Complex.re_le_norm _)
  rw [show (1/2:ℝ)*y=y/2 by ring,mul_right_comm c (Real.exp (y/2))] at hl
  have hp := Real.rpow_pos_of_pos hyp (-gamma a)
  have hpos : 0<c*y^(-gamma a)*Real.exp (y/2) := by positivity
  rw [norm_div]
  have h := div_le_div₀ (by positivity : 0≤B*‖g‖*y^(-gamma a)*Real.exp (y/2)/y)
    (hbound g y (hY.trans hy)) hpos hl
  apply h.trans_eq
  field_simp [hyp.ne',hc.ne',hp.ne',(Real.exp_pos (y/2)).ne']

end
end jacobi.GelfandLevitan
