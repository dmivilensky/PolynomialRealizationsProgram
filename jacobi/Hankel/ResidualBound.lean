import jacobi.Hankel.FourierTail
import jacobi.Hankel.QuarticTail

/-!
Article: jacobi, Lemma E.1.
Use: residualIntegral is the literal forcing in the genuine outgoing polynomial comparison equation.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse-fourth-power Liouville residual of the original outgoing Hankel polynomial.
Use: residualIntegral is the literal forcing in the genuine outgoing polynomial comparison equation.
Article: jacobi, Lemma E.1.
-/
def amplitudeResidual (c : ℂ) (x : ℝ) : ℂ :=
  -(c*(c+2)*(c+6))/(8*(x:ℂ)^4)

/-- The actual outgoing Green integral of the original fourth-order polynomial residual.
Use: the exact polynomial comparison identity and tailInverse_bound give the original Jost amplitude's genuine cubic error.
Article: jacobi, Lemma E.1.
-/
def residualIntegral (c : ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi x,outgoingKernel (y-x)*amplitudeResidual c y

/-- The norm of the genuine polynomial residual has its exact inverse-fourth-power majorant on the original positive ray.
Use: residualIntegrand_bound and residualIntegral_bound discharge the actual outgoing cubic forcing estimate.
Article: jacobi, Lemma E.1.
Proof: evaluate the true complex quotient norm; the real spatial coordinate is positive, so its norm is the original coordinate. -/
theorem amplitudeResidual_norm (c : ℂ) {y : ℝ} (hy : 0<y) :
    ‖amplitudeResidual c y‖=(‖c*(c+2)*(c+6)‖/8)*y⁻¹^4 := by
  have hn : ‖(8:ℂ)*(y:ℂ)^4‖=8*y^4 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    norm_num
  rw [amplitudeResidual,norm_div,norm_neg,hn]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

/-- The original causal Green kernel preserves the genuine fourth-order residual majorant.
Use: its actual tail integral has a cubic bound uniform whenever the true complex coefficient remains bounded.
Article: jacobi, Lemma E.1.
Proof: the genuine kernel has norm at most one; multiply by the exact original residual norm. -/
theorem residualIntegrand_bound (c : ℂ) {x y : ℝ} (hy : 0<y) :
    ‖outgoingKernel (y-x)*amplitudeResidual c y‖≤(‖c*(c+2)*(c+6)‖/8)*y⁻¹^4 := by
  rw [norm_mul,← amplitudeResidual_norm c hy]
  exact mul_le_of_le_one_left (norm_nonneg _) (outgoingKernel_norm_le _)

/-- The original outgoing residual integral is genuinely absolutely convergent on every positive ray.
Use: the exact polynomial comparison may subtract this true integral from the separately convergent original Volterra integral.
Article: jacobi, Lemma E.1.
Proof: its measurable original integrand is bounded by the proved integrable quartic tail times the genuine residual coefficient. -/
theorem residualIntegrand_integrable (c : ℂ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun y : ℝ => outgoingKernel (y-x)*amplitudeResidual c y) (Ioi x) := by
  apply ((quarticTail_integrable hx).const_mul (‖c*(c+2)*(c+6)‖/8)).mono'
    (((outgoingKernel_continuous.comp (continuous_id.sub continuous_const)).measurable.mul
      (by unfold amplitudeResidual; fun_prop : Measurable (amplitudeResidual c))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact residualIntegrand_bound c (hx.trans hy)

/-- The true outgoing integral of the actual polynomial residual has its explicit cubic spatial bound.
Use: tailInverse_bound converts this original integral forcing into the genuine uniform cubic outgoing Hankel error needed for the common complex-order zero tail.
Article: jacobi, Lemma E.1.
Proof: bound the norm of the actual convergent integral by its quartic-tail majorant and evaluate the original improper integral exactly as 1/(3*x^3). -/
theorem residualIntegral_bound (c : ℂ) {x : ℝ} (hx : 0<x) :
    ‖residualIntegral c x‖≤‖c*(c+2)*(c+6)‖/(24*x^3) := by
  -- Both the convergence and the numerical-free tail evaluation concern the original residual integral.
  have hb : ∀ᵐ y ∂volume.restrict (Ioi x),
      ‖outgoingKernel (y-x)*amplitudeResidual c y‖≤(‖c*(c+2)*(c+6)‖/8)*y⁻¹^4 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact residualIntegrand_bound c (hx.trans hy)
  have h := (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (residualIntegrand_integrable c hx).norm
      ((quarticTail_integrable hx).const_mul _) hb)
  rw [integral_const_mul,quarticTail_integral hx] at h
  exact h.trans_eq (by ring)

end
end jacobi.Hankel
