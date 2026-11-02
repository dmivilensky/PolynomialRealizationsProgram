import jacobi.Fredholm.WeightedMeans

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The actual printed logarithmic energy-to-mass ratio has a strictly negative
interior shape derivative and a nonnegative determinant-parameter derivative,
including full support. The signs use the proved original weighted-mean
inequalities and genuine dominated derivatives, not formal differentiation.
Source: Chebyshev's integral inequality and the verified common elliptic mean bound.
Use: differentiates the genuine printed Psi without assuming fractional-power differentiability at zero.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The logarithm of the actual normalized ratio written in derivative-friendly additive form.
Use: differentiates the genuine printed Psi without assuming fractional-power differentiability at zero.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def logShape (t c : ℝ) : ℝ := log (i3 t c)-(1/2:ℝ)*log t-(3/2:ℝ)*log (i2 t c)

/-- The additive logarithmic expression is exactly the logarithm of the printed positive shape ratio.
Use: transfers its genuine derivative signs to the original Psi in the article.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: all factors are positive on the physical parameter domain; apply
the ordinary logarithm product, quotient, square-root and real-power identities. -/
theorem log_shape_eq {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    log (shapeRatio t c)=logShape t c := by
  have h2 := i2_pos ⟨ht.1.le,ht.2⟩ hc
  have h3 := (state_mean_bounds ⟨ht.1.le,ht.2⟩ hc).1
  rw [shapeRatio,log_div h3.ne' (mul_pos (sqrt_pos.mpr ht.1) (rpow_pos_of_pos h2 _)).ne',
    log_mul (sqrt_pos.mpr ht.1).ne' (rpow_pos_of_pos h2 _).ne',log_sqrt ht.1.le,log_rpow h2]
  unfold logShape
  ring

/-- The actual logarithmic shape ratio has the strict negative printed interior shape derivative.
Use: energy strictly decreases along an actual constant-mass branch when chi decreases.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: genuine dominated derivatives give the exact logarithmic quotient
formula. The proved covariance says mean_3(psi)<=mean_2(psi); positivity
of the second mean leaves the strictly negative term -1/(2*tau). -/
theorem logShape_shape_hasDerivAt_neg {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    ∃ D : ℝ,HasDerivAt (fun u => log (shapeRatio u c)) D t ∧ D<0 := by
  -- Every differentiated state integral is the original convergent Fredholm quadrature.
  have ht' : t∈Ioc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
  have h2 := i2_pos ⟨ht.1.le,ht.2.le⟩ hc
  have h3 := (state_mean_bounds ⟨ht.1.le,ht.2.le⟩ hc).1
  have hcal := shape_calculus ht hc
  let D := shape3 t c/i3 t c-1/(2*t)-(3/2:ℝ)*(shape2 t c/i2 t c)
  have hd : HasDerivAt (fun u => logShape u c) D t := by
    convert ((hcal.2.log h3.ne').sub (((hasDerivAt_id t).log ht.1.ne').const_mul (1/2:ℝ))).sub
      ((hcal.1.log h2.ne').const_mul (3/2:ℝ)) using 1
    · rfl
    · dsimp only [D,id_eq]
      ring
  have heq : (fun u => log (shapeRatio u c))=ᶠ[𝓝 t] fun u => logShape u c := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact log_shape_eq ⟨hu.1,hu.2.le⟩ hc
  refine ⟨D,hd.congr_of_eventuallyEq heq,?_⟩
  have hcov : shape3 t c/i3 t c≤shape2 t c/i2 t c :=
    (div_le_div_iff₀ h3 h2).mpr (shape_covariance ht' hc)
  have hnon : 0≤shape2 t c := by
    rw [shape2,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact (shapeWeight_bound ⟨ht.1.le,ht.2.le⟩ hc hv).1
  have hterm : 0<1/(2*t) := div_pos (by norm_num) (mul_pos (by norm_num) ht.1)
  dsimp only [D]
  nlinarith [div_nonneg hnon h2.le]

/-- The actual logarithmic shape ratio has its nonnegative determinant-parameter derivative, including tau=1.
Use: controls energy along a mass curve and on the free-support branch.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: dominated chi differentiation gives -(tau/2)*(mean_3(h)-3*mean_2(h)/2).
The proved true response-mean bound makes the bracket nonpositive. -/
theorem logShape_parameter_hasDerivAt_nonneg {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ∃ D : ℝ,HasDerivAt (fun u => log (shapeRatio t u)) D c ∧ 0≤D := by
  -- At full support this is an ordinary derivative in chi, with tau fixed at its physical endpoint.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have h2 := i2_pos ht' hc'
  have h3 := (state_mean_bounds ht' hc').1
  have hcal := parameter_calculus ht' hc
  let D := -(t/2)*(response3 t c/i3 t c-(3/2:ℝ)*(response2 t c/i2 t c))
  have hd : HasDerivAt (fun u => logShape t u) D c := by
    convert ((hcal.2.log h3.ne').sub (hasDerivAt_const c ((1/2:ℝ)*log t))).sub
      ((hcal.1.log h2.ne').const_mul (3/2:ℝ)) using 1
    · rfl
    · dsimp only [D]
      ring
  have heq : (fun u => log (shapeRatio t u))=ᶠ[𝓝 c] fun u => logShape t u := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with u hu
    exact log_shape_eq ht ⟨hu.1.le,hu.2.le⟩
  refine ⟨D,hd.congr_of_eventuallyEq heq,?_⟩
  have hh : response3 t c/i3 t c≤(3/2:ℝ)*response2 t c/i2 t c :=
    (div_le_div_iff₀ h3 h2).mpr (response_mean_bound ht' hc')
  have hh' : response3 t c/i3 t c≤(3/2:ℝ)*(response2 t c/i2 t c) := by
    simpa only [mul_div_assoc] using hh
  dsimp only [D]
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith [ht.1]) (sub_nonpos.mpr hh')

end
end jacobi.Fredholm
