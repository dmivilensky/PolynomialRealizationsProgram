import jacobi.Fredholm.Quadratures

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The printed normalized mass strictly increases in each nontrivial parameter,
including comparison with the physical endpoints. These are genuine integral
inequalities. Pointwise classical derivatives establish strict order of the
original positive integrands, so no differentiation of a singular integral
or endpoint extension is assumed here.
Source: the common verified polynomial weight derivatives and integral positivity.
Use: controls parameter variations and the energy-to-mass ratio uniformly near v=0.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The Fredholm logarithmic derivative factor has the exact common bounded range.
Use: controls parameter variations and the energy-to-mass ratio uniformly near v=0.
Article: jacobi, Theorem D.7.
Proof: the previously proved bound r>=v² permits positive cancellation on (0,1). -/
theorem h_bounds {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) : 0≤v^3/r t c v ∧ v^3/r t c v≤v := by
  have hr := r_pos ht hc ⟨hv.1,hv.2.le⟩
  have hw := weights_bounds ht hc ⟨hv.1.le,hv.2.le⟩
  refine ⟨div_nonneg (pow_nonneg hv.1.le _) hr.le,(div_le_iff₀ hr).mpr ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left (hw.1.trans (hw.2.1.trans hw.2.2.1)) hv.1.le]

/-- At each actual interior coordinate, the normalized positive mass integrand strictly increases with shape.
Use: proves strict order of the true mass quadrature through tau=1 without differentiating at that endpoint.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the true inverse-square-root derivative is psi times itself,
and psi and the coordinate square are strictly positive. Apply the
mean value strict-monotonicity theorem on the closed physical interval. -/
theorem massWeight_shape_strictMono {c v : ℝ} (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) : StrictMonoOn (fun t => quadratureWeight t c v) (Icc (0:ℝ) 1) := by
  -- Every derivative is the ordinary derivative of the original positive integrand.
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun u => quadratureWeight u c v)
        (v^2*(psi t c v*(sqrt (P t c v))⁻¹)) t := by
    simpa only [quadratureWeight,div_eq_mul_inv] using
      (inverse_sqrt_shape_hasDerivAt ht hc hv).const_mul (v^2)
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  exact mul_pos (sq_pos_of_pos hv.1) (mul_pos
    (psi_pos (interior_subset ht) hc ⟨hv.1,hv.2.le⟩)
    (inv_pos.mpr (sqrt_pos.mpr (P_pos (interior_subset ht) hc hv))))

/-- At each interior coordinate, chi times the original positive mass weight strictly increases with chi.
Use: proves a unique determinant parameter for any fixed shape and positive mass.
Article: jacobi, Theorem D.7.
Proof: the exact derivative is (1-chi*tau*v³/(2*r))*weight. Since
chi*tau*v³<=r, its first factor is at least one half and the actual weight is positive. -/
theorem massWeight_parameter_strictMono {t v : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) : StrictMonoOn (fun c => c*quadratureWeight t c v) (Icc (0:ℝ) 1) := by
  -- The positive base polynomial prevents a spurious zero derivative at either physical endpoint.
  have hd (c : ℝ) (hc : c∈Icc (0:ℝ) 1) :
      HasDerivAt (fun u => u*quadratureWeight t u v)
        ((1-c*t/2*(v^3/r t c v))*quadratureWeight t c v) c := by
    have hw := (inverse_sqrt_fredholm_hasDerivAt ht hc hv).const_mul (v^2)
    convert (hasDerivAt_id c).mul hw using 1
    · funext u
      dsimp [quadratureWeight]
      ring
    · dsimp [quadratureWeight]
      ring
  have hpos (c : ℝ) (hc : c∈Icc (0:ℝ) 1) :
      0<(1-c*t/2*(v^3/r t c v))*quadratureWeight t c v := by
    have hh := h_bounds ht hc hv
    have hct : 0≤c*t ∧ c*t≤1 := ⟨mul_nonneg hc.1 ht.1,
      (mul_le_mul hc.2 ht.2 ht.1 (by norm_num)).trans_eq (one_mul 1)⟩
    have hprod : c*t*(v^3/r t c v)≤1 :=
      (mul_le_mul_of_nonneg_left (hh.2.trans hv.2.le) hct.1).trans (by simpa only [mul_one] using hct.2)
    exact mul_pos (by nlinarith) (div_pos (sq_pos_of_pos hv.1) (sqrt_pos.mpr (P_pos ht hc hv)))
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (fun c hc => (hd c hc).continuousAt.continuousWithinAt)
  intro c hc
  rw [(hd c (interior_subset hc)).deriv]
  exact hpos c (interior_subset hc)

/-- The genuine normalized Fredholm mass strictly increases with shape at every positive determinant parameter.
Use: makes the true constant-mass branch ordered and prevents disconnected root ambiguities.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the integrable difference of the two original positive weights is
strictly positive throughout (0,1); its integral is therefore positive.
Multiply by the positive mass coefficient. -/
theorem mass_shape_strictMono {c : ℝ} (hc : c∈Ioc (0:ℝ) 1) :
    StrictMonoOn (fun t => mass t c) (Icc (0:ℝ) 1) := by
  -- Strict integral positivity retains comparisons involving tau=0 and tau=1.
  intro t ht u hu htu
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2⟩
  have hi := (quadratureWeight_integrable hu hc').sub (quadratureWeight_integrable ht hc')
  have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun v hv => sub_pos.mpr (massWeight_shape_strictMono hc' hv ht hu htu))
    (by norm_num : (0:ℝ)<1)
  rw [intervalIntegral.integral_sub (quadratureWeight_integrable hu hc') (quadratureWeight_integrable ht hc')] at hp
  exact mul_lt_mul_of_pos_left (sub_pos.mp hp) (mul_pos (by norm_num) hc.1)

/-- The genuine normalized Fredholm mass strictly increases with its determinant parameter, including zero.
Use: the constant-mass equation has at most one chi at each shape, with its correct zero-amplitude endpoint.
Article: jacobi, Theorem D.7.
Proof: the difference of the original chi-weighted integrands is
integrable and strictly positive throughout (0,1); integrate and restore
the exact coefficient three halves. -/
theorem mass_parameter_strictMono {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    StrictMonoOn (mass t) (Icc (0:ℝ) 1) := by
  -- The parameter coefficient is kept inside the integrand before comparing different chi values.
  intro c hc k hk hck
  have hi := ((quadratureWeight_integrable ht hk).const_mul k).sub
    ((quadratureWeight_integrable ht hc).const_mul c)
  have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun v hv => sub_pos.mpr (massWeight_parameter_strictMono ht hv hc hk hck))
    (by norm_num : (0:ℝ)<1)
  rw [intervalIntegral.integral_sub ((quadratureWeight_integrable ht hk).const_mul k)
      ((quadratureWeight_integrable ht hc).const_mul c),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hp
  unfold mass i2
  nlinarith [hp]

end
end jacobi.Fredholm
