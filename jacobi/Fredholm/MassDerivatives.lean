import jacobi.Fredholm.WeightedMeans

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Both printed mass partial derivatives are genuine derivatives of the
original normalized integral, with strictly positive values. The ordinary
chi derivative includes the physical full-support endpoint tau=1.
Source: dominated state-quadrature differentiation and positive weight comparisons.
Use: proves a quantitative positive lower bound for the mass parameter derivative.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The true positive second determinant response is bounded above by the original second state moment.
Use: proves a quantitative positive lower bound for the mass parameter derivative.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: h lies between zero and one, so compare the convergent actual integrands. -/
theorem response2_bounds {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    0≤response2 t c ∧ response2 t c≤ i2 t c := by
  -- The coefficient is bounded before integration; no derivative sign is assumed.
  have hi := (response_integrable ht hc).1
  constructor
  · rw [response2,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact mul_nonneg (h_bounds ht hc hv).1 (quadratureWeight_bound ht hc hv).1
  · exact intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
      hi (quadratureWeight_integrable ht hc) (fun v hv =>
        (mul_le_mul_of_nonneg_right ((h_bounds ht hc hv).2.trans hv.2.le)
          (quadratureWeight_bound ht hc hv).1).trans_eq (one_mul _))

/-- The original mass has a genuine strictly positive interior shape derivative.
Use: justifies the shape direction in the constant-mass implicit-function construction.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the already proved actual i2 derivative is multiplied by its
positive mass coefficient; its integrable derivative weight is strictly positive on (0,1). -/
theorem mass_shape_hasDerivAt_pos {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioc (0:ℝ) 1) :
    HasDerivAt (fun u => mass u c) ((3/2:ℝ)*c*shape2 t c) t ∧
      0<(3/2:ℝ)*c*shape2 t c := by
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2⟩
  have hp : 0<shape2 t c := intervalIntegral.intervalIntegral_pos_of_pos_on
    (shape_integrable ht' hc').1 (fun v hv => mul_pos
      (psi_pos ht' hc' ⟨hv.1,hv.2.le⟩)
      (div_pos (sq_pos_of_pos hv.1) (sqrt_pos.mpr (P_pos ht' hc' hv)))) (by norm_num)
  exact ⟨((shape_calculus ht hc').1.const_mul ((3/2:ℝ)*c)),
    mul_pos (mul_pos (by norm_num) hc.1) hp⟩

/-- The original mass has a genuine strictly positive determinant-parameter derivative, including full support.
Use: proves actual constraint qualification of the printed constant-mass parameter curve.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the actual product (3/2)*chi*I2. The response term
has magnitude at most (3/4)*chi*tau*I2, while chi*tau<=1; a positive
multiple of the true positive I2 therefore remains. -/
theorem mass_parameter_hasDerivAt_pos {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ∃ D : ℝ,HasDerivAt (mass t) D c ∧ 0<D := by
  -- The signed response is the exact derivative of the original convergent i2 integral.
  have hi := (parameter_calculus ht hc).1
  have h := ((hasDerivAt_id c).const_mul (3/2:ℝ)).mul hi
  refine ⟨_,h,?_⟩
  have hb := response2_bounds ht ⟨hc.1.le,hc.2.le⟩
  have hi0 := i2_pos ht ⟨hc.1.le,hc.2.le⟩
  have hcoef : 0≤c*t ∧ c*t≤1 := ⟨mul_nonneg hc.1.le ht.1,
    (mul_le_mul hc.2.le ht.2 ht.1 (by norm_num)).trans_eq (one_mul 1)⟩
  have hprod : c*t*response2 t c≤ i2 t c :=
    (mul_le_mul_of_nonneg_left hb.2 hcoef.1).trans
      ((mul_le_mul_of_nonneg_right hcoef.2 hi0.le).trans_eq (one_mul _))
  norm_num only [one_mul,id_eq]
  nlinarith

end
end jacobi.Fredholm
