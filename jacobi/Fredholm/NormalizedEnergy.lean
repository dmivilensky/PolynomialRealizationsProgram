import jacobi.Fredholm.ShapeRatio
import jacobi.Fredholm.MassDerivatives

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The original energy factors exactly into the mass scale and the actual
shape ratio. Its determinant-parameter monotonicity follows from the
proved logarithmic derivative sign and the strict mass increase.
Source: positive real-power algebra and the verified actual parameter derivatives.
Use: energy and logarithm order comparisons multiply only by positive factors.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The actual printed shape ratio is positive on the whole nonzero physical parameter domain.
Use: energy and logarithm order comparisons multiply only by positive factors.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: I3, I2 and tau are strictly positive by the actual integral bounds. -/
theorem shapeRatio_pos {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    0<shapeRatio t c :=
  div_pos (state_mean_bounds ⟨ht.1.le,ht.2⟩ hc).1
    (mul_pos (sqrt_pos.mpr ht.1) (rpow_pos_of_pos (i2_pos ⟨ht.1.le,ht.2⟩ hc) _))

/-- The literal normalized energy has exactly the mass-and-shape factorization used in the source.
Use: reduces constant-mass energy comparisons to the actual shape-ratio comparison.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use the positive square-root form of the two three-halves powers,
factor sqrt(3*chi*I2), and cancel the actual positive sqrt(I2) cube. -/
theorem energy_mass_shape {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioc (0:ℝ) 1) :
    energy t c=(2*mass t c)^(3/2:ℝ)*shapeRatio t c := by
  -- The actual positive mass moment fixes the fractional-power branch exactly.
  have hi := i2_pos ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2⟩
  have hc0 := hc.1
  have ht0 := ht.1
  have hm : 2*mass t c=3*c*i2 t c := by unfold mass; ring
  rw [hm,energy,shapeRatio,Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤3*c*i2 t c),
    Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤3*c),
    Real.rpow_div_two_eq_sqrt 3 hi.le,Real.rpow_ofNat,Real.rpow_ofNat,Real.rpow_ofNat,
    sqrt_mul (by positivity : 0≤3*c),mul_pow]
  field_simp [(sqrt_pos.mpr hi).ne',(sqrt_pos.mpr ht.1).ne']

/-- The genuine shape ratio is nondecreasing in the determinant parameter for every fixed physical shape.
Use: together with strict mass growth this gives strict energy growth, including the free branch tau=1.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the proved ordinary logarithmic derivative is nonnegative on the
open chi interval. Mean-value monotonicity and positivity of the original
ratio convert logarithm order to the actual ratio order. -/
theorem shapeRatio_parameter_monotone {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) :
    MonotoneOn (shapeRatio t) (Ioo (0:ℝ) 1) := by
  -- All mean-value hypotheses are discharged by the genuine dominated derivatives.
  have hlog : MonotoneOn (fun c => log (shapeRatio t c)) (Ioo (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · intro c hc
      obtain ⟨D,hD,_⟩ := logShape_parameter_hasDerivAt_nonneg ht hc
      exact hD.continuousAt.continuousWithinAt
    · intro c hc
      obtain ⟨D,hD,_⟩ := logShape_parameter_hasDerivAt_nonneg ht (interior_subset hc)
      exact hD.differentiableAt.differentiableWithinAt
    · intro c hc
      obtain ⟨D,hD,hpos⟩ := logShape_parameter_hasDerivAt_nonneg ht (interior_subset hc)
      rwa [hD.deriv]
  intro c hc k hk hck
  exact (log_le_log_iff (shapeRatio_pos ht ⟨hc.1.le,hc.2.le⟩)
    (shapeRatio_pos ht ⟨hk.1.le,hk.2.le⟩)).mp (hlog hc hk hck)

/-- The actual normalized objective strictly increases with chi at every fixed positive shape, including full support.
Use: the free-branch determinant monotonicity follows from the envelope identity once that identity is proved.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the mass factor strictly increases by the actual mass theorem;
the positive shape factor is nondecreasing. Multiply the two genuine
comparisons using the exact energy factorization. -/
theorem energy_parameter_strictMono {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) :
    StrictMonoOn (energy t) (Ioo (0:ℝ) 1) := by
  -- This comparison is already valid on every fixed-shape branch, rather than only tau=1.
  intro c hc k hk hck
  have hc' : c∈Ioc (0:ℝ) 1 := ⟨hc.1,hc.2.le⟩
  have hk' : k∈Ioc (0:ℝ) 1 := ⟨hk.1,hk.2.le⟩
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  rw [energy_mass_shape ht hc',energy_mass_shape ht hk']
  have hm := mass_parameter_strictMono ht' ⟨hc.1.le,hc.2.le⟩ ⟨hk.1.le,hk.2.le⟩ hck
  have hmc := mass_pos ht' hc'
  have hpow := Real.rpow_lt_rpow (by positivity : 0≤2*mass t c)
    (mul_lt_mul_of_pos_left hm (by norm_num : (0:ℝ)<2)) (by norm_num : (0:ℝ)<3/2)
  have hpsi := shapeRatio_parameter_monotone ht hc hk hck.le
  exact (mul_lt_mul_of_pos_right hpow (shapeRatio_pos ht ⟨hc.1.le,hc.2.le⟩)).trans_le
    (mul_le_mul_of_nonneg_left hpsi (rpow_nonneg (by
      have hh := mass_pos ht' hk'
      positivity : 0≤2*mass t k) _))

/-- The actual shape ratio strictly decreases with the interior shape parameter at each fixed determinant parameter.
Use: compares energies on the genuine constant-mass set without assuming a differentiable graph in advance.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the proved strictly negative logarithmic derivative gives strict
mean-value decrease; positivity transfers this order to the original ratio. -/
theorem shapeRatio_shape_strictAnti {c : ℝ} (hc : c∈Icc (0:ℝ) 1) :
    StrictAntiOn (fun t => shapeRatio t c) (Ioo (0:ℝ) 1) := by
  -- The mean-value theorem uses only the actual open physical shape interval.
  have hlog : StrictAntiOn (fun t => log (shapeRatio t c)) (Ioo (0:ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
    · intro t ht
      obtain ⟨D,hD,_⟩ := logShape_shape_hasDerivAt_neg ht hc
      exact hD.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨D,hD,hneg⟩ := logShape_shape_hasDerivAt_neg (interior_subset ht) hc
      rwa [hD.deriv]
  intro t ht u hu htu
  exact (log_lt_log_iff (shapeRatio_pos ⟨hu.1,hu.2.le⟩ hc)
    (shapeRatio_pos ⟨ht.1,ht.2.le⟩ hc)).mp (hlog ht hu htu)

/-- Equal normalized masses at increasing shape parameters force a strictly decreasing determinant parameter.
Use: orders the true constant-mass set globally before the envelope and parameter uniqueness argument.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: if chi did not decrease, strict shape growth followed by mass
monotonicity in chi would contradict equality of the two actual masses. -/
theorem mass_level_parameter_order {t u c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htu : t<u) (hm : mass t c=mass u k) : k<c := by
  have hshape := mass_shape_strictMono ⟨hk.1,hk.2.le⟩ ⟨ht.1.le,ht.2.le⟩ ⟨hu.1.le,hu.2.le⟩ htu
  by_contra! hck
  have hparam := (mass_parameter_strictMono ⟨ht.1.le,ht.2.le⟩).monotoneOn
    ⟨hc.1.le,hc.2.le⟩ ⟨hk.1.le,hk.2.le⟩ hck
  linarith

/-- The actual normalized energy strictly decreases along the entire interior constant-mass set.
Use: the envelope identity can convert this global ordering into uniqueness of the determinant equation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: mass order forces chi to decrease. The true shape ratio strictly
decreases in tau and is nondecreasing in chi, so both changes reduce it.
The original equal positive mass scales cancel in the exact energy factorization. -/
theorem energy_mass_level_order {t u c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htu : t<u) (hm : mass t c=mass u k) : energy u k<energy t c := by
  -- Both points use the same actual normalized mass, so no putative mass curve is assumed.
  have hkc := mass_level_parameter_order ht hu hc hk htu hm
  have hshape := shapeRatio_shape_strictAnti ⟨hk.1.le,hk.2.le⟩ ht hu htu
  have hparam := shapeRatio_parameter_monotone ⟨ht.1,ht.2.le⟩ hk hc hkc.le
  rw [energy_mass_shape ⟨hu.1,hu.2.le⟩ ⟨hk.1,hk.2.le⟩,
    energy_mass_shape ⟨ht.1,ht.2.le⟩ ⟨hc.1,hc.2.le⟩,← hm]
  have hm0 := mass_pos ⟨ht.1.le,ht.2.le⟩ ⟨hc.1,hc.2.le⟩
  exact mul_lt_mul_of_pos_left (hshape.trans_le hparam) (rpow_pos_of_pos (by positivity : 0<2*mass t c) _)

end
end jacobi.Fredholm
