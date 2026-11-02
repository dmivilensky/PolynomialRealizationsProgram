import jacobi.Trichotomy.SubcriticalGap

/-!
Article: jacobi, Proposition C.4.
The original profile power and the actual endpoint-gap power determine
the exact printed compact-tail exponent and coefficient, with the same
positive spectral c_alpha and the same genuine finite support radius.
Use: subcritical_density_power_limit and the actual finite-end inverse transfer give the original compact density tail, including its coefficient.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The exact printed compact density power exponent in the source normalization.
Use: subcritical_density_power_limit and the actual finite-end inverse transfer give the original compact density tail, including its coefficient.
Article: jacobi, Proposition C.4.
-/
def compactDensityExponent (a : ℝ) : ℝ := 4*gamma a/(1-2*gamma a)

/-- The exact printed positive compact density coefficient in terms of the original spectral endpoint constant.
Use: the compact tail theorem identifies the true density coefficient with the source C_alpha, rather than an unspecified positive multiple.
Article: jacobi, Proposition C.4.
-/
def compactDensityCoefficient (a : ℝ) (ha : -1<a) : ℝ :=
  (endpointConstant a ha)^2*(endpointConstant a ha*(1-2*gamma a))^(compactDensityExponent a)

/-- The squared actual original profile divided by the genuine endpoint gap to the printed power tends to exactly the original compact density coefficient.
Use: the finite-end inverse-coordinate transfer identifies the source's literal m_alpha(x) asymptotic with its exact C_alpha.
Article: jacobi, Proposition C.4.
Proof: divide the squared genuine profile power asymptotic by the printed power of the genuine positive gap asymptotic. Their physical powers agree exactly because (1-2*gamma)*q=4*gamma. The true positive gap limit permits the continuous real power, and the source coefficient follows by the inverse real-power identity. -/
theorem subcritical_density_power_limit {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => (physicalProfile a ha t)^2/(packingGap a ha t)^(compactDensityExponent a))
      (𝓝[>] (0:ℝ)) (𝓝 (compactDensityCoefficient a ha)) := by
  -- Both asymptotics are for the original source functions and keep the same spectral c_alpha throughout.
  have hp : 0<1-2*gamma a := by dsimp only [gamma]; linarith
  have hc := endpointConstant_pos a ha hs
  have hb : 0<1/(endpointConstant a ha*(1-2*gamma a)) := one_div_pos.mpr (mul_pos hc hp)
  have hpow := (subcritical_gap_limit ha hs).rpow_const (p := compactDensityExponent a) (Or.inl hb.ne')
  have h := ((physicalProfile_subcritical_limit ha hs).pow 2).div hpow
    (Real.rpow_pos_of_pos hb _).ne'
  have hvalue : (endpointConstant a ha)^2/(1/(endpointConstant a ha*(1-2*gamma a)))^(compactDensityExponent a)=
      compactDensityCoefficient a ha := by
    rw [compactDensityCoefficient,one_div,Real.inv_rpow (mul_nonneg hc.le hp.le),div_inv_eq_mul]
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
  have hg : 0≤packingGap a ha t :=
    intervalIntegral.integral_nonneg_of_forall (μ := volume) ht.1.le (physicalProfile_reciprocal_nonneg a ha)
  have hq : (1-2*gamma a)*compactDensityExponent a=4*gamma a := by
    dsimp only [compactDensityExponent]
    field_simp [hp.ne']
  have he2 : (t^(2*gamma a))^2=t^(4*gamma a) := by
    rw [← Real.rpow_mul_natCast ht.1.le]
    congr 1
    ring
  dsimp only [Pi.div_apply]
  rw [div_pow,Real.div_rpow hg (Real.rpow_nonneg ht.1.le _) _,← Real.rpow_mul ht.1.le,hq,he2]
  field_simp [(Real.rpow_pos_of_pos ht.1 (4*gamma a)).ne']

end
end jacobi.Trichotomy
