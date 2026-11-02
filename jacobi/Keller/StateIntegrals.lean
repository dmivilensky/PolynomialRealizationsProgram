import jacobi.Keller.Jacobian
import jacobi.Keller.Parameter

/-!
Article: jacobi, Theorem D.6.
Mass, energy and root mass of the original attained optimizer are evaluated
by the proved actual Jacobian. The printed j_k are genuine convergent
integrals. Root-mass convergence is proved from the strictly positive
computed integral, so its extended-real value cannot hide a junk integral.
Source: the genuine optimizing change of variables and positive real square-root algebra.
Use: a single actual substitution gives the mass, objective and root-mass formulas.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- All positive root powers of the actual Euler density have their genuine j_k quadratures.
Use: a single actual substitution gives the mass, objective and root-mass formulas.
Article: jacobi, Theorem D.6.
Proof: specialize the proved observable change of variables; on (0,1),
sqrt(D*(1-v²)²)=sqrt(D)*(1-v²). Pull out its constant power. -/
theorem Profile.root_power_quadrature (p : Profile m ell M) (hell : 0<ell)
    {k : ℕ} (hk : 0<k) :
    (∫ x,(sqrt (p.rho x))^k)=
      (2/sqrt p.shape)*(sqrt ((3*ell/2)*p.shape))^k*j k p.shape := by
  -- The endpoint representatives are irrelevant; the equality is pointwise on the open integration interval.
  rw [p.quadrature hell (fun r => (sqrt r)^k) (by simp [Nat.ne_of_gt hk])]
  have hD : 0<(3*ell/2)*p.shape := mul_pos (by positivity) (zero_lt_one.trans_le (p.shape_ge_one hell))
  have hi : (∫ v in (0:ℝ)..1,
      (sqrt ((3*ell/2)*p.shape*(1-v^2)^2))^k/sqrt ((1-v^2/p.shape)*(p.shape*A v-1)))=
      (sqrt ((3*ell/2)*p.shape))^k*j k p.shape := by
    rw [j,← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
    dsimp only []
    rw [sqrt_mul hD.le,sqrt_sq (sub_pos.mpr hv2).le,mul_pow]
    ring
  rw [hi]
  ring

/-- The original actual optimizer has exactly the source's mass quadrature.
Use: determines the genuine mass equation in the active branch and the mass threshold in the free branch.
Article: jacobi, Theorem D.6.
Proof: transfer the original a.e. density to its nonnegative representative,
apply the proved root-square quadrature, and simplify the positive square roots. -/
theorem Profile.mass_quadrature (p : Profile m ell M) (hell : 0<ell) :
    m.mass=3*ell*massCurve p.shape := by
  -- Both integrals refer to the same original optimizer; its a.e. representative is used only for evaluation.
  have hi := p.root_power_quadrature hell (by decide : 0<2)
  have hn (x : ℝ) : 0≤p.rho x := mul_nonneg p.b_pos.le (sq_nonneg _)
  simp_rw [sq_sqrt (hn _)] at hi
  have hm : m.mass=∫ x,p.rho x := integral_congr_ae p.density
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  rw [hm,hi,sq_sqrt (mul_nonneg (by positivity : 0≤3*ell/2) hc.le),massCurve]
  have hs := sq_sqrt (zero_lt_one.trans_le (p.shape_ge_one hell)).le
  have hp := sqrt_pos.mpr (zero_lt_one.trans_le (p.shape_ge_one hell))
  field_simp
  nlinarith [congrArg (fun r : ℝ => r*j 2 p.shape) hs]

/-- The original actual optimizer has exactly the source's objective-energy quadrature.
Use: evaluates the attained variational infimum after the unique mass parameter is fixed.
Article: jacobi, Theorem D.6.
Proof: write the actual energy as the cube of its positive square root,
apply the proved root-cube substitution, and cancel sqrt(c) using its positive square. -/
theorem Profile.energy_quadrature (p : Profile m ell M) (hell : 0<ell) :
    m.energy=2*(3*ell/2)^(3/2:ℝ)*p.shape*j 3 p.shape := by
  -- The objective normalization is derived from the literal real integral, not an extended-real surrogate.
  have he : m.energy=∫ x,(sqrt (p.rho x))^3 := by
    apply integral_congr_ae
    filter_upwards [p.density] with x hx
    rw [hx,Real.rpow_div_two_eq_sqrt 3 (mul_nonneg p.b_pos.le (sq_nonneg _)),Real.rpow_ofNat]
    rfl
  rw [he,p.root_power_quadrature hell (by decide : 0<3),sqrt_mul (by positivity : 0≤3*ell/2),
    Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤3*ell/2),Real.rpow_ofNat]
  have hs := sq_sqrt (zero_lt_one.trans_le (p.shape_ge_one hell)).le
  have hp := sqrt_pos.mpr (zero_lt_one.trans_le (p.shape_ge_one hell))
  field_simp
  nlinarith [congrArg (fun r : ℝ => r*j 3 p.shape) hs]

/-- The genuine root-mass integral of the original optimizing density is finite and has its exact j_1 value.
Use: supplies the source's additional root-mass formula and rules out Bochner junk-value reasoning.
Article: jacobi, Theorem D.6.
Proof: the actual root-power substitution computes the real integral.
Its value is strictly positive because the printed j_1 is strictly positive;
a nonzero real integral implies integrability of that very function. -/
theorem Profile.root_integral (p : Profile m ell M) (hell : 0<ell) :
    Integrable (fun x => sqrt (m.value x)) ∧
      (∫ x,sqrt (m.value x))=2*sqrt (3*ell/2)*j 1 p.shape := by
  -- The convergence conclusion is recovered before converting to the extended root mass.
  have hi := p.root_power_quadrature hell (by decide : 0<1)
  simp only [pow_one] at hi
  have hm : (∫ x,sqrt (m.value x))=∫ x,sqrt (p.rho x) :=
    integral_congr_ae (p.density.fun_comp sqrt)
  have hs : 0<sqrt p.shape := sqrt_pos.mpr (zero_lt_one.trans_le (p.shape_ge_one hell))
  have hv : (∫ x,sqrt (m.value x))=2*sqrt (3*ell/2)*j 1 p.shape := by
    rw [hm,hi,sqrt_mul (by positivity : 0≤3*ell/2)]
    field_simp [hs.ne']
  have hp : 0<2*sqrt (3*ell/2)*j 1 p.shape :=
    mul_pos (mul_pos (by norm_num) (sqrt_pos.mpr (by positivity)))
      (j_pos (by decide : 1≤1) (p.shape_ge_one hell))
  exact ⟨Integrable.of_integral_ne_zero (hv ▸ hp.ne'),hv⟩

/-- The original optimizer's extended root mass is the ofReal of its actual finite printed quadrature.
Use: connects the Keller calibration to the root-mass hierarchy without any extra convergence premise.
Article: jacobi, Theorem D.6.
Proof: the proved integrability identifies the nonnegative lintegral with ofReal of its real integral. -/
theorem Profile.rootMass_quadrature (p : Profile m ell M) (hell : 0<ell) :
    m.rootMass=ENNReal.ofReal (2*sqrt (3*ell/2)*j 1 p.shape) := by
  obtain ⟨hi,hv⟩ := p.root_integral hell
  rw [Density.rootMass,← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => sqrt_nonneg _),hv]

end
end jacobi.Keller
