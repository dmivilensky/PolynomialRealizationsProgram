import jacobi.Fredholm.Jacobian
import jacobi.Fredholm.Quadratures

/-!
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
The original attained optimizer, not an independently prescribed profile,
has the printed mass and energy integrals. The amplitude is fixed by its
actual central turning equation, and the proved spatial Jacobian evaluates
the positive-part powers of its true affine Green coordinate.
Source: the actual optimizing first integral and Lebesgue substitution.
Use: converts all original density observables into genuine normalized Green quadratures.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The original Fredholm optimizing density has the exact printed normalized positive-part-square formula.
Use: converts all original density observables into genuine normalized Green quadratures.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: factor the positive central switching gap out of the actual Euler
positive part; the true normalized amplitude square is 3*chi/tau.
Cancel the strictly positive coupling only after this exact identity. -/
theorem Optimizer.normalized_density {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    P.density.value x=(3*P.chi hs/(2*s*P.tau hs))*(max (P.coordinate hs x) 0)^2 := by
  -- The normalization retains the genuine optimizing density at every point, including its boundary.
  have hparams := P.parameters hs
  have hd := sub_pos.mpr (P.shape hs).1
  have hinv := (P.inverse_parameters hs).2.2
  have hsq : P.A^2*(P.g hs.le 0-P.edge)^2=3*P.chi hs/P.tau hs := by
    rw [← P.amplitude_eq hs]
    unfold amplitude
    rw [div_pow,sq_sqrt (div_pos (mul_pos (by norm_num) hparams.2.1) hparams.1.1).le,hinv]
    field_simp [hd.ne']
  have hformula := P.density_formula hs x
  have hgap : P.g hs.le x-P.edge=(P.g hs.le 0-P.edge)*P.coordinate hs x := by
    have hh := P.coordinate_affine hs x
    linarith
  rw [hgap,show max ((P.g hs.le 0-P.edge)*P.coordinate hs x) 0=
    (P.g hs.le 0-P.edge)*max (P.coordinate hs x) 0 by
      rw [mul_max_of_nonneg _ _ hd.le,mul_zero],mul_pow,← mul_assoc,hsq] at hformula
  field_simp [hs.ne',hparams.1.1.ne'] at hformula ⊢
  nlinarith [hformula]

/-- Positive integer powers of the genuine optimizing coordinate have the literal unit-interval quadratures.
Use: specializes a single actual substitution to the original mass, energy and root mass.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: the clipped power vanishes throughout the nonpositive-coordinate
tail. Apply the proved whole-line observable substitution and remove
the clipping on the strictly positive target integration interval. -/
theorem Optimizer.power_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (k : ℕ) (hk : 0<k) :
    (∫ x,(max (P.coordinate hs x) 0)^k)=P.tau hs*
      (∫ v in (0:ℝ)..1,v^k/sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) v)) := by
  -- The endpoint representatives do not enter the true Lebesgue change of variables.
  rw [P.quadrature hs (fun v => (max v 0)^k)
    (fun v hv => by rw [max_eq_right hv,zero_pow (Nat.ne_of_gt hk)])]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun v hv => by rw [max_eq_left hv.1.le]

/-- The original actual optimizer mass equals its precise printed normalized quadrature.
Use: the active mass constraint becomes mass(tau,chi)=s*M without a new profile assumption.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: substitute the actual normalized density, pull out its constant
amplitude and evaluate the true coordinate square by its proved Jacobian. -/
theorem Optimizer.mass_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    s*P.density.mass=mass (P.tau hs) (P.chi hs) := by
  -- Evaluate the same original density by the true coordinate-square substitution.
  have hm : P.density.mass=(3*P.chi hs/(2*s*P.tau hs))*
      (∫ x,(max (P.coordinate hs x) 0)^2) := by
    change (∫ x,P.density.value x)=_
    simp_rw [P.normalized_density hs]
    exact integral_const_mul _ _
  rw [hm,P.power_quadrature hs 2 (by decide)]
  change s*(3*P.chi hs/(2*s*P.tau hs)*(P.tau hs*i2 (P.tau hs) (P.chi hs)))=_
  unfold mass
  field_simp [hs.ne',(P.parameters hs).1.1.ne']

/-- The genuine Fredholm optimizer's objective has its literal normalized cubic Green quadrature.
Use: evaluates the actual attained objective before simplifying its positive square-root normalization.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: the square root of the actual nonnegative positive-part-square
density is sqrt(amplitude)*v_+. Its cube is the original energy integrand.
The true coordinate-cube substitution then evaluates its real integral. -/
theorem Optimizer.energy_quadrature_raw {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.density.energy=(sqrt (3*P.chi hs/(2*s*P.tau hs)))^3*P.tau hs*i3 (P.tau hs) (P.chi hs) := by
  -- The original finite energy is used directly, so no junk integral can supply an objective value.
  have hp := P.parameters hs
  have ht0 := hp.1.1
  have hc0 := hp.2.1
  have hC : 0≤3*P.chi hs/(2*s*P.tau hs) := by positivity
  have he : P.density.energy=(sqrt (3*P.chi hs/(2*s*P.tau hs)))^3*
      (∫ x,(max (P.coordinate hs x) 0)^3) := by
    change (∫ x,(P.density.value x)^(3/2:ℝ))=_
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [P.normalized_density hs x,Real.rpow_div_two_eq_sqrt 3 (mul_nonneg hC (sq_nonneg _)),
        Real.rpow_ofNat,Real.sqrt_mul hC,Real.sqrt_sq (le_max_right _ _),mul_pow]
  rw [he,P.power_quadrature hs 3 (by decide)]
  simp only [mul_assoc]
  congr 1
  congr 1
  unfold i3 quadratureWeight
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun v _ => by ring

/-- The actual Fredholm objective equals the printed normalized energy with its exact coupling scale.
Use: converts the original optimizing cost into the source's two-parameter minimum value.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: all square-root arguments are positive. Their multiplicative
identities reduce the raw genuine cubic quadrature to (3*chi)^(3/2)/sqrt(tau). -/
theorem Optimizer.energy_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    (2*s)^(3/2:ℝ)*P.density.energy=energy (P.tau hs) (P.chi hs) := by
  -- Positive real square roots fix every fractional-power sign in the printed normalization.
  have hp := P.parameters hs
  have ht0 := hp.1.1
  have hc0 := hp.2.1
  have ht : 0<sqrt (P.tau hs) := sqrt_pos.mpr hp.1.1
  have hsqrt : 0<sqrt (2*s) := sqrt_pos.mpr (by positivity)
  have hst := sq_sqrt hp.1.1.le
  rw [P.energy_quadrature_raw hs,energy,Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤2*s),
    Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤3*P.chi hs),Real.rpow_ofNat,Real.rpow_ofNat,
    Real.sqrt_div (by positivity : 0≤3*P.chi hs),Real.sqrt_mul (by positivity : 0≤2*s)]
  field_simp [ht.ne',hsqrt.ne']
  rw [hst]

end
end jacobi.Fredholm
