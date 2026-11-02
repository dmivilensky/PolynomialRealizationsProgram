import jacobi.Support.GroundVolterra

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The actual ground-normalized nested Volterra problem has the genuine
reference core as its unique continuous regular solution, at every
complex energy. Integrability at the singular corner, subtraction of
actual operator values, and uniqueness are all proved. NormalizedMeshLimit
passes the actual finite nested operator to this continuum operator;
NormalizedEdge then proves convergence of the original complex waves.
The single-integral Cauchy-kernel representation is a separate identity.
Use: groundVolterra_sub subtracts actual nested operator values using the ordinary integral subtraction theorem, with all integrability premises discharged.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The original ground-normalized inner primitive is genuinely integrable through the singular corner for every continuous regular factor.
Use: groundVolterra_sub subtracts actual nested operator values using the ordinary integral subtraction theorem, with all integrability premises discharged.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the weighted inner primitive is continuous on the full closed interval. Its ground-square quotient is continuous away from zero, hence measurable on the actual integration interval. The proved ground-primitive bound and monotonicity of the norm primitive dominate it by one integrable constant on that finite interval. -/
theorem groundFlux_intervalIntegrable {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} {t:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (hq:ContinuousOn q (Icc 0 t)) :
    IntervalIntegrable (groundFlux a q) volume 0 t := by
  -- Measurability away from zero and an actual finite constant majorant suffice at the original singular corner.
  let g (s:ℝ) := (weight a s:ℂ)^2*q s
  have hw : Continuous (fun s:ℝ => (weight a s:ℂ)^2) :=
    (Complex.continuous_ofReal.comp (weight_properties ha).1).pow 2
  have hg : IntervalIntegrable g volume 0 t := (hw.continuousOn.mul hq).intervalIntegrable_of_Icc ht.1
  have hp : ContinuousOn (fun r:ℝ => ∫s in (0:ℝ)..r,g s) (Ioc 0 t) :=
    (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc).mono
      (by rw [uIcc_of_le ht.1]; exact Ioc_subset_Icc_self)
  have hflux : ContinuousOn (groundFlux a q) (Ioc 0 t) := hp.div hw.continuousOn (fun r hr =>
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (weight_pos a ⟨hr.1,by linarith [hr.2,ht.2]⟩).ne'))
  have hi : IntervalIntegrable (fun s:ℝ => ‖q s‖) volume 0 t := hq.norm.intervalIntegrable_of_Icc ht.1
  have hconst : Integrable (fun _:ℝ => ∫s in (0:ℝ)..t,‖q s‖) (volume.restrict (Ioc 0 t)) := integrable_const _
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
  apply hconst.mono' (hflux.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hqr : ContinuousOn q (Icc 0 r) := hq.mono (by intro s hs; exact ⟨hs.1,hs.2.trans hr.2⟩)
  exact (groundFlux_bound ha ⟨hr.1.le,hr.2.trans ht.2⟩ hqr).trans
    (intervalIntegral.integral_mono_interval le_rfl hr.1.le hr.2 (Eventually.of_forall (fun s => norm_nonneg (q s))) hi)

/-- The genuine original inner ground primitive respects subtraction of continuous regular factors.
Use: groundVolterra_sub and regularWave_unique reduce uniqueness of the inhomogeneous original continuum equation to the proved homogeneous Gronwall theorem.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: both original weighted continuous factors are integrable on the actual closed interval. Distribute the ground square through their difference, subtract the genuine inner integrals and divide by the common endpoint ground square. -/
theorem groundFlux_sub {a:ℝ} (ha:-1<a) {q r:ℝ→ℂ} {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hq:ContinuousOn q (Icc 0 t)) (hr:ContinuousOn r (Icc 0 t)) :
    groundFlux a (fun s => q s-r s) t=groundFlux a q t-groundFlux a r t := by
  -- Subtraction is applied only after both actual weighted inner integrals are proved convergent.
  have hw : Continuous (fun s:ℝ => (weight a s:ℂ)^2) :=
    (Complex.continuous_ofReal.comp (weight_properties ha).1).pow 2
  have hiq : IntervalIntegrable (fun s:ℝ => (weight a s:ℂ)^2*q s) volume 0 t :=
    (hw.continuousOn.mul hq).intervalIntegrable_of_Icc ht.1
  have hir : IntervalIntegrable (fun s:ℝ => (weight a s:ℂ)^2*r s) volume 0 t :=
    (hw.continuousOn.mul hr).intervalIntegrable_of_Icc ht.1
  unfold groundFlux
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hiq hir,sub_div]

/-- The actual normalized continuum Volterra operator respects subtraction on the full physical half-interval.
Use: regularWave_unique proves actual inhomogeneous uniqueness from the original homogeneous equation, without a formal integral-linearity premise.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: both genuine ground primitives are integrable through zero by the proved singular-corner estimate. Subtract their outer integrals and apply exact inner subtraction on every actual subinterval. -/
theorem groundVolterra_sub {a:ℝ} (ha:-1<a) {q r:ℝ→ℂ} {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hq:ContinuousOn q (Icc 0 t)) (hr:ContinuousOn r (Icc 0 t)) :
    groundVolterra a (fun s => q s-r s) t=groundVolterra a q t-groundVolterra a r t := by
  -- The original outer integrals have actual integrability, including the endpoint with zero ground state.
  unfold groundVolterra
  rw [← intervalIntegral.integral_sub (groundFlux_intervalIntegrable ha ht hq) (groundFlux_intervalIntegrable ha ht hr)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact groundFlux_sub ha ⟨hs.1,hs.2.trans ht.2⟩
    (hq.mono (by intro x hx; exact ⟨hx.1,hx.2.trans hs.2⟩))
    (hr.mono (by intro x hx; exact ⟨hx.1,hx.2.trans hs.2⟩))

/-- The actual arbitrary-energy reference core is continuous on the full original physical half-interval.
Use: regularWave_groundVolterra and regularWave_unique provide a genuine existing continuous solution of the original normalized continuum equation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the already proved actual core is analytic at every original physical point including zero, hence continuous on the entire closed half-interval. -/
theorem regularWave_continuous_half (a:ℝ) (z:ℂ) : ContinuousOn (regularWave a z) (Icc (0:ℝ) (1/2)) := by
  intro t ht
  exact (regularWave_analytic a z ⟨ht.1,by linarith [ht.2]⟩).continuousAt.continuousWithinAt

/-- The actual original regular reference core solves the genuine normalized ground Volterra equation at every complex energy and every physical half-interval point.
Use: regularWave_unique identifies arbitrary continuous candidates with this original reference solution; the finite support edge limit compares against this actual normalized continuum equation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: use the already proved actual nested Green integral identity. Substitute the exact original ground-state factorization inside the genuine inner integral and factor the constant complex energy displacement from the actual outer integral. -/
theorem regularWave_groundVolterra {a:ℝ} (ha:-1<a) (z:ℂ) {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    regularWave a z t=1+((eigenvalue a 0:ℂ)-z)*groundVolterra a (regularWave a z) t := by
  -- The true arbitrary-energy solution, rather than an independently specified Volterra candidate, supplies this equation.
  rw [regularWave_volterra ha z ⟨ht.1,by linarith [ht.2]⟩,groundVolterra]
  congr 1
  have hi (r:ℝ) : (∫s in (0:ℝ)..r,(weight a s:ℂ)*solution a z s)=
      ∫s in (0:ℝ)..r,(weight a s:ℂ)^2*regularWave a z s := by
    apply intervalIntegral.integral_congr
    intro s _
    change (weight a s:ℂ)*solution a z s=(weight a s:ℂ)^2*regularWave a z s
    rw [solution_regularWave]
    ring
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  change ((eigenvalue a 0:ℂ)-z)*(∫s in (0:ℝ)..r,(weight a s:ℂ)*solution a z s)/(weight a r:ℂ)^2=_
  rw [hi r]
  dsimp [groundFlux]
  ring

/-- Every continuous regular solution of the original normalized continuum Volterra equation equals the actual reference core, at every complex energy.
Use: the finite support-chain continuum identification has a proved unique actual reference solution, without an unproved ODE or endpoint-normalization certificate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the actual reference core is a proved existing continuous solution. Subtract its equation from the arbitrary candidate's equation, using the actual integrability and exact subtraction of the normalized operator. The difference is a continuous homogeneous solution, so the independently proved original Gronwall argument forces it to vanish. -/
theorem regularWave_unique {a:ℝ} (ha:-1<a) (z:ℂ) {q:ℝ→ℂ}
    (hq:ContinuousOn q (Icc (0:ℝ) (1/2)))
    (he:∀t∈Icc (0:ℝ) (1/2),q t=1+((eigenvalue a 0:ℂ)-z)*groundVolterra a q t) :
    ∀t∈Icc (0:ℝ) (1/2),q t=regularWave a z t := by
  -- The sole candidate hypotheses define the original continuous normalized Volterra problem itself.
  have hr := regularWave_continuous_half a z
  have hzero := groundVolterra_unique_zero ha (hq.sub hr) ((eigenvalue a 0:ℂ)-z) (fun t ht => by
    change q t-regularWave a z t=((eigenvalue a 0:ℂ)-z)*groundVolterra a (fun s => q s-regularWave a z s) t
    rw [groundVolterra_sub ha ht
      (hq.mono (by intro s hs; exact ⟨hs.1,hs.2.trans ht.2⟩))
      (hr.mono (by intro s hs; exact ⟨hs.1,hs.2.trans ht.2⟩)),he t ht,regularWave_groundVolterra ha z ht]
    ring)
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

end
end jacobi.Support
