import jacobi.Reference.GreenIdentity
import jacobi.Reference.CoreBounds

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The actual arbitrary-complex-energy reference solution is factored by
its genuine positive sine-power ground state. Its regular factor and
ordinary derivative extend analytically through the singular endpoint.
The original Green identity gives the exact nested Volterra equation
for this same actual regular factor. The later finite-kernel convergence
and single-integral Cauchy-kernel identification are separate steps.
Use: regularWave_volterra identifies the actual arbitrary-energy limit candidate in the support-chain continuum Volterra argument.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The actual ground-normalized regular reference wave, defined without division at its singular endpoint.
Use: regularWave_volterra identifies the actual arbitrary-energy limit candidate in the support-chain continuum Volterra argument.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def regularWave (a:ℝ) (z:ℂ) (t:ℝ) : ℂ := energyCore a z (coordinate t:ℂ)

/-- The genuine ordinary spatial slope of the actual regular reference wave.
Use: regularWave_green_derivative and regularWave_volterra retain the true endpoint-regular derivative before integrating the singular ground-state formula.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def regularWaveSlope (a:ℝ) (z:ℂ) (t:ℝ) : ℂ :=
  deriv (energyCore a z) (coordinate t:ℂ)*(coordinateSlope t:ℂ)

/-- The actual regular reference wave is analytic in its spatial variable through the original singular endpoint.
Use: regularWave_volterra uses a genuine continuous derivative at zero, avoiding an unproved cancellation of singular powers in the nested integral.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the actual original physical hypergeometric coordinate lies strictly inside the unit disk, also at zero. Restrict the genuine complex analytic energy core to real scalars and compose with the original analytic cosine coordinate. -/
theorem regularWave_analytic (a:ℝ) (z:ℂ) {t:ℝ} (ht:t∈Ico 0 1) : AnalyticAt ℝ (regularWave a z) t := by
  -- Analyticity is asserted for the actual regular factor, retaining the singular sine power separately.
  have hc := (energyCore_spatial_analytic a z (coordinate_norm_lt_one_of_nonneg ht)).restrictScalars (𝕜:=ℝ)
  have hx : AnalyticAt ℝ coordinate t := by
    unfold coordinate
    fun_prop
  have hxc := (Complex.ofRealCLM.analyticAt _).comp hx
  exact hc.comp (f:=fun s:ℝ => (coordinate s:ℂ)) hxc

/-- The actual regular wave slope is spatially analytic through the original singular endpoint.
Use: regularWave_volterra integrates this genuine continuous slope on the full original closed interval, including zero.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the derivative of the actual analytic energy core is analytic inside the same original disk. Compose with the analytic physical coordinate and multiply by its genuine analytic sine Jacobian. -/
theorem regularWaveSlope_analytic (a:ℝ) (z:ℂ) {t:ℝ} (ht:t∈Ico 0 1) : AnalyticAt ℝ (regularWaveSlope a z) t := by
  -- This proves continuity of the actual differentiated factor at zero, not only inside the open physical interval.
  have hc := (energyCore_spatial_analytic a z (coordinate_norm_lt_one_of_nonneg ht)).deriv.restrictScalars (𝕜:=ℝ)
  have hx : AnalyticAt ℝ coordinate t := by unfold coordinate; fun_prop
  have hxc := (Complex.ofRealCLM.analyticAt _).comp hx
  have hxsR : AnalyticAt ℝ coordinateSlope t := by unfold coordinateSlope; fun_prop
  have hxs : AnalyticAt ℝ (fun s:ℝ => (coordinateSlope s:ℂ)) t := (Complex.ofRealCLM.analyticAt _).comp hxsR
  exact (hc.comp (f:=fun s:ℝ => (coordinate s:ℂ)) hxc).mul hxs

/-- The displayed regular reference slope is the true ordinary derivative even at the singular left endpoint.
Use: solutionSlope_regularWave differentiates the actual ground-state factorization, and regularWave_volterra applies the ordinary fundamental theorem on the complete original closed interval.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: compose the actual complex analytic energy-core derivative with the genuine real physical cosine coordinate and its ordinary Jacobian. -/
theorem regularWave_hasDerivAt (a:ℝ) (z:ℂ) {t:ℝ} (ht:t∈Ico 0 1) :
    HasDerivAt (regularWave a z) (regularWaveSlope a z t) t :=
  (energyCore_spatial_analytic a z (coordinate_norm_lt_one_of_nonneg ht)).differentiableAt.hasDerivAt.comp t
    (coordinate_hasDerivAt t).ofReal_comp

/-- The original normalized regular reference branch has value one and slope zero at the actual singular endpoint, at every complex energy.
Use: regularWave_volterra fixes its genuine integration constant and includes zero in the regularized singular derivative identity.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original physical coordinate is zero there, its Jacobian is zero and the genuine energy core has central value one. -/
theorem regularWave_initial (a:ℝ) (z:ℂ) : regularWave a z 0=1 ∧ regularWaveSlope a z 0=0 := by
  simp [regularWave,regularWaveSlope,coordinate_properties.1,energyCore_zero,coordinateSlope]

/-- The actual original reference solution is exactly its genuine ground sine-power factor times its endpoint-regular wave.
Use: regularWave_green_derivative rewrites the actual original Green identity in its regular ground-state coordinate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the independently proved original square-root-free energy-series identity is precisely this factorization. -/
theorem solution_regularWave (a:ℝ) (z:ℂ) (t:ℝ) :
    solution a z t=(weight a t:ℂ)*regularWave a z t := solution_eq_energy_series a z t

/-- The actual lowest original reference eigenfunction is exactly the genuine sine-power ground state.
Use: regularWave_green_derivative specializes Green's identity to the true reference ground energy, rather than postulating a ground-state profile.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the already identified actual reference eigenfunction at degree zero has the constant normalized Jacobi polynomial one. -/
theorem referenceGround_eq_weight (a t:ℝ) : solution a (eigenvalue a 0:ℂ) t=(weight a t:ℂ) := by
  rw [solution_at_eigenvalue]
  have hp : jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) 0=1 := by
    simp [jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]
  simp only [eigenfunction,jacobi.Jacobi.angular,hp,Polynomial.eval_one,mul_one]

/-- The actual original reference ground slope is the genuine sine-power ground derivative.
Use: regularWave_green_derivative cancels the true mixed ground-derivative terms in the original Wronskian.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original ground solution is identically the same actual weight, and both derivatives are independently proved genuine derivatives. Uniqueness identifies them. -/
theorem referenceGround_slope (a:ℝ) {t:ℝ} (ht:t∈Ioo 0 1) :
    solutionSlope a (eigenvalue a 0:ℂ) t=((weightLogSlope a t*weight a t:ℝ):ℂ) := by
  have hd := (weight_hasDerivAt a ht).ofReal_comp
  have he : (fun s:ℝ => (weight a s:ℂ))=solution a (eigenvalue a 0:ℂ) :=
    funext (fun s => (referenceGround_eq_weight a s).symm)
  rw [he] at hd
  exact (solution_hasDerivAt a (eigenvalue a 0:ℂ) ht).unique hd

/-- The true original reference slope is exactly the differentiated actual ground-state factorization.
Use: regularWave_green_derivative expresses the original Green Wronskian through the genuine regular derivative with all singular mixed terms cancelled.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: differentiate the same actual weight and regular wave by the ordinary product rule. Their literal product is the existing original reference solution, so uniqueness of derivatives identifies its original slope. -/
theorem solutionSlope_regularWave (a:ℝ) (z:ℂ) {t:ℝ} (ht:t∈Ioo 0 1) :
    solutionSlope a z t=((weightLogSlope a t*weight a t:ℝ):ℂ)*regularWave a z t+
      (weight a t:ℂ)*regularWaveSlope a z t := by
  have hd := ((weight_hasDerivAt a ht).ofReal_comp).mul (regularWave_hasDerivAt a z ⟨ht.1.le,ht.2⟩)
  have he : (fun s:ℝ => (weight a s:ℂ)*regularWave a z s)=solution a z :=
    funext (fun s => (solution_regularWave a z s).symm)
  change HasDerivAt (fun s:ℝ => (weight a s:ℂ)*regularWave a z s) _ t at hd
  rw [he] at hd
  exact (solution_hasDerivAt a z ht).unique hd

/-- The actual regular reference derivative has the exact original singular ground-state Green integral formula at arbitrary complex energy.
Use: regularWave_volterra integrates this proved identity through the actual regular endpoint, supplying the continuum equation for the original support-chain limit candidate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: specialize the independently proved original Green identity to the genuine reference ground energy. Substitute the actual solution and slope factorizations; both mixed ground-slope terms cancel. The actual interior ground state is positive, so divide its nonzero square. -/
theorem regularWave_green_derivative {a:ℝ} (ha:-1<a) (z:ℂ) {t:ℝ} (ht:t∈Ioo 0 1) :
    regularWaveSlope a z t=((eigenvalue a 0:ℂ)-z)*
      (∫s in (0:ℝ)..t,(weight a s:ℂ)*solution a z s)/(weight a t:ℂ)^2 := by
  -- The same actual reference Green identity controls every complex energy; the ground square is genuinely nonzero.
  have hgreen := reference_green_identity ha z (eigenvalue a 0:ℂ) ht
  have hi : (∫s in (0:ℝ)..t,solution a z s*solution a (eigenvalue a 0:ℂ) s)=
      ∫s in (0:ℝ)..t,(weight a s:ℂ)*solution a z s := by
    apply intervalIntegral.integral_congr
    intro s _
    change solution a z s*solution a (eigenvalue a 0:ℂ) s=(weight a s:ℂ)*solution a z s
    rw [referenceGround_eq_weight,mul_comm]
  rw [hi,referenceWronskian,referenceGround_eq_weight,referenceGround_slope a ht,
    solutionSlope_regularWave a z ht,solution_regularWave a z t] at hgreen
  apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (weight_pos a ht).ne'))).mpr
  linear_combination hgreen

/-- The original arbitrary-complex-energy regular solution satisfies its actual nested ground-state Volterra equation, including the singular left endpoint.
Use: the support-chain continuum limit can identify its normalized candidate by this genuine equation before proving convergence of the finite reduction-of-order kernels and the single-integral Cauchy representation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the actual regular solution has a genuine continuous slope on the full original closed interval, with value one at zero. Its Green derivative formula holds at every positive point and at zero both sides vanish. The integrand is consequently the same continuous actual slope, so it is genuinely integrable even at the singular endpoint. The ordinary fundamental theorem gives the asserted nested equation. -/
theorem regularWave_volterra {a:ℝ} (ha:-1<a) (z:ℂ) {t:ℝ} (ht:t∈Ico 0 1) :
    regularWave a z t=1+∫r in (0:ℝ)..t,((eigenvalue a 0:ℂ)-z)*
      (∫s in (0:ℝ)..r,(weight a s:ℂ)*solution a z s)/(weight a r:ℂ)^2 := by
  -- The singular-looking integrand is the actual endpoint-regular derivative on the complete integration interval.
  have hc : ContinuousOn (regularWaveSlope a z) (Icc 0 t) := by
    intro r hr
    exact (regularWaveSlope_analytic a z ⟨hr.1,hr.2.trans_lt ht.2⟩).continuousAt.continuousWithinAt
  have hD (r:ℝ) (hr:r∈uIcc 0 t) : HasDerivAt (regularWave a z) (regularWaveSlope a z r) r := by
    rw [uIcc_of_le ht.1] at hr
    exact regularWave_hasDerivAt a z ⟨hr.1,hr.2.trans_lt ht.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hc.intervalIntegrable_of_Icc ht.1)
  have hi : (∫r in (0:ℝ)..t,regularWaveSlope a z r)=
      ∫r in (0:ℝ)..t,((eigenvalue a 0:ℂ)-z)*
        (∫s in (0:ℝ)..r,(weight a s:ℂ)*solution a z s)/(weight a r:ℂ)^2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    rcases eq_or_lt_of_le hr.1 with h | h
    · subst r
      change regularWaveSlope a z 0=((eigenvalue a 0:ℂ)-z)*(∫s in (0:ℝ)..0,(weight a s:ℂ)*solution a z s)/(weight a 0:ℂ)^2
      rw [(regularWave_initial a z).2,intervalIntegral.integral_same,mul_zero,zero_div]
    · exact regularWave_green_derivative ha z ⟨h,hr.2.trans_lt ht.2⟩
  rw [hi,(regularWave_initial a z).1] at hFTC
  linear_combination -hFTC

end
end jacobi.Support
