import jacobi.Applications.StandardSlope
import jacobi.Jacobi.StandardSlopeFormula
import jacobi.Finite.FlowTaylor

/-!
Strict asymptotic improvement by the actual standard resolvent flow.
The energy, conserved trace and initial derivative limits are proved for
the genuine finite matrices. Passing their global Taylor bound to the limit
therefore supplies actual competitors in every finite polynomial fibre.
Use: AllThreeTerm and the final comparisons use the improved upper bound;
the nonzero derivative also excludes finite standard critical points.
Article: jacobi, Theorem 5.6.
Article role: the explicit descent time, positive improvement gap and controlled Taylor
cancellation.
-/
namespace jacobi.Applications
noncomputable section
open Real Set Filter jacobi.Jacobi jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The scaled spectral trace is precisely the original matrix's packing
mass. This identifies the Taylor constant without a separate trace premise.
Article: jacobi, Theorem 5.6.
-/
theorem flowMass_eq_mass {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    flowMass S=jacobi.Packing.mass J.val := by
  have h := flowSpectral_trace S (spectralWeights S J) (flowEigenvalue S) 0
  change Matrix.trace (flowGreen S (spectralWeights S J) 0)=flowTrace S at h
  rw [flowGreen_eq,resolventWeights_zero,reconstruct_spectralWeights] at h
  rw [flowMass,flowScale,jacobi.Packing.mass,← h]
  ring

/-- The actual finite derivative converges to the evaluated rational
constant. Both the logarithmic and symmetric parameters are included.
Article: jacobi, Theorem 5.6.
-/
theorem standard_initial_slope_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => standardInitialVelocity a b (by linarith : -1<a) hb n/
      ((n+1:ℕ):ℝ)^3) atTop (𝓝 (standardSlope a)) := by
  rw [← standard_slope_integral ha]
  exact standard_initial_slope_integral_limit ha hb

/-- Off the symmetric parameter, every sufficiently large actual
standard realization has a nonzero tangent derivative along its own fibre.
Article: jacobi, Theorem 5.6.
-/
theorem standard_eventually_noncritical {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b)
    (hne : a≠1/2) :
    ∀ᶠ n : ℕ in atTop,standardInitialVelocity a b (by linarith : -1<a) hb n≠0 := by
  have hD : standardSlope a≠0 := (standardSlope_eq_zero_iff ha).not.mpr hne
  filter_upwards [(standard_initial_slope_limit ha hb).eventually_ne hD] with n hn
  intro h
  apply hn
  rw [h,zero_div]

/-- The true normalized energy after flowing the actual standard matrix.
It is a competitor in the same finite polynomial fibre for every real time.
Article: jacobi, Theorem 5.6.
-/
def standardFlowEnergy (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (t : ℝ) : ℝ :=
  (resolventFlow (nodes a b ha hb (n+1)) (standardFiber a b ha hb n) t).val.energy/
    ((n+1:ℕ):ℝ)^3

/-- The genuine Taylor inequality in normalized finite-dimensional units.
Every term is tied to the same matrix, dimension and conserved mass.
Article: jacobi, Theorem 5.6.
-/
theorem standard_flow_taylor {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (t : ℝ) :
    standardFlowEnergy a b ha hb n t≤
      (standardChain a b ha hb (n+1)).energy/((n+1:ℕ):ℝ)^3+
      t*(standardInitialVelocity a b ha hb n/((n+1:ℕ):ℝ)^3)+
      12*(jacobi.Packing.mass (standardChain a b ha hb (n+1)))^2*
        exp (4*jacobi.Packing.mass (standardChain a b ha hb (n+1))*|t|)*t^2*
          ((standardChain a b ha hb (n+1)).energy/((n+1:ℕ):ℝ)^3) := by
  let S := nodes a b ha hb (n+1)
  let J := standardFiber a b ha hb n
  have h := flowEnergy_taylor S (spectralWeights S J) t
  simp only [flowEnergy_eq,resolventWeights_zero,reconstruct_spectralWeights] at h
  rw [flowMass_eq_mass S J] at h
  have hdiv := (div_le_div_iff_of_pos_right
    (show (0:ℝ)<((n+1:ℕ):ℝ)^3 by positivity)).mpr h
  change standardFlowEnergy a b ha hb n t≤
    ((standardChain a b ha hb (n+1)).energy+t*standardInitialVelocity a b ha hb n+
      12*(jacobi.Packing.mass (standardChain a b ha hb (n+1)))^2*
        exp (4*jacobi.Packing.mass (standardChain a b ha hb (n+1))*|t|)*t^2*
          (standardChain a b ha hb (n+1)).energy)/((n+1:ℕ):ℝ)^3 at hdiv
  exact hdiv.trans_eq (by ring)

/-- The actual normalized Taylor majorant at a prescribed fixed time.
Its finite matrix energy, derivative and mass are all already verified.
Article: jacobi, Theorem 5.6.
-/
def standardTaylorMajorant (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (t : ℝ) : ℝ :=
  (standardChain a b ha hb (n+1)).energy/((n+1:ℕ):ℝ)^3+
    t*(standardInitialVelocity a b ha hb n/((n+1:ℕ):ℝ)^3)+
    12*(jacobi.Packing.mass (standardChain a b ha hb (n+1)))^2*
      exp (4*jacobi.Packing.mass (standardChain a b ha hb (n+1))*|t|)*t^2*
        ((standardChain a b ha hb (n+1)).energy/((n+1:ℕ):ℝ)^3)

/-- Every true flowed energy is bounded by this same concrete majorant.
Article: jacobi, Theorem 5.6.
-/
theorem standardTaylorMajorant_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (t : ℝ) :
    standardFlowEnergy a b ha hb n t≤standardTaylorMajorant a b ha hb n t :=
  standard_flow_taylor ha hb n t

/-- The Taylor majorant converges with the actual initial data. This
explicit scalar limit is used when padding the finite flowed competitors.
Article: jacobi, Theorem 5.6.
-/
theorem standardTaylorMajorant_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) (t : ℝ) :
    Tendsto (fun n : ℕ => standardTaylorMajorant a b (by linarith : -1<a) hb n t) atTop
      (𝓝 (standardEnergy a+t*standardSlope a+
        12*(standardMass a)^2*exp (4*standardMass a*|t|)*t^2*standardEnergy a)) := by
  have ha' : -1<a := by linarith
  have hE : Tendsto (fun n : ℕ => (standardChain a b ha' hb (n+1)).energy/((n+1:ℕ):ℝ)^3)
      atTop (𝓝 (standardEnergy a)) :=
    (standard_energy_limit ha hb).comp (tendsto_add_atTop_nat 1)
  have hV := standard_initial_slope_limit ha hb
  have hM := standard_mass_limit ha' hb
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp ((hM.const_mul 4).mul_const |t|)
  exact (hE.add (hV.const_mul t)).add
    (((((hM.pow 2).const_mul 12).mul hexp).mul_const (t^2)).mul hE)

/-- The true flowed energies have the improved upper limit. The estimate
uses exact power/log integrals and the global derivative remainder, with
no numerical certificate or asymptotic hypothesis about the chosen flow.
Article: jacobi, Theorem 5.6.
-/
theorem standard_flow_descent {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    limsup (fun n : ℕ => ENNReal.ofReal
      (standardFlowEnergy a b (by linarith : -1<a) hb n (descentTime a))) atTop≤
      ENNReal.ofReal (standardEnergy a-descentGap a) := by
  have ha' : -1<a := by linarith
  let E n := (standardChain a b ha' hb (n+1)).energy/((n+1:ℕ):ℝ)^3
  let V n := standardInitialVelocity a b ha' hb n/((n+1:ℕ):ℝ)^3
  let M n := jacobi.Packing.mass (standardChain a b ha' hb (n+1))
  have hE : Tendsto E atTop (𝓝 (standardEnergy a)) :=
    (standard_energy_limit ha hb).comp (tendsto_add_atTop_nat 1)
  have hV : Tendsto V atTop (𝓝 (standardSlope a)) := standard_initial_slope_limit ha hb
  have hM : Tendsto M atTop (𝓝 (standardMass a)) := standard_mass_limit ha' hb
  let T n := E n+descentTime a*V n+
    12*(M n)^2*exp (4*M n*|descentTime a|)*(descentTime a)^2*E n
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp
    ((hM.const_mul 4).mul_const |descentTime a|)
  have hT : Tendsto T atTop (𝓝 (standardEnergy a+descentTime a*standardSlope a+
      12*(standardMass a)^2*exp (4*standardMass a*|descentTime a|)*
        (descentTime a)^2*standardEnergy a)) :=
    (hE.add (hV.const_mul _)).add
      (((((hM.pow 2).const_mul 12).mul hexp).mul_const _).mul hE)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hT
  have hle := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun n =>
    ENNReal.ofReal_le_ofReal (standard_flow_taylor ha' hb n (descentTime a))))
  exact (hle.trans_eq hlim.limsup_eq).trans (ENNReal.ofReal_le_ofReal (descentTime_taylor_bound ha))

/-- Every flowed standard matrix is a genuine competitor, so the
infimum over all irreducible realizations satisfies the same improved bound.
Article: jacobi, Theorem 5.6.
-/
theorem standard_fibre_descent {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    limsup (fun n : ℕ => fibreEnergyInfimum (nodes a b (by linarith : -1<a) hb (n+1))) atTop≤
      ENNReal.ofReal (standardEnergy a-descentGap a) := by
  have hle := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun n =>
    show fibreEnergyInfimum (nodes a b (by linarith : -1<a) hb (n+1))≤
      ENNReal.ofReal (standardFlowEnergy a b (by linarith : -1<a) hb n (descentTime a)) from
    sInf_le ⟨_,(resolventFlow _ (standardFiber a b (by linarith) hb n) (descentTime a)).property,rfl⟩))
  exact hle.trans (standard_flow_descent ha hb)

end
end jacobi.Applications
