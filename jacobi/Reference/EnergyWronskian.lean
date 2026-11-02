import jacobi.Reference.ZeroGreenCoefficients

/-!
Article: jacobi, Proposition C.4.
The genuine reflected-solution Wronskian is constant at every real
energy. Below the first original reference eigenvalue it is nonzero;
the exact midpoint characteristic proves this without a new spectral
or boundary-condition hypothesis. This extends the earlier c_0 argument
to energy zero and to the full reference resolvent set below tau_1.
Source: Abel's identity and the already proved midpoint factorization.
Use: energyGreenConstant_at fixes the denominator of the original Green kernel at E=0, rather than only at c_0.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual selected left/right Wronskian at an arbitrary real energy.
Use: energyGreenConstant_at fixes the denominator of the original Green kernel at E=0, rather than only at c_0.
Article: jacobi, Proposition C.4.
-/
def energyWronskian (a E t : ℝ) : ℂ :=
  solution a (E:ℂ) (1-t)*solutionSlope a (E:ℂ) t+
    solution a (E:ℂ) t*solutionSlope a (E:ℂ) (1-t)

/-- The true reflected-solution Wronskian has derivative zero at every physical interior point and every real energy.
Use: energyWronskian_formula identifies the actual Green normalization with the exact original characteristic.
Article: jacobi, Proposition C.4.
Source: Abel's Wronskian identity for a scalar Schrodinger equation.
Proof: differentiate the original four factors and substitute their genuine differential equations; reflection symmetry cancels the potential and energy terms. -/
theorem energyWronskian_hasDerivAt {a E t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (energyWronskian a E) 0 t := by
  -- Reflection changes each actual spatial derivative's sign before the two product rules are combined.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hR := (solution_hasDerivAt a (E:ℂ) hr).scomp t ((hasDerivAt_id t).const_sub 1)
  have hR' := (solutionSlope_hasDerivAt a (E:ℂ) hr).scomp t ((hasDerivAt_id t).const_sub 1)
  have h := (hR.mul (solutionSlope_hasDerivAt a (E:ℂ) ht)).add
    ((solution_hasDerivAt a (E:ℂ) ht).mul hR')
  convert h using 1
  · rfl
  · have he := solution_equation ha (E:ℂ) ht
    have her := solution_equation ha (E:ℂ) hr
    rw [potential_reflection] at her
    simp only [neg_smul,one_smul,Function.comp_apply]
    linear_combination solution a (E:ℂ) (1-t)*he-solution a (E:ℂ) t*her

/-- The actual constant Wronskian has exactly the original characteristic normalization at every real energy.
Use: energyGreenConstant_ne_zero discharges the nonzero denominator in the Green factor at energy zero from the true first-eigenvalue condition.
Article: jacobi, Proposition C.4.
Proof: the actual derivative vanishes on the connected interior; evaluate the constant at the midpoint and reuse the already verified identity 2*a_0*b_0=kappa*Delta_tau. -/
theorem energyWronskian_formula {a E t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    energyWronskian a E t=((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicTau a (E:ℂ) := by
  -- Both sides use the original reference functions and their fixed source normalization.
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun t ht => (energyWronskian_hasDerivAt (E := E) ha ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (energyWronskian_hasDerivAt (E := E) ha ht).deriv) ht
    (show (1/2:ℝ)∈Ioo (0:ℝ) 1 by norm_num)
  rw [hc]
  have hm := solution_midpoint_product ha (E:ℂ)
  convert hm using 1
  dsimp only [energyWronskian]
  rw [show (1:ℝ)-1/2=1/2 by ring]
  ring

/-- The genuine real Green denominator is the selected left/right Wronskian at the nonsingular midpoint.
Use: energyGreenFactor uses this independently fixed normalization at the original real energy.
Article: jacobi, Proposition C.4.
-/
def energyGreenConstant (a E : ℝ) : ℝ := (energyWronskian a E (1/2)).re

/-- The same genuine real Green denominator is the true Wronskian at every interior point.
Use: energyGreenFactor_coefficient combines the actual two Green identities with the correct constant and sign.
Article: jacobi, Proposition C.4.
Proof: the original solutions and slopes are real at real energies. Take real parts of the already proved constant complex Wronskian identity. -/
theorem energyGreenConstant_at {a E t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    realSolution a E (1-t)*realSlope a E t+realSolution a E t*realSlope a E (1-t)=
      energyGreenConstant a E := by
  -- Reality has already been proved for these actual spatial derivatives.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have he : energyWronskian a E t=energyWronskian a E (1/2) :=
    (energyWronskian_formula ha ht).trans (energyWronskian_formula ha (by norm_num)).symm
  have hw : ((realSolution a E (1-t)*realSlope a E t+
      realSolution a E t*realSlope a E (1-t):ℝ):ℂ)=energyWronskian a E t := by
    simp only [energyWronskian,Complex.ofReal_add,Complex.ofReal_mul,realSolution_cast,
      realSlope,solutionSlope_real a E ht,solutionSlope_real a E hr]
  exact (congrArg Complex.re hw).trans (congrArg Complex.re he)

/-- Every genuine reference eigenvalue lies strictly above a real energy below the first one.
Use: all energyGreen spectral denominators are positive under the literal condition used by Appendix C.5 at E=0.
Article: jacobi, Proposition C.4.
Proof: use the already proved monotonicity of the complete original reference spectrum. -/
theorem energy_gap_pos {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) (k : ℕ) :
    0<eigenvalue a k-E :=
  sub_pos.mpr (hE.trans_le ((eigenvalue_strictMono ha).monotone (Nat.zero_le k)))

/-- The actual Green Wronskian is nonzero below the true first reference eigenvalue.
Use: energyGreenFactor_coefficient divides by its genuine denominator with no unproved zero-energy invertibility premise.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: every zero of the actual reference characteristic is a genuine enumerated reference eigenvalue. The first-eigenvalue bound excludes it. The independently proved positive norm constant and reality transfer this nonvanishing to the original real Wronskian. -/
theorem energyGreenConstant_ne_zero {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) :
    energyGreenConstant a E≠0 := by
  -- The exact characteristic zero set replaces a separate completeness or invertibility assumption.
  have hc : characteristicTau a (E:ℂ)≠0 := by
    intro hz
    obtain ⟨k,hk⟩ := (characteristicTau_zero_iff a (E:ℂ)).mp hz
    have he : E=eigenvalue a k := Complex.ofReal_injective hk
    linarith [energy_gap_pos ha hE k]
  have hW := mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (by positivity [normConstant_pos ha] : 0<2*Real.pi^2*normConstant a))) hc
  rw [← energyWronskian_formula ha (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)] at hW
  have hreal : ((energyGreenConstant a E:ℝ):ℂ)=energyWronskian a E (1/2) := by
    rw [← energyGreenConstant_at ha (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)]
    simp only [energyWronskian,Complex.ofReal_add,Complex.ofReal_mul,realSolution_cast,
      realSlope,solutionSlope_real a E (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1),
      show (1:ℝ)-1/2=1/2 by ring]
  exact fun hz => hW (by rw [← hreal,hz,Complex.ofReal_zero])

end
end jacobi.Reference
