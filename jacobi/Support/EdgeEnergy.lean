import jacobi.Support.NormalizedEdge
import jacobi.Support.NodeLimit

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The original printed frequency and complex energy coordinates give
precisely the normalized displacement used in the finite Volterra
limit. All degree shifts, the ground phase and c_0 are exact.
Use: edgeEnergy_limit converts the exact printed N^2 energy coordinate to the n^2 factor in the actual finite Volterra equation.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The original support frequency at dimension n+1 divided by its polynomial degree n tends to one.
Use: edgeEnergy_limit converts the exact printed N^2 energy coordinate to the n^2 factor in the actual finite Volterra equation.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the dimension shift is exactly the already proved degree-frequency ratio with alpha replaced by alpha+2. -/
theorem support_frequency_ratio (a b:ℝ) :
    Tendsto (fun n:ℕ => jacobi.Jacobi.frequency a b (n+1)/(n:ℝ)) atTop (𝓝 1) := by
  convert jacobi.Jacobi.frequency_ratio_tendsto (a+2) b using 1
  funext n
  dsimp only [jacobi.Jacobi.frequency]
  push_cast
  ring

/-- The actual top-node cosine gap has its exact original scaled ground energy.
Use: edgeEnergy_limit subtracts this actual moving reference energy from every convergent complex printed energy.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: reuse the actual natural-node distance limit at its first node and at the exact n+1 matrix dimension; its original phase is pi*gamma. -/
theorem topNode_energy_limit (a b:ℝ) :
    Tendsto (fun n:ℕ => 2*(jacobi.Jacobi.frequency a b (n+1))^2*
      (1-cos (gamma a*step a b (n+1)))) atTop (𝓝 (π^2*(gamma a)^2)) := by
  have h := (naturalNode_distance_limit a b 0).comp (tendsto_add_atTop_nat 1)
  have hangle (n:ℕ) : jacobi.Jacobi.modelAngle a b (n+1) 0=gamma a*step a b (n+1) := by
    rw [jacobi.Jacobi.modelAngle,phaseGrid_eq]
    simp only [Nat.cast_zero,zero_add]
    dsimp only [step]
    ring
  simpa only [Function.comp_def,hangle,phaseGrid_eq,Nat.cast_zero,zero_add,mul_pow] using h

/-- Every actual convergent printed complex edge energy gives the exact scaled ground displacement required by the genuine finite Volterra limit.
Use: naturalWave_complex_edge applies the proved normalized convergence directly to y_n=1-z_n/(2*N^2), with no additional asymptotic assumption.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the genuine top-node energy tends to pi^2*gamma^2 and the actual n/N ratio tends to one. Their exact finite identity gives the scaled displacement; the reference ground eigenvalue includes precisely the original c_0 correction. -/
theorem edgeEnergy_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) {z:ℕ→ℂ} {E:ℂ}
    (hz:Tendsto z atTop (𝓝 E)) :
    Tendsto (fun n:ℕ => groundScaledEnergy a b n
      (1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2))) atTop
      (𝓝 (((eigenvalue a 0:ℂ)-(E+(jacobi.Jacobi.endpointCorrection a:ℂ)))/2)) := by
  -- Keep the original frequency ratio and top-node energy as separate proved limits.
  have hratio := (support_frequency_ratio a b).inv₀ one_ne_zero
  simp only [inv_one] at hratio
  have hratioC := Complex.continuous_ofReal.continuousAt.tendsto.comp hratio
  have htop := Complex.continuous_ofReal.continuousAt.tendsto.comp (topNode_energy_limit a b)
  have hlim := ((hratioC.pow 2).mul (htop.sub hz)).div_const 2
  have hv : ((1:ℂ)^2*((π^2*(gamma a)^2:ℝ)-E))/2=
      ((eigenvalue a 0:ℂ)-(E+(jacobi.Jacobi.endpointCorrection a:ℂ)))/2 := by
    simp only [eigenvalue,Nat.cast_zero,zero_add,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
    ring
  simp only [Complex.ofReal_one] at hlim
  rw [hv] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  -- Their exact finite identity supplies the original ground-scaled displacement.
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hF : (jacobi.Jacobi.frequency a b (n+1):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (jacobi.Jacobi.frequency_pos ha hb (by omega)).ne'
  simp only [Function.comp_def,groundScaledEnergy,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_ofNat,Complex.ofReal_natCast,inv_div]
  field_simp [hF,hn0]
  ring

end
end jacobi.Support
