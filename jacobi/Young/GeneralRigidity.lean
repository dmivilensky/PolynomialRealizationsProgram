import jacobi.Young.GeneralMoment
import jacobi.Young.HolderRigidity

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The proved full-domain Green potential satisfies exactly the same sharp
Holder/Sobolev chain. Equality forces sqrt(m) proportional to this actual
H1 potential. Its square is integrable, so every nonzero equality source
automatically has finite total mass; the complete profile classification
already proved for finite mass therefore applies without a restriction.
Use: full-domain equality propagation reuses the exact finite-mass sharp argument.
-/
namespace jacobi.Young.EnergySource
noncomputable section
open Real MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

/-- The same sharp analytic chain holds on the complete source domain.
Use: full-domain equality propagation reuses the exact finite-mass sharp argument.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: discharge every premise of the shared Holder/Sobolev theorem with
the actual Riesz Green potential, its finite cube and proved Green energy. -/
theorem young_chain (m : EnergySource) :
    m.second^3≤m.energy^2*(∫ x, m.green x^3) ∧
      18*(∫ x, m.green x^3)^2≤5*m.second^3 :=
  jacobi.Young.young_chain_of_green m.measurable.aestronglyMeasurable m.nonneg m.energy_integrable
    m.green_sobolev m.green_nonneg m.green_cube_integrable rfl m.green_energy

/-- Every nonzero equality source in the unrestricted Young domain has finite mass.
Use: the proved finite-mass classification covers the entire printed equality statement.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: equality in the common chain gives G³=E²S. The exact cubic Holder
defect at c=E/G has zero integral and forces sqrt(m)=cu almost everywhere.
Hence m=c²u² is integrable because the actual potential belongs to H1. -/
theorem integrable_of_young_equality (m : EnergySource) (hE : 0<m.energy)
    (he : 18*m.second^3=5*m.energy^4) : Integrable m.value := by
  -- The positive actual second moment fixes a legitimate normalization even before mass is known finite.
  have hG := m.second_pos hE
  have hEq := young_chain_rigid hG hE.le
    (integral_nonneg (fun x => pow_nonneg (m.green_nonneg x) _)) (m.young_chain).1 (m.young_chain).2 he
  let c := m.energy/m.second
  have hc : 0<c := div_pos hE hG
  have hp (x : ℝ) : Real.sqrt (m.value x)^3=m.value x^(3/2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 3 (m.nonneg x),Real.rpow_ofNat]
  have hroot : Integrable (fun x => Real.sqrt (m.value x)^3) := by
    simp_rw [hp]
    exact m.energy_integrable
  have hcross : Integrable (fun x => Real.sqrt (m.value x)^2*m.green x) := by
    simp_rw [Real.sq_sqrt (m.nonneg _)]
    exact m.green_pair_integrable
  have hzero : 2*(∫ x, Real.sqrt (m.value x)^3)+c^3*(∫ x, m.green x^3)-
      3*c*(∫ x, Real.sqrt (m.value x)^2*m.green x)=0 := by
    simp_rw [hp,Real.sq_sqrt (m.nonneg _)]
    change 2*m.energy+c^3*(∫ x, m.green x^3)-3*c*m.second=0
    dsimp only [c]
    field_simp
    nlinarith [hEq]
  have h := cubic_holder_rigidity (fun x => Real.sqrt_nonneg _) m.green_nonneg
    hroot m.green_cube_integrable hcross hc hzero
  apply (m.green_sobolev.value_memLp.integrable_sq.const_mul (c^2)).congr
  filter_upwards [h] with x hx
  have hh := congrArg (fun r : ℝ => r^2) hx
  rw [Real.sq_sqrt (m.nonneg x),mul_pow] at hh
  exact hh.symm

end
end jacobi.Young.EnergySource
