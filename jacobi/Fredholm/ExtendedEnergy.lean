import jacobi.Variational.ExtendedEnergy
import jacobi.Variational.FredholmRelaxation

/-!
Article: jacobi, Theorem D.7.
The Fredholm problem over finite-energy densities is exactly the printed
infimum over all nonnegative L1 sources. A genuine finite extended energy
constructs the original Density with the same source, operator and spectrum;
an infinite-energy source cannot lower either infimum.
Source: nonnegative Lebesgue integration and order properties of infima.
Use: the calibration and transfer statements apply to the full stated source domain.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational
open scoped ENNReal

/-- The literal Fredholm variational infimum over every nonnegative L1 source, allowing infinite energy.
Use: the calibration and transfer statements apply to the full stated source domain.
Article: jacobi, Theorem D.7.
-/
def extendedInfimum (s M : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  sInf (L1Source.energyCost '' {m | m.mass≤M ∧ d≤m.fredholm s})

/-- Every admissible nonnegative L1 source satisfies the Fredholm relaxed lower bound without a finite-energy premise.
Use: the final calibrated bound includes initially infinite-energy competitors.
Article: jacobi, Theorem D.7.
Proof: infinite energy is automatic; at finite energy wrap the literal
source in Density, preserving the actual determinant and mass exactly. -/
theorem infimum_le_extended_energy (s M : ℝ) (d : ℝ≥0∞) (m : L1Source)
    (hm : m.mass≤M) (hD : d≤m.fredholm s) : fredholmInfimum s M d≤m.energyCost := by
  by_cases h : m.energyCost=∞
  · rw [h]
    exact le_top
  · let q := m.finiteEnergyDensity h
    exact (sInf_le ⟨q,⟨hm,hD⟩,rfl⟩ : fredholmInfimum s M d≤q.cost).trans_eq q.energyCost_eq_cost.symm

/-- The unrestricted source infimum is exactly the original Fredholm infimum, with no feasibility assumptions.
Use: identifies the proved calibration value with the source's literal B_s on its entire stated domain.
Article: jacobi, Theorem D.7.
Proof: every finite-energy competitor is an unrestricted source with the
same cost. Conversely the unrestricted lower bound handles finite and
infinite energy, giving the reverse order comparison. -/
theorem extendedInfimum_eq (s M : ℝ) (d : ℝ≥0∞) : extendedInfimum s M d=fredholmInfimum s M d := by
  -- Neither direction needs nonemptiness or an auxiliary integrability assumption.
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨m,⟨hm,hD⟩,rfl⟩
    exact (sInf_le ⟨m.toL1Source,⟨hm,hD⟩,rfl⟩ :
      extendedInfimum s M d≤m.toL1Source.energyCost).trans_eq m.energyCost_eq_cost
  · apply le_sInf
    rintro _ ⟨m,⟨hm,hD⟩,rfl⟩
    exact infimum_le_extended_energy s M d m hm hD

end
end jacobi.Fredholm
