import jacobi.Young.SineSpectrum
import jacobi.Young.Calibration

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The distinguished density realizes the entire edge spectrum at U. It is
therefore admissible for every subset of the two spectral constraints, with
mass 1/3 and root mass one. Whenever the second constraint is retained,
both actual infima equal 2/15, with attainment by the literal density.
The Jacobi identification alpha=1/2 belongs to the separate Bessel edge theory.
Use: identifies the mass in general Transfer and the joint U relaxations.
-/
namespace jacobi.Young
noncomputable section
open Real Set jacobi.Variational
open scoped ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual distinguished edge mass is one third.
Use: identifies the mass in general Transfer and the joint U relaxations.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the proved complete sine spectrum has the exact Euler trace sum. -/
theorem distinguishedEdge_mass : distinguishedEdge.mass=1/3 := sineEigenvalue_hasSum.tsum_eq

/-- Every edge threshold at U equals the actual observation of the attaining density.
Use: verifies all joint spectral constraints simultaneously.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the top entries and the second spectral sums agree termwise. -/
theorem distinguishedEdge_threshold (i : Observation) :
    threshold distinguishedEdge i=observe distinguishedDensity i := by
  cases i with
  | second => exact tsum_congr (fun j => congrArg (fun r : ℝ => r^2) (distinguished_spectrum j).symm)
  | top => exact (distinguished_spectrum 0).symm

/-- The U profile is admissible for every set of the two spectral constraints.
Use: proves the common upper bound for root-free and root-normalized relaxations.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: combine the actual mass and root-mass identities with exact full-spectrum equality. -/
theorem distinguished_admissible (S : Set Observation) :
    distinguishedDensity.mass=distinguishedEdge.mass ∧ distinguishedDensity.rootMass≤1 ∧
      ∀ i ∈ S, threshold distinguishedEdge i≤observe distinguishedDensity i := by
  exact ⟨distinguished_mass.trans distinguishedEdge_mass.symm,distinguished_rootMass.le,
    fun i _ => (distinguishedEdge_threshold i).le⟩

/-- Every U relaxation is bounded above by the energy of its actual admissible profile.
Use: the attaining upper half of the joint calibration theorem.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: insert m_U in the actual root-constrained admissible cost set. -/
theorem joint_upper_at_U (S : Set Observation) :
    relaxedInfimum S distinguishedEdge.mass (threshold distinguishedEdge)≤
      rootInfimum S distinguishedEdge.mass (threshold distinguishedEdge) ∧
    rootInfimum S distinguishedEdge.mass (threshold distinguishedEdge)≤(2/15 : ℝ≥0∞) := by
  refine ⟨relaxed_le_root _ _ _,?_⟩
  rw [← distinguished_cost]
  exact sInf_le ⟨distinguishedDensity,distinguished_admissible S,rfl⟩

/-- Every joint U calibration retaining G_2 has exactly the attained value 2/15.
Use: closes the full common-point assertion, including both simultaneous constraints.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: sharp Young bounds every admissible candidate from below; the proved
full-spectrum attaining density gives the matching upper bound for the stronger problem. -/
theorem joint_calibration_at_U (S : Set Observation) (hS : Observation.second ∈ S) :
    relaxedInfimum S distinguishedEdge.mass (threshold distinguishedEdge)=(2/15 : ℝ≥0∞) ∧
    rootInfimum S distinguishedEdge.mass (threshold distinguishedEdge)=(2/15 : ℝ≥0∞) := by
  -- This lower bound applies to the actual joint admissible set without discarding its extra constraint.
  have hl : (2/15 : ℝ≥0∞)≤relaxedInfimum S distinguishedEdge.mass (threshold distinguishedEdge) := by
    apply le_sInf
    rintro a ⟨m,hm,rfl⟩
    have ht : (2/45 : ℝ)≤observe m .second := by
      have hh := hm.2 .second hS
      rwa [distinguishedEdge_threshold,distinguished_second] at hh
    have he := second_energy_lower m (by norm_num : (0 : ℝ)≤2/45) ht
    rw [youngValue_at_U] at he
    convert ENNReal.ofReal_le_ofReal he using 1
    · norm_num [ENNReal.ofReal_div_of_pos]
    · rfl
  obtain ⟨hrr,hu⟩ := joint_upper_at_U S
  exact ⟨le_antisymm (hrr.trans hu) hl,le_antisymm hu (hl.trans hrr)⟩

end
end jacobi.Young
