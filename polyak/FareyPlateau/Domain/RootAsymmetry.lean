import polyak.FareyPlateau.Domain.Recovery
import polyak.Levels.Chart.GapHomeomorphism

/-! The displayed D parameter is exactly the asymmetry of the actual
ordered roots of Ξ(c)−1−c, in the original gap chart. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels

theorem source_root_asymmetry {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (q : Tuning) {a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k)
      (Chart.rationalHeight j k) a D) (ha : aE K j k D<a) :
    D=a*(Chart.leftRoot (Chart.coefficients q)+Chart.rightRoot (Chart.coefficients q)-
      2*Chart.rationalCosine j k) := by
  obtain ⟨a',r₁,r₂,_h₁,hr,_h₂,_ha',hpoly⟩ :=
    Chart.root_coordinates_of_gap q ((source_edgedomain q hK hf he).mpr ha)
  have hco : Chart.gapPolynomial a' r₁ r₂=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D := hpoly.symm.trans he
  have h₂ := congrArg Chart.Coefficients.c2 hco
  have h₁ := congrArg Chart.Coefficients.c1 hco
  dsimp only [Chart.gapPolynomial,edgeCoefficients] at h₁ h₂
  have haa : a'=a := by linarith
  have hap : 0<a' := by rw [haa];exact (aE_pos hK hf D).trans ha
  rw [hpoly,Chart.leftRoot_gapPolynomial hap hr.le,Chart.rightRoot_gapPolynomial hap hr.le]
  rw [haa] at h₁
  nlinarith

end polyak.FareyPlateau
