import jacobi.Young.SineFrame
import Mathlib.NumberTheory.ZetaValues

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The actual compact Green operator has the full ordered spectrum
2/(pi(n+1))^2, with every multiplicity accounted for. Min--max supplies
entrywise lower bounds from genuine eigenvectors; Euler's proved zeta(2)
sum exhausts the known trace 1/3 and forces equality in every entry.
Source: Euler's zeta(2) identity (mathlib), positivity and trace-class min--max.
Use: exhausts the actual trace and rules out additional eigenvalues or multiplicities.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory jacobi.Variational chebyshev2.Continuum
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The target sine eigenvalues have total mass exactly one third.
Use: exhausts the actual trace and rules out additional eigenvalues or multiplicities.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Source: Euler's zeta(2) identity, formalized as mathlib's hasSum_zeta_two.
Proof: remove the zero initial term in zeta(2), multiply by 2/pi²,
and identify each summand with the actual Dirichlet-frequency expression. -/
theorem sineEigenvalue_hasSum : HasSum sineEigenvalue (1/3 : ℝ) := by
  -- The library's zero-index term is zero, so shifting loses no mass.
  have hz : HasSum (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)^2) (Real.pi^2/6) := by
    simpa only [Finset.sum_range_one,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),
      div_zero,sub_zero,Nat.cast_add,Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  convert hz.mul_left (2/Real.pi^2) using 1
  · funext n
    dsimp [sineEigenvalue,frequency]
    field_simp [Real.pi_ne_zero]
  · field_simp [Real.pi_ne_zero]
    ring

/-- The complete actual ordered spectrum of the distinguished Young density.
Use: proves every spectral constraint at U and supplies its exact positive edge spectrum.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: differences between actual eigenvalues and the min--max sine lower bounds
are summable and nonnegative. Their total is zero because both traces are 1/3;
each difference is therefore zero. -/
theorem distinguished_spectrum (n : ℕ) : distinguishedDensity.spectrum n=sineEigenvalue n := by
  -- This step proves spectral completeness, beyond merely constructing eigenfunctions.
  have hs : Summable distinguishedDensity.spectrum :=
    (kernelSpectralData distinguishedDensity.integrable distinguishedDensity.nonneg).eigenvalue_summable
  have hd := hs.sub sineEigenvalue_hasSum.summable
  have ht : (∑' j, (distinguishedDensity.spectrum j - sineEigenvalue j))=0 := by
    rw [hs.tsum_sub sineEigenvalue_hasSum.summable,
      show (∑' j,distinguishedDensity.spectrum j)=distinguishedDensity.mass from
        kernelEigenvalue_mass distinguishedDensity.integrable distinguishedDensity.nonneg,
      distinguished_mass,sineEigenvalue_hasSum.tsum_eq,sub_self]
  have h := hd.le_tsum n (fun j _ => sub_nonneg.mpr (sineEigenvalue_le_spectrum j))
  rw [ht] at h
  exact le_antisymm (sub_nonpos.mp h) (sineEigenvalue_le_spectrum n)

/-- The actual distinguished eigenvalues are positive and occur without repetitions.
Use: records simplicity in the existing spectrum convention, which counts every multiplicity.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: substitute the full spectrum identity and use strict decrease of positive reciprocal squares. -/
theorem distinguished_spectrum_simple : (∀ n, 0<distinguishedDensity.spectrum n) ∧
    StrictAnti distinguishedDensity.spectrum := by
  simp_rw [show distinguishedDensity.spectrum=sineEigenvalue from funext distinguished_spectrum]
  exact ⟨sineEigenvalue_pos,sineEigenvalue_strictAnti⟩

/-- The actual top eigenvalue at the common calibration point.
Use: verifies the additional top-eigenvalue constraint for joint calibrations at U.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: specialize the complete spectrum to its first entry. -/
theorem distinguished_top : observe distinguishedDensity .top=2/Real.pi^2 := by
  change distinguishedDensity.spectrum 0=_
  rw [distinguished_spectrum]
  norm_num [sineEigenvalue,frequency]

/-- The distinguished spectrum is an actual positive edge spectrum.
Use: specializes general Transfer and every calibration threshold to U without assumed data.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def distinguishedEdge : EdgeSpectrum where
  value := sineEigenvalue
  positive := sineEigenvalue_pos
  antitone := sineEigenvalue_strictAnti.antitone
  summable := sineEigenvalue_hasSum.summable

end
end jacobi.Young
