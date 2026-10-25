import chebyshev2.SineContinuum.KernelConjugacy
import chebyshev2.Continuum.InfiniteSorting
import chebyshev2.Continuum.SpectralIdentification
import chebyshev2.Continuum.SpectralOrder

/-!
Article: chebyshev2, Proposition 2.
Proposition 2: the complete sorted spectrum of the actual real-line Birman--Schwinger operator,
including all multiplicities.
Result: `chebyshev2.SineContinuum.sine_density_eigenvalue` supplies the stated article
conclusion.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `StrictAnti Continuum.referenceEigenvalue`.

Use: `chebyshev2.SineContinuum.sineSpectralData_eigenvalue` uses this assertion to
establish exact identity `sineSpectralData.eigenvalue=Continuum.referenceEigenvalue`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.Continuum.referenceEigenvalue_eq` with the
arguments shown in the proof.
-/
theorem reference_strictAnti : StrictAnti Continuum.referenceEigenvalue := by
  intro i j hij
  rw [Continuum.referenceEigenvalue_eq,Continuum.referenceEigenvalue_eq]
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  have hc : (i:ℝ) < j := Nat.cast_lt.mpr hij
  have hsq : ((i:ℝ)+1/2)^2 < ((j:ℝ)+1/2)^2 := by nlinarith
  exact mul_lt_mul_of_pos_left hsq (sq_pos_of_pos pi_pos)

/--
Constructs `sineSpectralData` of type `Continuum.PositiveSpectralData sineKernel` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` uses this definition to establish
the stated quantitative bound `Continuum.kernelEigenvalue m_integrable (fun x => (m_positive
x).le)= Continuum.referenceEigenvalue`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def sineSpectralData : Continuum.PositiveSpectralData sineKernel where
  Index := ℕ
  basis := sineRealHilbertBasis
  eig := Continuum.referenceEigenvalue
  equation := sineKernel_basis
  nonneg j := (Continuum.referenceEigenvalue_pos j).le
  summable := Continuum.summable_reference

/--
Exact identity `sineSpectralData.eigenvalue=Continuum.referenceEigenvalue`.

Use: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` uses this identity to establish the
stated quantitative bound `Continuum.kernelEigenvalue m_integrable (fun x => (m_positive
x).le)= Continuum.referenceEigenvalue`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineSpectralData_eigenvalue : sineSpectralData.eigenvalue=Continuum.referenceEigenvalue := by
  funext j
  exact Continuum.spectralSorted_nat reference_strictAnti Continuum.referenceEigenvalue_pos
    Continuum.summable_reference j

/--
Proposition 2: the complete sorted spectrum of the actual real-line Birman--Schwinger operator,
including all multiplicities.

The stated quantitative bound `Continuum.kernelEigenvalue m_integrable (fun x => (m_positive
x).le)= Continuum.referenceEigenvalue`.

Use: `chebyshev2.SineContinuum.sine_density_eigenvalue` uses this identity to establish
exact identity `D.eigenvalue=Continuum.referenceEigenvalue`.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_integrable`,
`chebyshev2.SineContinuum.m_positive`,
`chebyshev2.Continuum.eigenvalue_basis_independent` with the arguments shown in the proof.
-/
theorem sine_kernel_eigenvalue :
    Continuum.kernelEigenvalue m_integrable (fun x => (m_positive x).le)=
      Continuum.referenceEigenvalue :=
  (Continuum.eigenvalue_basis_independent
    (Continuum.kernelSpectralData m_integrable (fun x => (m_positive x).le))
      sineSpectralData).trans sineSpectralData_eigenvalue
/--
Exact identity `D.eigenvalue=Continuum.referenceEigenvalue`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_integrable`,
`chebyshev2.SineContinuum.m_positive`,
`chebyshev2.Continuum.density_kernel_eigenvalue_eq` with the arguments shown in the proof.
-/
theorem sine_density_eigenvalue
    (D : Continuum.PositiveSpectralData (Continuum.densityOperator m)) :
    D.eigenvalue=Continuum.referenceEigenvalue :=
  (Continuum.density_kernel_eigenvalue_eq m_integrable (fun x => (m_positive x).le) D).trans
    sine_kernel_eigenvalue

end
end chebyshev2.SineContinuum
