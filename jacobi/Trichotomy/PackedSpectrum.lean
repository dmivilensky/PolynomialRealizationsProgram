import jacobi.Trichotomy.PackedEigenfunctions
import chebyshev2.Continuum.Eigenframe
import jacobi.Bessel.Rayleigh

/-!
Article: jacobi, Proposition 2.2.
The actual packed density has exactly the original entire nonzero spectrum,
with multiplicities. A shorter proof than constructing a redundant full-space
unitary is sufficient: the true orthonormal eigenframe supplies every sorted
lower bound, and its eigenvalues exhaust the already proved exact mass trace.
Source: the min-max principle and equality of the positive trace.
Use: packedDensity_spectrum completes the original density's spectral
identification alongside GreenExponential and the three PackingMoments identities.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open chebyshev2.Continuum
open scoped Topology InnerProductSpace

/-- The actual constructed density has exactly the entire sorted original
edge spectrum, including multiplicities, without additional spectral premises.
Use: completes Proposition 2.2 for every original alpha>-1,
including both compact and infinite intrinsic coordinate images.
Article: jacobi, Proposition 2.2.
Proof: the first k+1 actual transferred orthonormal eigenfunctions give
the kth sorted eigenvalue at least Lambda_k. Both positive sequences are
summable and have the same exact mass trace. Their nonnegative difference
has zero sum, so every index agrees; no extra nonzero level can remain. -/
theorem packedDensity_spectrum (a : ℝ) (ha : -1<a) :
    kernelEigenvalue (packedDensity_integrable a ha) (packedDensity_nonneg a ha)=
      jacobi.Bessel.edgeValue a ha := by
  let D := kernelSpectralData (packedDensity_integrable a ha) (packedDensity_nonneg a ha)
  -- At each index use the first k+1 actual transported eigenfunctions,
  -- with their original decreasing eigenvalues.
  have hlower (k : ℕ) : jacobi.Bessel.edgeValue a ha k≤D.eigenvalue k := by
    have hv : Orthonormal ℝ (fun i : Fin (k+1) => packedBasis a ha i) :=
      (packedBasis_orthonormal a ha).comp (fun i : Fin (k+1) => (i:ℕ)) Fin.val_injective
    have he (i : Fin (k+1)) :
        kernelOperator (packedDensity_integrable a ha) (packedDensity_nonneg a ha)
          (packedBasis a ha i)= jacobi.Bessel.edgeValue a ha i • packedBasis a ha i :=
      packedKernel_basis a ha i
    have hb (i : Fin (k+1)) : jacobi.Bessel.edgeValue a ha k≤ jacobi.Bessel.edgeValue a ha i :=
      (jacobi.Bessel.edgeValue_properties ha).2.antitone (by omega)
    exact eigenvalue_ge_of_eigenframe D hv he hb k (by simp)
  -- Every sorted spectral surplus is nonnegative. The exact mass trace
  -- exhausts their sum, ruling out extra levels and extra multiplicities.
  have hsum := D.eigenvalue_summable.sub (jacobi.Bessel.edgeValue_summable ha)
  have hz : (∑' k,(D.eigenvalue k- jacobi.Bessel.edgeValue a ha k))=0 := by
    rw [D.eigenvalue_summable.tsum_sub (jacobi.Bessel.edgeValue_summable ha)]
    change (∑' k,kernelEigenvalue (packedDensity_integrable a ha)
      (packedDensity_nonneg a ha) k)-(∑' k,jacobi.Bessel.edgeValue a ha k)=0
    rw [kernelEigenvalue_mass,packedDensity_mass,jacobi.Bessel.first_rayleigh_sum ha,sub_self]
  funext k
  have hn := hsum.le_tsum k (fun j _ => sub_nonneg.mpr (hlower j))
  rw [hz] at hn
  change D.eigenvalue k= jacobi.Bessel.edgeValue a ha k
  linarith [hlower k]

end
end jacobi.Trichotomy
