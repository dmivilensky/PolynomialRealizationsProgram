import «2610.05164v2».Continuum.NuclearSeries
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: 2610.05164v2, Theorem 2.3.
A finite orthonormal basis gives a finite nuclear bound for every operator.
Use: `«2610.05164v2».Continuum.euclidean_isTraceClass` feeds
`«2610.05164v2».Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A finite orthonormal basis gives a finite nuclear bound for every operator.

The precise assertion is `TraceBound T (∑ i, ‖T (b i)‖)`.

Use: `«2610.05164v2».Continuum.euclidean_isTraceClass` uses this assertion to establish the
trace-class property: `IsTraceClass T`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceBound_tsum`,
`«2610.05164v2».Continuum.traceBound_rankOne` with the arguments shown in the proof.
-/
theorem finite_basis_traceBound {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    TraceBound T (∑ i, ‖T (b i)‖) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.traceBound_tsum`,
  -- `«2610.05164v2».Continuum.traceBound_rankOne` with the arguments shown in the proof.
  have he : T = ∑ i, InnerProductSpace.rankOne ℝ (T (b i)) (b i) := by
    apply ContinuousLinearMap.ext
    intro u
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    simp only [map_smul,sum_apply,InnerProductSpace.rankOne_apply,OrthonormalBasis.repr_apply_apply]
  have h := traceBound_tsum (Summable.of_finite (f := fun i => InnerProductSpace.rankOne ℝ (T (b i)) (b i)))
    (Summable.of_finite (f := fun i => ‖T (b i)‖)) (fun i => by
      simpa only [b.orthonormal.norm_eq_one,mul_one] using traceBound_rankOne (T (b i)) (b i))
  simpa only [tsum_fintype,← he] using h

/--
The trace-class property: `IsTraceClass T`.

Use: `«2610.05164v2».Continuum.atomicMatrixSpectralData` uses this assertion in the displayed
construction of `atomicMatrixSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.isTraceClass`,
`«2610.05164v2».Continuum.finite_basis_traceBound` with the arguments shown in the proof.
-/
theorem euclidean_isTraceClass {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) : IsTraceClass T :=
  (finite_basis_traceBound (EuclideanSpace.basisFun ι ℝ) T).isTraceClass

end
end «2610.05164v2».Continuum
