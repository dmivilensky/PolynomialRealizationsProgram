import «2610.05164v2».Continuum.MatrixSpectrum

/-!
Article: 2610.05164v2, Theorem 2.3.
The entrywise l1 bound, with no dimension-dependent operator-norm loss.
Use: `«2610.05164v2».Continuum.matrix_traceBound` feeds
`«2610.05164v2».Packing.Representation.atomic_matrix_traceBound` (atomic matrix trace Bound).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The entrywise l1 bound, with no dimension-dependent operator-norm loss.

The precise assertion is `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (∑ i, ∑ j, |A i j|)`.

Use: `«2610.05164v2».Packing.Representation.atomic_matrix_traceBound` uses this identity to
establish the precise assertion is `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ)
J.normalizedGreen - Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J)
P.point)) (exp (-gap)*(N : ℝ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem matrix_traceBound (A : Matrix ι ι ℝ) :
    TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (∑ i, ∑ j, |A i j|) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let b := EuclideanSpace.basisFun ι ℝ
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) A = ∑ j, ∑ i, A i j • InnerProductSpace.rankOne ℝ (b i) (b j) := by
    apply ContinuousLinearMap.ext
    intro u
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    simp only [map_smul,sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hb : Matrix.toEuclideanCLM (𝕜 := ℝ) A (b j) = ∑ i, A i j • b i := by
      rw [← b.sum_repr (Matrix.toEuclideanCLM (𝕜 := ℝ) A (b j))]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      change (Matrix.toEuclideanCLM (𝕜 := ℝ) A (b j)).ofLp i = A i j
      change A.mulVec (b j).ofLp i = _
      simp [b,EuclideanSpace.basisFun_apply,Matrix.mulVec, dotProduct]
    rw [hb,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change b.repr u j • (A i j • b i) = A i j • (inner ℝ (b j) u • b i)
    rw [OrthonormalBasis.repr_apply_apply,smul_smul,smul_smul,mul_comm]
  have h := traceBound_tsum (f := fun j => ∑ i, A i j • InnerProductSpace.rankOne ℝ (b i) (b j))
    Summable.of_finite Summable.of_finite (fun j => by
      have h := traceBound_tsum (f := fun i => A i j • InnerProductSpace.rankOne ℝ (b i) (b j))
        Summable.of_finite Summable.of_finite (fun i => by
          simpa only [b, (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one,mul_one] using
            (traceBound_rankOne (b i) (b j)).smul (A i j))
      simpa only [tsum_fintype] using h)
  simp only [tsum_fintype] at h
  rw [← he] at h
  rw [Finset.sum_comm] at h
  exact h

end
end «2610.05164v2».Continuum
