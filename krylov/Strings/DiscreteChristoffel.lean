import krylov.Strings.DiscreteIdentification

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a)`.
The actual physical energy is exactly the canonical Christoffel kernel at
−1. The existing reproducing-kernel minimization theorem therefore gives
the attained unique physical minimum, with all spectral and state
normalizations already proved for this same finite string.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Polynomial jacobi.Finite
open scoped BigOperators InnerProductSpace
variable {N : ℕ} (S : DiscreteString N)

/-- The actual canonical polynomial contributes exactly the physical mass
weighted position energy at spectral parameter −1. -/
theorem orthogonalPolynomial_neg_one_sq (i : Fin (N+1)) :
    ((S.spectralData.orthogonalPolynomial i).eval (-1))^2=S.mass i.val*S.φ i.val^2 := by
  rw [S.orthogonalPolynomial_eq i, eval_mul, eval_C,
    (S.polynomialState_eval_neg_one i.val).1, mul_pow, mul_pow,
    alternating_sq, Real.sq_sqrt (S.mass_pos i.val (by omega)).le, one_mul]

/-- Genuine finite-site summation agrees with the literal physical prefix
sum, retaining both the unit origin atom and the last included mass. -/
theorem sum_physical_prefix (m : ℕ) (hm : m≤N) (f : ℕ→ℝ) :
    (∑ i : Fin (N+1) with i.val≤m, f i.val)=∑ j∈Finset.range (m+1), f j := by
  apply Finset.sum_bij (fun i _ ↦ i.val)
  · intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega)
  · intro i hi j hj he
    exact Fin.ext he
  · intro j hj
    have hjm := Finset.mem_range.mp hj
    refine ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    change j≤m
    omega
  · intro i hi
    rfl

/-- The actual Christoffel diagonal is the physical accumulated energy. -/
theorem christoffelKernel_eq (m : ℕ) (hm : m≤N) :
    krylov.Reference.christoffelKernel S.spectralData m (-1)=S.K m := by
  rw [krylov.Reference.christoffelKernel]
  simp_rw [S.orthogonalPolynomial_neg_one_sq]
  rw [sum_physical_prefix m hm (fun k ↦ S.mass k*S.φ k^2), S.K_eq_sum]

/-- Actual unique minimizing polynomial for the physical exterior problem. -/
def christoffelOptimizer (m : ℕ) : ℝ[X] :=
  krylov.Reference.christoffelPolynomial S.spectralData m (-1)

/-- The true physical exterior optimizer has the required degree and value. -/
theorem christoffelOptimizer_admissible (m : ℕ) :
    (S.christoffelOptimizer m).natDegree≤m ∧ (S.christoffelOptimizer m).eval (-1)=1 :=
  krylov.Reference.christoffelPolynomial_admissible S.spectralData m (-1)

/-- The actual exterior minimum is attained and equals the reciprocal
physical energy of precisely the same mass-gap prefix. -/
theorem christoffelOptimizer_norm (m : ℕ) (hm : m≤N) :
    ‖S.spectralData.evaluate (S.christoffelOptimizer m)‖^2=(S.K m)⁻¹ := by
  rw [christoffelOptimizer, krylov.Reference.christoffelPolynomial_norm S.spectralData (by omega),
    S.christoffelKernel_eq m hm]

/-- Full physical Christoffel minimum and its exact uniqueness statement. -/
theorem christoffel_minimum (m : ℕ) (hm : m≤N) {P : ℝ[X]}
    (hP : P.natDegree≤m) (hP1 : P.eval (-1)=1) :
    (S.K m)⁻¹≤‖S.spectralData.evaluate P‖^2 ∧
      (‖S.spectralData.evaluate P‖^2=(S.K m)⁻¹ ↔ P=S.christoffelOptimizer m) := by
  have h := krylov.Reference.christoffel_minimum_unique S.spectralData (by omega) (-1) hP hP1
  rwa [S.christoffelKernel_eq m hm] at h

end
end krylov.Strings.DiscreteString
