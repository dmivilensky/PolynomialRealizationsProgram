import krylov.Stability.UniformGram
import krylov.Secant.Canonical
import Mathlib.Tactic.NoncommRing

/-!
Article: main_krylov, eq:weighted-flags and eq:weighted-flag-bound, true flag algebra.
Use: express actual square oblique flags by their genuine normalized-column
Gram correction and true column rank-one changes before taking weighted bounds.
Source: exact finite Gram factorization and the existing transported-flag convention.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Secant
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual near-identity normalized-column Gram data give a genuine square column inverse domain.
Use: the true oblique flag is well defined without any lower bound on original physical column lengths.
Article: main_krylov, apB:lem:UAsteps and eq:weighted-flags.
Proof: the proved Gram inverse domain forces the square column determinant
nonzero, because the true Gram determinant is its square. -/
theorem column_unit_of_near_gram (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) : IsUnit T.det := by
  have hu := (near_identity_inverse (Tᵀ*T) hT).1
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hd := isUnit_iff_ne_zero.mp hu
  rw [Matrix.det_mul,Matrix.det_transpose,hz,zero_mul] at hd
  exact hd rfl

/-- The true square column inverse is its actual inverse Gram followed by transpose.
Use: convert the real oblique flag to the same normalized Gram coordinates as the uniform conditioning estimate.
Article: main_krylov, eq:weighted-flags.
Proof: reverse the true Gram product inverse and cancel the genuine transpose inverse. -/
theorem inverseGram_transpose (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    (Tᵀ*T)⁻¹*Tᵀ=T⁻¹ := by
  rw [Matrix.mul_inv_rev,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (by simpa only [Matrix.det_transpose] using hT),Matrix.mul_one]

/-- The actual old-column quadratic form is exactly the sum of its true old-column rank-one matrices.
Use: weighted flag comparisons isolate each actual normalized-column change.
Article: main_krylov, eq:weighted-flags, sum of unit outer products.
Proof: multiply the actual prefix diagonal into each column and expand the
remaining true matrix contraction; its indicator selects precisely the old columns. -/
theorem prefix_form_eq_column_sum (T : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    T*prefixProjection n l*Tᵀ=
      ∑ j∈Finset.univ.filter (fun j : Fin n => j.val≤l),
        Matrix.vecMulVec (fun i => T i j) (fun i => T i j) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [prefixProjection,Matrix.mul_diagonal,Matrix.transpose_apply,Matrix.sum_apply,
    Matrix.vecMulVec_apply,Finset.sum_filter,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]

/-- The true square oblique-flag change splits into actual inverse-Gram error and true column rank-one differences.
Use: the weighted argument keeps each small reference column length paired with its own actual reference-error weight.
Article: main_krylov, eq:weighted-flags and eq:weighted-flag-bound.
Proof: insert the proved inverse-Gram formula into the actual transported
flag, add and subtract its genuine old-column quadratic form, and expand both
actual old-column forms as finite rank-one sums. -/
theorem transportedFlag_gram_split (T Q : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsUnit T.det) (l : ℕ) :
    transportedFlag T l-Q*prefixProjection n l*Qᵀ=
      T*prefixProjection n l*((Tᵀ*T)⁻¹-1)*Tᵀ+
        ∑ j∈Finset.univ.filter (fun j : Fin n => j.val≤l),
          (Matrix.vecMulVec (fun i => T i j) (fun i => T i j)-
            Matrix.vecMulVec (fun i => Q i j) (fun i => Q i j)) := by
  -- The first term is genuinely a normalized Gram error; every remaining term keeps its own physical column.
  rw [Finset.sum_sub_distrib,← prefix_form_eq_column_sum,← prefix_form_eq_column_sum]
  unfold transportedFlag
  have hi := inverseGram_transpose T hT
  calc
    _ = T*prefixProjection n l*((Tᵀ*T)⁻¹*Tᵀ)-Q*prefixProjection n l*Qᵀ := by rw [hi]
    _ = _ := by noncomm_ring

end
end krylov.Stability
