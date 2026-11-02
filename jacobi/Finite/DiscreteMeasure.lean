import jacobi.Finite.Gram
import Mathlib.LinearAlgebra.Vandermonde

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Weighted polynomial evaluation realizes the finite discrete L² space in the
existing Euclidean space. Distinct nodes and positive weights imply positivity
of every full polynomial Gram matrix, by the Vandermonde determinant.
Source: de Boor and Golub, The numerically stable reconstruction of a Jacobi
matrix from spectral data; the finite weighted polynomial construction.
Use: is the spectral-weight domain for Jacobi reconstruction and change of measure.
-/

namespace jacobi.Finite
noncomputable section
open Polynomial Matrix
open scoped BigOperators InnerProductSpace

/-- A finite probability measure with distinct labelled atoms and positive weights.
Use: is the spectral-weight domain for Jacobi reconstruction and change of measure.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
structure DiscreteMeasure (N : ℕ) where
  /-- Location of each atom. -/
  node : Fin N → ℝ
  /-- The support consists of exactly N distinct atoms. -/
  distinct : Function.Injective node
  /-- The spectral probability weights. -/
  weight : Fin N → ℝ
  /-- Every atom is present in the spectral measure. -/
  positive : ∀ i, 0 < weight i
  /-- The constant polynomial has squared norm one. -/
  probability : ∑ i, weight i = 1

namespace DiscreteMeasure
variable {N : ℕ} (M : DiscreteMeasure N)

/-- Weighted evaluation, an isometric model of the discrete polynomial L² norm.
Use: applies the community Gram--Schmidt process to polynomial values.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def evaluate (p : ℝ[X]) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => Real.sqrt (M.weight i) * p.eval (M.node i))

/-- Weighted evaluation as a linear map on polynomials.
Use: transports the inverse triangular change of basis to actual polynomials.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def evaluation : ℝ[X] →ₗ[ℝ] EuclideanSpace ℝ (Fin N) where
  toFun := M.evaluate
  map_add' p q := by
    apply PiLp.ext
    intro i
    simp [evaluate, mul_add]
  map_smul' a p := by
    apply PiLp.ext
    intro i
    simp [evaluate, mul_left_comm]

/-- Inner products are exactly the weighted polynomial integrals.
Use: identifies Euclidean Gram matrices with those printed in the article.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the two square-root weights multiply to the weight itself. -/
theorem inner_evaluate (p q : ℝ[X]) :
    inner ℝ (M.evaluate p) (M.evaluate q) =
      ∑ i, M.weight i * p.eval (M.node i) * q.eval (M.node i) := by
  rw [evaluate, evaluate, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = Real.sqrt (M.weight i)^2 *
        (p.eval (M.node i) * q.eval (M.node i)) := by ring
    _ = _ := by rw [Real.sq_sqrt (M.positive i).le]; ring

/-- Polynomial evaluation in a degree-graded basis has nonzero determinant.
Use: makes the full Gram matrix positive definite for every positive weight vector.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: factor evaluation into a Vandermonde matrix and an upper triangular
coefficient matrix with nonzero diagonal. -/
theorem evaluation_det_ne_zero (p : Fin N → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree = i.val) (hlc : ∀ i, (p i).leadingCoeff ≠ 0) :
    (Matrix.of (fun i j => (p j).eval (M.node i))).det ≠ 0 := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    M.node p (fun i => (hdeg i).le), Matrix.det_mul]
  apply mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr M.distinct)
  rw [Matrix.det_of_isUpperTriangular
    (Matrix.matrixOfPolynomials_isUpperTriangular p (fun i => (hdeg i).le))]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simpa only [Matrix.of_apply, ← hdeg i, coeff_natDegree] using hlc i

/-- Degree-graded polynomials remain linearly independent in the discrete L² model.
Use: invokes the proved positive-diagonal Cholesky construction.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: positive diagonal weighting preserves the invertible evaluation matrix. -/
theorem evaluate_linearIndependent (p : Fin N → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree = i.val) (hlc : ∀ i, (p i).leadingCoeff ≠ 0) :
    LinearIndependent ℝ (fun i => M.evaluate (p i)) := by
  -- The Vandermonde determinant and the positive diagonal weighting both remain invertible.
  let A := Matrix.diagonal (fun i => Real.sqrt (M.weight i)) *
    Matrix.of (fun i j => (p j).eval (M.node i))
  have hA : A.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ =>
      (Real.sqrt_pos.mpr (M.positive i)).ne')) (M.evaluation_det_ne_zero p hdeg hlc)
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hA
  have h := hli.map' (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.injective)
  convert h using 1
  funext i
  apply PiLp.ext
  intro k
  change Real.sqrt (M.weight k) * (p i).eval (M.node k) = A k i
  simp [A]

/-- The weighted polynomial Gram matrix is strictly positive definite.
Use: supplies the inverse principal Gram blocks in the Schur formulas.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: combine polynomial independence with mathlib's positive Gram theorem. -/
theorem gram_posDef (p : Fin N → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree = i.val) (hlc : ∀ i, (p i).leadingCoeff ≠ 0) :
    (Matrix.of (fun i j =>
      ∑ k, M.weight k * (p i).eval (M.node k) * (p j).eval (M.node k))).PosDef := by
  have h := Matrix.posDef_gram_of_linearIndependent (M.evaluate_linearIndependent p hdeg hlc)
  simpa only [Matrix.gram, Matrix.of_apply, inner_evaluate] using h

/-- Evaluation is faithful below the number of distinct atoms.
Use: turns identities of discrete L² vectors into actual polynomial identities.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: a nonzero polynomial of degree below N cannot vanish at N distinct nodes. -/
theorem evaluate_eq_zero {p : ℝ[X]} (hp : p.natDegree < N) (he : M.evaluate p = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p M.distinct
  · intro i
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) he
    change Real.sqrt (M.weight i) * p.eval (M.node i) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr (M.positive i)).ne'
  · simpa using hp

/-- Equal weighted evaluations determine bounded-degree polynomials uniquely.
Use: identifies reconstructed recurrence polynomials with the canonical orthonormal family.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: apply the root-counting result to the difference polynomial. -/
theorem evaluate_injective {p q : ℝ[X]} (hp : p.natDegree < N) (hq : q.natDegree < N)
    (he : M.evaluate p = M.evaluate q) : p = q := by
  apply sub_eq_zero.mp
  apply M.evaluate_eq_zero (lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hp hq))
  change M.evaluation (p-q) = 0
  rw [map_sub, show M.evaluation p = M.evaluation q from he, sub_self]

end DiscreteMeasure
end
end jacobi.Finite
