import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
Article: Definition 2.2 [def:latest] of krylov.tex.
Use: the data-only latest-information model and defect are the common inputs
to flag identities, correction formulas and information-radius bounds.
Source: the symmetric multipoint secant model of Burdakov (1983), cited as
Burdakov83 in main_krylov; the identities below are elementary matrix algebra.
-/

namespace krylov.Secant

open scoped Matrix
variable {ι R : Type*}

/-- Symmetrize the observed pairing matrix by retaining its newer observation.
Use: the model of every ordered secant window, independently of its rank.
Article: main_krylov, Definition def:latest, T̄ᵢⱼ = M_min(i,j),max(i,j).
Source: Burdakov83, symmetric multipoint secant construction. -/
def latest [LinearOrder ι] (M : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => M (min i j) (max i j)

/-- The antisymmetric part of the observed pairing matrix, without a factor 1/2.
Use: measures incompatible secant observations and drives the FC residual.
Article: main_krylov, Definition def:latest, D = M − Mᵀ. -/
def defect [Sub R] (M : Matrix ι ι R) : Matrix ι ι R := M - Mᵀ

/-- Retain exactly the strictly lower triangular entries of a matrix.
Use: states the exact relation between raw observations and their model.
Article: main_krylov, Lemma lem:flag, the operator tril. -/
def strictLower [LinearOrder ι] [Zero R] (M : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => if j < i then M i j else 0

/-- The latest-information construction always gives a symmetric model.
Use: permits symmetric correction solves even when the data are incompatible.
Article: main_krylov, Definition def:latest.
Proof: interchange the minimum and maximum arguments. -/
theorem latest_isSymm [LinearOrder ι] (M : Matrix ι ι R) : (latest M).IsSymm := by
  exact Matrix.IsSymm.ext fun i j => by simp only [latest, min_comm j i, max_comm j i]

/-- Above the diagonal the model agrees with the actual newer observation.
Use: identifies each model entry with the latest available secant operator.
Article: main_krylov, Definition def:latest.
Proof: evaluate minimum and maximum in their prescribed order. -/
theorem latest_apply_of_le [LinearOrder ι] (M : Matrix ι ι R) {i j : ι} (h : i ≤ j) :
    latest M i j = M i j := by
  simp only [latest, min_eq_left h, max_eq_right h]

/-- Compatible symmetric observations are fixed by the latest-information model.
Use: the model is exact on quadratic secant data.
Article: main_krylov, Definition def:latest and Lemma lem:consistent.
Proof: split the order of the indices and use symmetry below the diagonal. -/
theorem latest_eq_of_isSymm [LinearOrder ι] {M : Matrix ι ι R}
    (hM : M.IsSymm) : latest M = M := by
  ext i j
  rcases le_total i j with h | h
  · exact latest_apply_of_le M h
  · simpa only [latest, min_eq_right h, max_eq_left h] using hM.apply i j

/-- Transposing the observed defect reverses its sign.
Use: defect data have only one independent triangular half.
Article: main_krylov, Definition def:latest.
Proof: transposition swaps the two terms of the difference. -/
theorem defect_transpose [AddCommGroup R] (M : Matrix ι ι R) :
    (defect M)ᵀ = -defect M := by
  ext i j
  simp only [defect, Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, neg_sub]

/-- There is no observed defect on a diagonal entry.
Use: separates diagonal curvature uncertainty from observable commutators.
Article: main_krylov, Definition def:latest and Theorem thm:window.
Proof: the diagonal entry subtracts itself. -/
theorem defect_diag [AddCommGroup R] (M : Matrix ι ι R) (i : ι) : defect M i i = 0 := by
  exact sub_self _

/-- Raw observations differ from their model exactly by the lower defect.
Use: the third exact secant flag identity, with no independence assumption.
Article: main_krylov, Lemma lem:flag, M − T̄ = tril D.
Proof: above the diagonal the model retains M; below it the model retains Mᵀ. -/
theorem sub_latest [LinearOrder ι] [AddCommGroup R] (M : Matrix ι ι R) :
    M - latest M = strictLower (defect M) := by
  ext i j
  by_cases h : j < i
  · simp only [Matrix.sub_apply, latest, strictLower, defect, Matrix.transpose_apply,
      h, ite_true, min_eq_right h.le, max_eq_left h.le]
  · simp only [Matrix.sub_apply, latest, strictLower, h, ite_false,
      min_eq_left (le_of_not_gt h), max_eq_right (le_of_not_gt h), sub_self]

end krylov.Secant
