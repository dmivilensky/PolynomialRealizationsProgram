import krylov.Reference.CGPolynomials
import Mathlib.Algebra.Polynomial.Sequence

/-!
Article: main_krylov, s2:eq:cg, the genuine Krylov flag.
Use: identify the computed CG directions with the polynomial Krylov space,
before proving the energy minimum or a stopping criterion.
Source: the classical polynomial description of CG (Meurant06); the finite
degree-graded spanning argument reuses mathlib's Polynomial.Sequence.
-/

namespace krylov.Reference.CG
noncomputable section
open Polynomial
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Apply a polynomial in the actual reference operator to its initial gradient.
Use: expresses the Krylov flag without an assumed reference basis.
Article: main_krylov, s2:eq:cg, polynomial representation of the reference. -/
def polynomialAction (Q : E →L[ℝ] E) (g : E) : ℝ[X] →ₗ[ℝ] E :=
  (ContinuousLinearMap.apply ℝ E g).toLinearMap.comp (aeval Q).toLinearMap

/-- The actual two CG polynomial recurrences represent the actual two vector recurrences.
Use: the reference residual polynomial is computed by CG itself.
Article: main_krylov, s2:eq:cg.
Proof: induction applies the algebra homomorphism to each executed recurrence. -/
theorem polynomialAction_pair (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    polynomialAction Q g (residualPolynomial Q g k) = gradient Q g k ∧
      polynomialAction Q g (directionPolynomial Q g k) = direction Q g k := by
  -- Operator evaluation respects both executed recurrences, so the two representations are proved together.
  induction k with
  | zero => simp [polynomialAction, residualPolynomial, directionPolynomial, polynomialRun, gradient, direction, cgRun]
  | succ k ih =>
    have hr : polynomialAction Q g (residualPolynomial Q g (k+1)) = gradient Q g (k+1) := by
      rw [residualPolynomial_succ, map_add]
      simp only [polynomialAction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply, map_mul,
        aeval_C, aeval_X, mul_apply_eq_comp, ContinuousLinearMap.algebraMap_apply]
      change polynomialAction Q g (residualPolynomial Q g k) +
        length Q g k • Q (polynomialAction Q g (directionPolynomial Q g k)) = _
      rw [ih.1, ih.2, gradient_succ]
    refine ⟨hr, ?_⟩
    rw [directionPolynomial_succ, map_add, map_neg, hr]
    simp only [polynomialAction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply, map_mul,
      aeval_C, mul_apply_eq_comp, ContinuousLinearMap.algebraMap_apply]
    change -gradient Q g (k+1) + beta Q g k •
      polynomialAction Q g (directionPolynomial Q g k) = _
    rw [ih.2, direction_succ]

/-- Before breakdown the computed residual and direction polynomials have their exact indexed degrees.
Use: the actual directions span every admissible polynomial displacement.
Article: main_krylov, s2:eq:cg, the Krylov flag before exhaustion.
Proof: each positive line introduces one new leading term; the lower-degree
Fletcher--Reeves correction cannot cancel it. -/
theorem polynomial_exact_degree (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hl : ∀ i<k, length Q g i≠0) :
    (residualPolynomial Q g k).degree = k ∧ (directionPolynomial Q g k).degree = k := by
  -- Work with degree, including its bottom element, to justify every leading-term assertion.
  induction k with
  | zero => simp [residualPolynomial, directionPolynomial, polynomialRun]
  | succ k ih =>
    obtain ⟨hr, hd⟩ := ih (fun i hi => hl i (by omega))
    have hp : (C (length Q g k)*X*directionPolynomial Q g k).degree = (↑(k+1) : WithBot ℕ) := by
      rw [degree_mul, degree_mul, degree_C (hl k (by omega)), degree_X, hd]
      simp only [zero_add, Nat.cast_add, Nat.cast_one]
      ac_rfl
    have hnew : (residualPolynomial Q g (k+1)).degree = (↑(k+1) : WithBot ℕ) := by
      rw [residualPolynomial_succ, degree_add_eq_right_of_degree_lt (by rw [hr, hp]; exact_mod_cast Nat.lt_succ_self k), hp]
    refine ⟨hnew, ?_⟩
    rw [directionPolynomial_succ]
    apply (degree_add_eq_left_of_degree_lt ?_).trans
      ((degree_neg _).trans hnew)
    rw [degree_neg, hnew]
    by_cases hb : beta Q g k=0
    · simp [hb]
    · rw [degree_mul, degree_C hb, zero_add, hd]
      exact_mod_cast Nat.lt_succ_self k

/-- The polynomial Krylov flag consists of q(Q)g for degree q strictly below k.
Use: fixes the flag also at k=0 and after exhaustion.
Article: main_krylov, K_k=span{g,Ag,...,A^(k−1)g}. -/
def krylovSpace (Q : E →L[ℝ] E) (g : E) (k : ℕ) : Submodule ℝ E :=
  (degreeLT ℝ k).map (polynomialAction Q g)

/-- A finite degree-graded polynomial prefix, extended by monomials afterward.
Use: reuses the community spanning theorem with only finite nondegeneracy hypotheses.
Article: main_krylov, s2:eq:cg, finite Krylov flag. -/
def degreeSequence (p : ℕ → ℝ[X]) (m : ℕ) (hd : ∀ i<m, (p i).degree=i) : Polynomial.Sequence ℝ where
  elems' i := if i<m then p i else X^i
  degree_eq' i := by
    split_ifs with hi
    · exact hd i hi
    · simp

/-- Any genuinely degree-graded polynomial prefix spans the actual polynomial Krylov flag after operator evaluation.
Use: the residual and direction flags share one proved polynomial spanning argument.
Article: main_krylov, s2:eq:cg, the actual polynomial flag.
Proof: extend only the finite degree-graded prefix and map its proved full polynomial span into the state space. -/
theorem polynomialAction_span (Q : E →L[ℝ] E) (g : E) (p : ℕ → ℝ[X]) (k : ℕ)
    (hd : ∀ i<k, (p i).degree=i) :
    krylovSpace Q g k=Submodule.span ℝ ((fun i => polynomialAction Q g (p i)) '' Set.Iio k) := by
  -- Mapping the full low-degree polynomial span proves equality, not only membership of the computed vectors.
  let S := degreeSequence p k hd
  have hs := S.span_degreeLT (m := k) (fun i _ => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (S.ne_zero i)))
  rw [krylovSpace, ← hs, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨q, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, by simp only [S, degreeSequence, ite_eq_left (show i<k from hi)]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨S i, ⟨i, hi, rfl⟩, by simp only [S, degreeSequence, ite_eq_left (show i<k from hi)]⟩

/-- The actual first k CG directions span precisely the actual polynomial Krylov flag.
Use: converts residual orthogonality to the full variational condition.
Article: main_krylov, s2:eq:cg, the reference Krylov flag.
Proof: apply the common finite polynomial flag theorem to the actual direction polynomials. -/
theorem krylovSpace_eq_span_directions (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hl : ∀ i<k, length Q g i≠0) :
    krylovSpace Q g k=Submodule.span ℝ (direction Q g '' Set.Iio k) := by
  have hd (i : ℕ) (hi : i<k) := (polynomial_exact_degree Q g i (fun j hj => hl j (hj.trans hi))).2
  simpa only [(polynomialAction_pair Q g _).2] using polynomialAction_span Q g (directionPolynomial Q g) k hd

/-- The actual first k gradients span precisely the same polynomial Krylov flag.
Use: the normalized computed residuals form its actual Lanczos basis.
Article: main_krylov, s2:eq:cg and prop:dict(i), residual Krylov flag.
Proof: apply the same degree-graded spanning theorem to the computed residual polynomials. -/
theorem krylovSpace_eq_span_gradients (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hl : ∀ i<k, length Q g i≠0) :
    krylovSpace Q g k=Submodule.span ℝ (gradient Q g '' Set.Iio k) := by
  have hd (i : ℕ) (hi : i<k) := (polynomial_exact_degree Q g i (fun j hj => hl j (hj.trans hi))).1
  simpa only [(polynomialAction_pair Q g _).1] using polynomialAction_span Q g (residualPolynomial Q g) k hd

/-- The computed residual is orthogonal to the whole preceding Krylov space.
Use: establishes the CG Galerkin condition from the executed recurrence.
Article: main_krylov, s2:eq:cg, classical CG energy minimization.
Proof: the actual invariant kills each preceding direction, and these span the actual flag. -/
theorem gradient_orthogonal_krylov (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, gradient Q g i≠0) {v : E} (hv : v∈krylovSpace Q g k) :
    inner ℝ v (gradient Q g k)=0 := by
  -- The actual direction invariant annihilates the entire proved Krylov span.
  have hk := invariant Q hQ hpos g k hg
  rw [krylovSpace_eq_span_directions Q g k (fun i hi => (hk.lines_pos i hi).ne')] at hv
  have hle : Submodule.span ℝ (direction Q g '' Set.Iio k) ≤
      (innerSL ℝ (gradient Q g k)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change inner ℝ (gradient Q g k) (direction Q g i)=0
    rw [real_inner_comm]
    exact hk.old_direction i hi
  have he := hle hv
  change inner ℝ (gradient Q g k) v=0 at he
  rwa [real_inner_comm] at he

end
end krylov.Reference.CG
