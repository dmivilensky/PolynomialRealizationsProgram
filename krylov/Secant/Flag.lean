import krylov.Secant.Model
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
Article: Lemma 2.3 [lem:flag] of krylov.tex.
Use: decompose the exact window model error into old-flag compressions and
the observed defect into commutators, before any perturbative approximation.
Source: entrywise telescoping of the compressed symmetric operators Sᵀ Aₖ S;
finite telescoping and diagonal multiplication are reused from mathlib.
-/

namespace krylov.Secant

open scoped Matrix BigOperators

/-- The coordinate projector onto the first l+1 entries of an ordered window.
Use: compression onto the old secant flag in the exact flag identities.
Article: main_krylov, Lemma lem:flag, I_≤l. -/
def prefixProjection (p l : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal fun i => if i.val ≤ l then 1 else 0

/-- The pairing matrix obtained by observing column j at operator time j.
Use: Cₖ = Sᵀ Aₖ S specializes this data to actual secant pairs.
Article: main_krylov, Definition def:latest and Lemma lem:flag, Mᵢⱼ. -/
def observed {p : ℕ} (C : ℕ → Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => C j.val i j

/-- A compressed entry survives precisely when both indices belong to the flag.
Use: reduces the model-error identity to a single scalar telescoping sum.
Article: main_krylov, Lemma lem:flag, I_≤l X I_≤l.
Proof: multiply by the two diagonal indicator matrices. -/
theorem prefix_compression_apply {p : ℕ} (l : ℕ) (X : Matrix (Fin p) (Fin p) ℝ)
    (i j : Fin p) :
    (prefixProjection p l * X * prefixProjection p l) i j =
      if max i.val j.val ≤ l then X i j else 0 := by
  simp only [prefixProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi, hj]

/-- The upper observation uses the operator at the later of the two indices.
Use: identifies the exact terminal model error without choosing a step basis.
Article: main_krylov, Appendix A, apA:eq:entries.
Proof: choose the upper triangle and use symmetry in the lower triangle. -/
theorem latest_observed_apply {p : ℕ} (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k, (C k).IsSymm) (i j : Fin p) :
    latest (observed C) i j = C (max i.val j.val) i j := by
  rcases le_total i j with h | h
  · simp only [latest, min_eq_left h, max_eq_right h, observed,
      max_eq_right (show i.val ≤ j.val from h)]
  · simpa only [latest, min_eq_right h, max_eq_left h, observed,
      max_eq_left (show j.val ≤ i.val from h)] using (hC i.val).apply i j

/-- A terminal tail of consecutive differences is its endpoint difference.
Use: each model-error entry contains exactly the increments after its newer index.
Article: main_krylov, proof of Lemma lem:flag.
Source: mathlib Finset.sum_Ico_sub, finite telescoping.
Proof: identify the filtered range with the half-open interval and telescope. -/
theorem sum_tail_sub (f : ℕ → ℝ) {a p : ℕ} (h : a ≤ p) :
    (∑ l ∈ Finset.range p, if a ≤ l then f (l + 1) - f l else 0) = f p - f a := by
  rw [← Finset.sum_filter]
  have hs : (Finset.range p).filter (fun l => a ≤ l) = Finset.Ico a p := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
  rw [hs]
  exact Finset.sum_Ico_sub f h

/-- The newest operator minus the secant model is the sum of old-flag compressions.
Use: the exact hidden-curvature identity underlying the information radius and RFC.
Article: main_krylov, Lemma lem:flag, first identity.
Proof: each entry is the telescoping tail beginning at the newer column index. -/
theorem model_error_eq_sum_compressions {p : ℕ}
    (C : ℕ → Matrix (Fin p) (Fin p) ℝ) (hC : ∀ k, (C k).IsSymm) :
    C p - latest (observed C) = ∑ l ∈ Finset.range p,
      prefixProjection p l * (C (l + 1) - C l) * prefixProjection p l := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, prefix_compression_apply,
    latest_observed_apply C hC]
  exact (sum_tail_sub (fun k => C k i j) (max_le i.isLt.le j.isLt.le)).symm

/-- A flag commutator keeps the two opposite cross blocks with opposite signs.
Use: expresses the observable part of each increment entrywise.
Article: main_krylov, Lemma lem:flag, [I_≤l,X].
Proof: left and right multiplication select the respective row and column. -/
theorem prefix_commutator_apply {p : ℕ} (l : ℕ) (X : Matrix (Fin p) (Fin p) ℝ)
    (i j : Fin p) :
    (prefixProjection p l * X - X * prefixProjection p l) i j =
      (if i.val ≤ l then X i j else 0) - (if j.val ≤ l then X i j else 0) := by
  simp only [prefixProjection, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi, hj]

/-- The observed secant defect is exactly the sum of increment commutators.
Use: the second exact flag identity, with the last zero commutator omitted.
Article: main_krylov, Lemma lem:flag, D = ∑_(l<p−1) [I_≤l,X_l].
Proof: telescope the row and column tails to their common endpoint and cancel it. -/
theorem defect_eq_sum_commutators {p : ℕ}
    (C : ℕ → Matrix (Fin p) (Fin p) ℝ) (hC : ∀ k, (C k).IsSymm) :
    defect (observed C) = ∑ l ∈ Finset.range (p - 1),
      (prefixProjection p l * (C (l + 1) - C l) -
        (C (l + 1) - C l) * prefixProjection p l) := by
  ext i j
  -- The two scalar tails have the same terminal value C_(p−1).
  change C j.val i j - C i.val j i = _
  simp_rw [Matrix.sum_apply, prefix_commutator_apply]
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [sum_tail_sub (fun k => C k i j) (Nat.le_sub_one_of_lt i.isLt),
    sum_tail_sub (fun k => C k i j) (Nat.le_sub_one_of_lt j.isLt), (hC i.val).apply i j]
  ring

/-- Apply each segment operator to its own column of the actual step matrix.
Use: the real secant data Y have exactly these columns yⱼ = Aⱼ sⱼ.
Article: main_krylov, Definition def:model and Lemma lem:flag. -/
def pairImages {n p : ℕ} (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  fun a j => (A j.val * S) a j

/-- The compressed-operator observations are precisely the actual pairings SᵀY.
Use: connects the abstract compressed flag calculus to the article's step data.
Article: main_krylov, Lemma lem:flag, M = SᵀY.
Proof: associate each matrix product before evaluating its observed column. -/
theorem observed_compression {n p : ℕ} (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    observed (fun k => Sᵀ * A k * S) = Sᵀ * pairImages S A := by
  ext i j
  change (Sᵀ * A j.val * S) i j = _
  rw [Matrix.mul_assoc]
  rfl

/-- All three exact secant flag identities hold for the actual physical operators.
Use: the common algebraic foundation for unresolved curvature and adaptive corrections.
Article: main_krylov, Lemma lem:flag, all three displayed identities.
Proof: compress the symmetric operators by S, apply the two telescoping identities
and identify their observations with SᵀY; the third identity is data-only. -/
theorem flag_identities {n p : ℕ} (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm) :
    let M := Sᵀ * pairImages S A
    let X := fun l => Sᵀ * (A (l + 1) - A l) * S
    (Sᵀ * A p * S - latest M = ∑ l ∈ Finset.range p,
      prefixProjection p l * X l * prefixProjection p l) ∧
    (defect M = ∑ l ∈ Finset.range (p - 1),
      (prefixProjection p l * X l - X l * prefixProjection p l)) ∧
    (M - latest M = strictLower (defect M)) := by
  -- Congruence preserves symmetry without any rank or positivity assumption on S.
  have hC (k : ℕ) : (Sᵀ * A k * S).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
      (hA k).eq, Matrix.mul_assoc]
  have hmodel := model_error_eq_sum_compressions (fun k => Sᵀ * A k * S) hC
  have hdefect := defect_eq_sum_commutators (fun k => Sᵀ * A k * S) hC
  simp only [observed_compression, ← Matrix.sub_mul, ← Matrix.mul_sub] at hmodel hdefect
  exact ⟨hmodel, hdefect, sub_latest _⟩

end krylov.Secant
