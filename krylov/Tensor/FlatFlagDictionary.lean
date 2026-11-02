import krylov.Tensor.FlatPrefixResponse
import krylov.Tensor.CubicUncurrying

/-!
Article: main_krylov, apG:flat, actual midpoint/flag dictionary.
Use: identify the true flat compatible response with the prefix expression
to which the genuine dyadic estimate applies.
Source: direct finite summation of the symmetric bilinear midpoint slices.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Direct summation of real adjacent midpoint slices gives exactly the
quadratic-prefix expression printed as sym N_a.
Article: main_krylov, apG:flat. -/
theorem flat_midpoint_prefix_sum (e : ℕ → E) (T : SymmetricCubic E) (x : E) (b : ℕ) :
    (∑ l ∈ range b, T.form x (e (l+1) + e l) (∑ j ∈ range (l+1), e j)) =
      T.form x (∑ j ∈ range b, e j) (∑ j ∈ range b, e j) +
        T.form x (e b) (∑ j ∈ range b, e j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [map_add, _root_.add_apply]
    rw [T.swap₂ x (∑ j ∈ range b, e j) (e b)]
    ring

/-- The actual finite orthogonal family, extended by zero only outside its
original finite index set. Article: main_krylov, apG:flat. -/
def flatExtend {N : ℕ} (e : Fin N → E) (j : ℕ) : E :=
  if h : j < N then e ⟨j, h⟩ else 0

omit [InnerProductSpace ℝ E] in
/-- Within its original index set the actual extension is the original family.
Article: main_krylov, apG:flat. -/
theorem flatExtend_fin {N : ℕ} (e : Fin N → E) (a : Fin N) : flatExtend e a.val = e a := by
  simp only [flatExtend, dite_eq_left a.isLt]

omit [InnerProductSpace ℝ E] in
/-- The finite strict-prefix vector is precisely its actual ordinary finite
range sum. Article: main_krylov, apG:flat. -/
theorem flatPrefixVector_range {N : ℕ} (e : Fin N → E) (a : Fin N) :
    flatPrefixVector e a = ∑ j ∈ range a.val, flatExtend e j := by
  unfold flatPrefixVector
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact mem_range.mpr (mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, (mem_range.mp hj).trans a.isLt⟩, mem_filter.mpr ⟨mem_univ _, mem_range.mp hj⟩, rfl⟩
  · intro i _
    exact (flatExtend_fin e i).symm

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A true finite threshold sum is exactly its ordinary range sum.
Article: main_krylov, apG:flat, reversing the finite old flags. -/
theorem flat_fin_threshold_sum (m b : ℕ) (hb : b ≤ m) (f : ℕ → ℝ) :
    (∑ l : Fin m, if l.val < b then f l.val else 0) = ∑ l ∈ range b, f l := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun l _ => l.val)
  · intro l hl
    exact mem_range.mpr (mem_filter.mp hl).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, (mem_range.mp hj).trans_le hb⟩, mem_filter.mpr ⟨mem_univ _, mem_range.mp hj⟩, rfl⟩
  · intro _ _
    rfl

/-- The actual adjacent flat midpoint increments, in reversed coordinates.
Article: main_krylov, apG:flat. -/
def flatReverseMidpoint {N : ℕ} (e : Fin N → E) (l : Fin (N-1)) : E :=
  (2 : ℝ)⁻¹ • (flatExtend e (l.val+1) + flatExtend e l.val)

/-- The actual remaining flat tail in reversed coordinates.
Article: main_krylov, apG:flat. -/
def flatReverseTail {N : ℕ} (e : Fin N → E) (l : Fin (N-1)) : E :=
  ∑ j ∈ range (l.val+1), flatExtend e j

/-- The genuine flat old flags, with their original order reversed.
Article: main_krylov, apG:flat. -/
def flatReverseFlag (N : ℕ) (l : Fin (N-1)) : Finset (Fin N) :=
  univ.filter (fun a => l.val < a.val)

/-- Direct summation identifies the genuine flat old-flag response with the
real prefix formula used in the dyadic proof. Article: main_krylov, apG:flat. -/
theorem flatReverseResponse_eq {N : ℕ} (e : Fin N → E) (T : SymmetricCubic E) :
    flagResponse e (flatReverseFlag N) (flatReverseMidpoint e) (flatReverseTail e)
      (cubicUncurried T) = flatPrefixResponse e T := by
  unfold flagResponse flatReverseFlag
  simp only [sum_filter, cubicUncurried_apply]
  rw [Finset.sum_comm]
  unfold flatPrefixResponse
  apply sum_congr rfl
  intro a _
  change (∑ l : Fin (N-1), if l.val < a.val then
    T.form (e a) (flatReverseMidpoint e l) (flatReverseTail e l) • e a else 0) = _
  simp only [← zero_smul ℝ (e a), ← ite_smul, ← sum_smul]
  congr 1
  have hterm (l : Fin (N-1)) :
      (if l.val < a.val then T.form (e a) (flatReverseMidpoint e l) (flatReverseTail e l) else 0) =
        (2 : ℝ)⁻¹ * (if l.val < a.val then T.form (e a)
          (flatExtend e (l.val+1) + flatExtend e l.val)
          (∑ j ∈ range (l.val+1), flatExtend e j) else 0) := by
    by_cases h : l.val < a.val <;>
      simp only [h, ite_true, ite_false, flatReverseMidpoint, flatReverseTail,
        map_smul, smul_apply, smul_eq_mul, mul_zero]
  simp_rw [hterm]
  rw [← mul_sum, flat_fin_threshold_sum (N-1) a.val (by have := a.isLt; omega)
    (fun l => T.form (e a) (flatExtend e (l+1) + flatExtend e l)
      (∑ j ∈ range (l+1), flatExtend e j)),
    flat_midpoint_prefix_sum, ← flatPrefixVector_range, flatExtend_fin]

end
end krylov.Tensor
