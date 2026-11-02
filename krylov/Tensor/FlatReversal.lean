import krylov.Tensor.FlatFlagDictionary
import Mathlib.Data.Fin.Rev

/-!
Article: main_krylov, apG:flat, the actual reversal of the flat CG flags.
Use: identify the genuine chronological midpoint/tail response with the
proved dyadic prefix response, without an assumed coordinate dictionary.
Source: finite permutation of the actual orthogonal frame.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual chronological flat midpoint increment.
Article: main_krylov, apG:flat. -/
def flatForwardMidpoint (e : Fin N → E) (l : Fin (N-1)) : E :=
  (2 : ℝ)⁻¹ • (flatExtend e l.val + flatExtend e (l.val+1))

/-- The actual chronological flat remaining tail.
Article: main_krylov, apG:flat. -/
def flatForwardTail (e : Fin N → E) (l : Fin (N-1)) : E :=
  ∑ a : Fin N, if l.val < a.val then e a else 0

/-- The actual chronological old flag of a flat profile.
Article: main_krylov, apG:flat. -/
def flatForwardFlag (N : ℕ) (l : Fin (N-1)) : Finset (Fin N) :=
  univ.filter (fun a => a.val ≤ l.val)

omit [InnerProductSpace ℝ E] in
/-- The real chronological flat tail becomes precisely the genuine prefix
under reversal. Article: main_krylov, apG:flat. -/
theorem flatForwardTail_rev (e : Fin N → E) (l : Fin (N-1)) :
    flatForwardTail e l.rev = flatReverseTail (fun a => e a.rev) l := by
  have hm : l.val + 1 < N := by have := l.isLt; omega
  rw [show flatReverseTail (fun a => e a.rev) l =
      flatPrefixVector (fun a => e a.rev) ⟨l.val+1, hm⟩ by
        exact (flatPrefixVector_range (fun a : Fin N => e a.rev) (⟨l.val+1, hm⟩ : Fin N)).symm]
  unfold flatForwardTail flatPrefixVector
  rw [← Equiv.sum_comp Fin.revPerm]
  apply sum_congr rfl
  intro a _
  change (if l.rev.val < a.rev.val then e a.rev else 0) =
    (if a.val < l.val+1 then e a.rev else 0)
  have hp : l.rev.val < a.rev.val ↔ a.val < l.val+1 := by
    have := l.isLt
    have := a.isLt
    simp only [Fin.val_rev]
    omega
  simp only [hp]

/-- The actual adjacent midpoint increment reverses to the actual adjacent
prefix midpoint increment. Article: main_krylov, apG:flat. -/
theorem flatForwardMidpoint_rev (e : Fin N → E) (l : Fin (N-1)) :
    flatForwardMidpoint e l.rev = flatReverseMidpoint (fun a => e a.rev) l := by
  have hl : l.val < N := by have := l.isLt; omega
  have hl1 : l.val+1 < N := by have := l.isLt; omega
  have hr : l.rev.val < N := by have := l.rev.isLt; omega
  have hr1 : l.rev.val+1 < N := by have := l.rev.isLt; omega
  have h0 : (⟨l.rev.val, hr⟩ : Fin N) = (⟨l.val+1, hl1⟩ : Fin N).rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := l.isLt
    omega
  have h1 : (⟨l.rev.val+1, hr1⟩ : Fin N) = (⟨l.val, hl⟩ : Fin N).rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := l.isLt
    omega
  simp only [flatForwardMidpoint, flatReverseMidpoint, flatExtend,
    dite_eq_left hr, dite_eq_left hr1, dite_eq_left hl, dite_eq_left hl1, h0, h1]

/-- Chronological flat old flags and actual midpoint/tail vectors give exactly
the true prefix response after reversal. Article: main_krylov, apG:flat. -/
theorem flatForwardResponse_eq (e : Fin N → E) (T : SymmetricCubic E) :
    flagResponse e (flatForwardFlag N) (flatForwardMidpoint e) (flatForwardTail e)
      (cubicUncurried T) = flatPrefixResponse (fun a => e a.rev) T := by
  rw [← flatReverseResponse_eq]
  unfold flagResponse flatForwardFlag flatReverseFlag
  simp only [sum_filter]
  rw [← Equiv.sum_comp (Fin.revPerm (n := N-1))]
  apply sum_congr rfl
  intro l _
  rw [← Equiv.sum_comp (Fin.revPerm (n := N))]
  apply sum_congr rfl
  intro a _
  change (if a.rev.val ≤ l.rev.val then
      cubicUncurried T ![e a.rev, flatForwardMidpoint e l.rev, flatForwardTail e l.rev] • e a.rev else 0) = _
  rw [flatForwardMidpoint_rev, flatForwardTail_rev]
  have hp : a.rev.val ≤ l.rev.val ↔ l.val < a.val := by
    have := a.isLt
    have := l.isLt
    simp only [Fin.val_rev]
    omega
  simp only [hp]

/-- The printed logarithmic bound holds for the actual chronological flat
compatible response. Article: main_krylov, apG:flat. -/
theorem norm_flatForwardResponse_le [FiniteDimensional ℝ E]
    (e : Fin N → E) (he : Orthonormal ℝ e) (T : SymmetricCubic E)
    (hd : ∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ 2) (hN : 2 ≤ N) :
    ‖flagResponse e (flatForwardFlag N) (flatForwardMidpoint e) (flatForwardTail e)
      (cubicUncurried T)‖ ≤ 10 * N * Real.logb 2 (4 * N) := by
  rw [flatForwardResponse_eq]
  exact norm_flatPrefixResponse_le _ (he.comp Fin.rev Fin.rev_injective) T hd hN

end
end krylov.Tensor
