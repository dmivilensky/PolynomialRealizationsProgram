import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
Article: Appendix C, the finite-difference step in Lemma telescoping.
Use: zero-sum diagonal rows and zero value charge have local primitives,
with width reduced by one and a bound depending only on the original width.
The real spectral factorization is a separate obligation.
-/
namespace polyak.FiniteHorizon
open scoped BigOperators

/-- A finite prefix in a sequence indexed on all integer times. -/
def prefixSum (f : ℤ → ℝ) (j : ℤ) (a : ℕ) : ℝ :=
  ∑ r ∈ Finset.range a, f (j+r)

/-- The local primitive of a row of coefficients supported in 0,...,D. -/
def primitive (D : ℕ) (μ : ℕ → ℝ) (f : ℤ → ℝ) (j : ℤ) : ℝ :=
  ∑ a ∈ Finset.range (D+1), μ a * prefixSum f j a

/-- Shifting a finite prefix by one exposes just its two boundary terms. -/
theorem prefix_shift_sub (f : ℤ → ℝ) (j : ℤ) (a : ℕ) :
    prefixSum f (j+1) a-prefixSum f j a=f (j+a)-f j := by
  rw [prefixSum,prefixSum,← Finset.sum_sub_distrib]
  have he (r : ℕ) : j+1+(r : ℤ)=j+((r+1 : ℕ) : ℤ) := by push_cast; ring
  simp_rw [he]
  simpa using Finset.sum_range_sub (fun r : ℕ => f (j+r)) a

/-- Exact scalar telescoping for every zero-sum coefficient row. -/
theorem zero_sum_row_telescoping (D : ℕ) (μ : ℕ → ℝ)
    (hμ : ∑ a ∈ Finset.range (D+1), μ a=0) (f : ℤ → ℝ) (j : ℤ) :
    (∑ a ∈ Finset.range (D+1), μ a*f (j+a))=
      primitive D μ f (j+1)-primitive D μ f j := by
  symm
  unfold primitive
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ a ∈ Finset.range (D+1), μ a*(prefixSum f (j+1) a-prefixSum f j a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a ∈ Finset.range (D+1), μ a*(f (j+a)-f j) := by
      simp_rw [prefix_shift_sub]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,← Finset.sum_mul,hμ,zero_mul,sub_zero]

/-- The primitive only uses the first D entries, for arbitrary integer offsets. -/
theorem primitive_congr (D : ℕ) (μ : ℕ → ℝ) (f g : ℤ → ℝ) (j : ℤ)
    (h : ∀ r : ℕ, r<D → f (j+r)=g (j+r)) :
    primitive D μ f j=primitive D μ g j := by
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun value => μ a*value)
  unfold prefixSum
  apply Finset.sum_congr rfl
  intro r hr
  exact h r (by have h₁:=Finset.mem_range.mp ha; have h₂:=Finset.mem_range.mp hr; omega)

/-- The explicit coefficient size of the chosen primitive. -/
def primitiveSize (D : ℕ) (μ : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (D+1), |μ a| *(a : ℝ)

/-- Local telescoping increases the coefficient size by at most the width. -/
theorem primitiveSize_le (D : ℕ) (μ : ℕ → ℝ) :
    primitiveSize D μ ≤ (D : ℝ)*(∑ a ∈ Finset.range (D+1), |μ a|) := by
  unfold primitiveSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have ha' : a≤D := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hr : (a : ℝ)≤D := by exact_mod_cast ha'
  nlinarith [abs_nonneg (μ a)]

end polyak.FiniteHorizon

namespace polyak.FiniteHorizon
open scoped BigOperators

/-- The diagonal with lag e in a quadratic window. -/
def diagonalValue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (e : ℕ) (j : ℤ) : ℝ := inner ℝ (f j) (f (j+e))

/-- Triangular-row form of a quadratic/value window of width D. -/
def rowFunctional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  (∑ e ∈ Finset.range (D+1), ∑ a ∈ Finset.range (D-e+1),
    μ e a*diagonalValue f e (j+a)) + ∑ a ∈ Finset.range (D+1), d a*h (j+a)

/-- Explicit local primitive of the quadratic rows and value charge. -/
def rowPrimitive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  (∑ e ∈ Finset.range (D+1), primitive (D-e) (μ e) (diagonalValue f e) j)+
    primitive D d h j

/-- Zero diagonal coefficients and zero charge telescope in every real Hilbert space. -/
theorem rowFunctional_telescoping {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hμ : ∀ e≤D, ∑ a ∈ Finset.range (D-e+1), μ e a=0)
    (hd : ∑ a ∈ Finset.range (D+1), d a=0) (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    rowFunctional D μ d f h j=rowPrimitive D μ d f h (j+1)-rowPrimitive D μ d f h j := by
  unfold rowFunctional rowPrimitive
  have he (e : ℕ) (he : e∈Finset.range (D+1)) :=
    zero_sum_row_telescoping (D-e) (μ e)
      (hμ e (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))) (diagonalValue f e) j
  rw [Finset.sum_congr rfl he,zero_sum_row_telescoping D d hd h j,
    Finset.sum_sub_distrib]
  ring

/-- The primitive uses only D samples, one fewer than the original width-D window. -/
theorem rowPrimitive_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (f g : ℤ → E) (h k : ℤ → ℝ) (j : ℤ)
    (hf : ∀ r : ℕ, r<D → f (j+r)=g (j+r))
    (hh : ∀ r : ℕ, r<D → h (j+r)=k (j+r)) :
    rowPrimitive D μ d f h j=rowPrimitive D μ d g k j := by
  unfold rowPrimitive
  rw [primitive_congr D d h k j hh]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply primitive_congr
  intro r hr
  have he' : e≤D := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  have hre : r+e<D := by omega
  unfold diagonalValue
  have hi : j+(r : ℤ)+(e : ℤ)=j+((r+e : ℕ) : ℤ) := by push_cast; ring
  rw [hi,hf r (by omega),hf (r+e) hre]

end polyak.FiniteHorizon
