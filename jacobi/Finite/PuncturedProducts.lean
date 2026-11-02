import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Finite products with one omitted lattice index split into the points before
and after that index. This elementary bookkeeping makes the support-weight
calculation an identity for the actual characteristic gaps.
Source: elementary finite-product identities.
Use: the cosine-lattice characteristic derivative splits into its left and right sine factors, which determine the actual support probabilities.
-/
namespace jacobi.Finite
open Finset

/-- Omitting one index separates a finite product into its two contiguous parts.
Use: the cosine-lattice characteristic derivative splits into its left and right sine factors, which determine the actual support probabilities.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the erased interval is the disjoint union of its two sides; translate the second side back to a zero-based range. -/
theorem punctured_product {M : Type*} [CommMonoid M] (f : ℕ → M)
    {n k : ℕ} (hk : k≤n) :
    (∏j∈(range (n+1)).erase k,f j)=
      (∏j∈range k,f j)*(∏j∈range (n-k),f (k+1+j)) := by
  -- Keep the omitted point out of both products, including at either endpoint.
  have hs : (range (n+1)).erase k=range k∪Ico (k+1) (n+1) := by
    ext j
    simp only [mem_erase,mem_range,mem_union,mem_Ico]
    omega
  have hd : Disjoint (range k) (Ico (k+1) (n+1)) := by
    rw [disjoint_left]
    intro j hj hj'
    simp only [mem_range,mem_Ico] at hj hj'
    omega
  rw [hs,prod_union hd,prod_Ico_eq_prod_range]
  rw [show n+1-(k+1)=n-k by omega]

/-- A product over an erased finite type is the same original product over natural lattice indices.
Use: naturalMeasure_adjacent_ratio applies the interval product identities to the genuine finite characteristic derivative.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the value map is a bijection from the erased finite type to the erased natural range. -/
theorem fin_punctured_product {M : Type*} [CommMonoid M] (f : ℕ → M)
    {n : ℕ} (k : Fin (n+1)) :
    (∏j∈(univ : Finset (Fin (n+1))).erase k,f j)=
      ∏j∈(range (n+1)).erase (k:ℕ),f j := by
  -- The value map preserves the omitted index and bijects the remaining finite nodes.
  apply prod_bij (fun (j:Fin (n+1)) _ => (j:ℕ))
  · intro j hj
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp hj).1 (Fin.ext he),mem_range.mpr j.isLt⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j,mem_range.mp (mem_erase.mp hj).2⟩,?_,rfl⟩
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp hj).1 (congrArg Fin.val he),mem_univ _⟩
  · intro _ _
    rfl

/-- Sliding a finite window of factors replaces precisely its first factor by the next endpoint.
Use: the sum-angle sine product telescopes between two adjacent support nodes in the exact spectral-weight ratio.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: expand the same product with one additional term at its two endpoints and reassociate. -/
theorem sliding_product {M : Type*} [CommMonoid M] (f : ℕ → M) (n k : ℕ) :
    (∏j∈range (n+1),f (k+1+j))*f k=
      (∏j∈range (n+1),f (k+j))*f (k+n+1) := by
  have h := prod_range_succ' (fun j => f (k+j)) (n+1)
  rw [prod_range_succ] at h
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.add_zero] using h.symm

end jacobi.Finite
