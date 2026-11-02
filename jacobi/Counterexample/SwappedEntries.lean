import jacobi.Counterexample.SwappedInverse
import jacobi.Finite.MatrixEncoding

/-!
Article: jacobi, Proposition 6.1.
Exact entries of the original swapped matrix identify it with a genuine
finite Jacobi chain. Positivity of its original factor coefficients
gives its positive couplings; the characteristic polynomial and inverse
diagonal remain the already proved actual matrix quantities.
Use: swapped_entry computes every entry of B^T*B without an assumed band formula.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Multiplying an original bidiagonal column has exactly its two genuine nonzero physical terms.
Use: swapped_entry computes every entry of B^T*B without an assumed band formula.
Article: jacobi, Proposition 6.1.
Proof: split the original diagonal and subdiagonal finite sums; each
has singleton support, with the missing last subdiagonal term zero. -/
theorem bidiagonal_column_mul {N:ℕ} (d l:ℕ→ℝ) (i:Fin N) (f:Fin N→ℝ) :
    (∑k:Fin N,bidiagonal d l N k i*f k)=d i*f i+
      if h:i.val+1<N then l (i.val+1)*f ⟨i.val+1,h⟩ else 0 := by
  classical
  -- The finite upper endpoint is retained, so no artificial last coupling is included.
  simp only [bidiagonal,Bidiagonal.matrix,add_mul,Finset.sum_add_distrib]
  have hdiag : (∑k:Fin N,(if k=i then d k else 0)*f k)=d i*f i := by simp [ite_mul]
  rw [hdiag]
  congr 1
  by_cases hi : i.val+1<N
  · simp only [hi,dite_true]
    have he (k:Fin N) : i.val+1=k.val ↔ k=⟨i.val+1,hi⟩ := by
      rw [Fin.ext_iff]
      exact eq_comm
    simp only [he,ite_mul,zero_mul]
    simp
  · have he (k:Fin N) : ¬i.val+1=k.val := by omega
    simp only [hi,dite_false,he,ite_false,zero_mul,Finset.sum_const_zero]

/-- Every actual swapped matrix entry has exactly the source's diagonal and two adjacent products.
Use: swappedJacobi_matrix and swappedJacobi_irreducible prove that the actual constant-inverse-diagonal matrix is an admissible genuine positive-coupling chain.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the genuine two-term column formula computes B^T*B. At most
the diagonal and one neighboring column overlap; the original finite
last row retains precisely its missing-boundary convention. -/
theorem swapped_entry {N:ℕ} (d l:ℕ→ℝ) (i j:Fin N) :
    swappedGram d l N i j=
      if i=j then (d i)^2+(if i.val+1<N then (l (i.val+1))^2 else 0)
      else if i.val+1=j.val then l j*d j
      else if j.val+1=i.val then d i*l i else 0 := by
  classical
  -- Column overlap computes the genuine matrix, independently of its later Jacobi encoding.
  change (∑k:Fin N,bidiagonal d l N k i*bidiagonal d l N k j)=_
  rw [bidiagonal_column_mul]
  by_cases hi : i.val+1<N
  · rw [dite_eq_left hi]
    have hnext (j:Fin N) : (⟨i.val+1,hi⟩:Fin N)=j ↔ i.val+1=j.val := Fin.ext_iff
    have hsame : j.val+1=i.val+1 ↔ i=j := by rw [Nat.add_right_cancel_iff,Fin.ext_iff]; exact eq_comm
    simp only [bidiagonal,Bidiagonal.matrix,hnext,hsame]
    by_cases hij : i=j
    · subst j
      simp only [ite_true,show ¬i.val+1=i.val by omega,ite_false,zero_add,add_zero,hi]
      ring
    · by_cases hu : i.val+1=j.val
      · have hp : ¬j.val+1=i.val := by omega
        simp only [hij,ite_false,hu,ite_true,hp,zero_add,add_zero,mul_zero]
      · by_cases hl : j.val+1=i.val
        · simp only [hij,ite_false,hu,hl,ite_true,zero_add,add_zero,mul_zero]
        · simp only [hij,ite_false,hu,hl,add_zero,mul_zero]
  · rw [dite_eq_right hi]
    have hu : ¬i.val+1=j.val := by omega
    simp only [bidiagonal,Bidiagonal.matrix,add_zero]
    by_cases hij : i=j
    · subst j
      simp only [ite_true,hi,ite_false,show ¬i.val+1=i.val by omega,add_zero]
      ring
    · by_cases hl : j.val+1=i.val
      · simp only [hij,ite_false,hu,hl,ite_true,zero_add]
      · simp only [hij,ite_false,hu,hl,zero_add,mul_zero]

end
end jacobi.Counterexample
