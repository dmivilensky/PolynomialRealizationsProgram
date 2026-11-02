import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Rectangular bidiagonal factors give actual finite Darboux deletion.
The formulas below are elementary real matrix identities; the support
chain later supplies its original positive square-root coefficients.
Use: supportDarbouxFactor specializes this matrix to the genuine support coefficients and identifies its two Gram products with the original and shifted finite chains.
-/
namespace jacobi.Support
noncomputable section
open Matrix Finset

/-- The rectangular first-difference factor with its actual original adjacent real weights.
Use: supportDarbouxFactor specializes this matrix to the genuine support coefficients and identifies its two Gram products with the original and shifted finite chains.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def bidiagonal (n : ℕ) (p q : ℕ → ℝ) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  fun i j => (if j=i.castSucc then p i else 0)-(if j=i.succ then q i else 0)

/-- Multiplying an actual bidiagonal row against any genuine finite column uses exactly its two adjacent original values.
Use: bidiagonal_rows_diagonal and bidiagonal_rows_upper compute the smaller actual Darboux Gram matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the elementary two-term finite sum identity.
Proof: distribute the original difference and evaluate its two singleton-supported sums. -/
theorem bidiagonal_row_sum (n : ℕ) (p q : ℕ → ℝ) (i : Fin n) (f : Fin (n+1) → ℝ) :
    (∑ j,bidiagonal n p q i j*f j)=p i*f i.castSucc-q i*f i.succ := by
  simp [bidiagonal,sub_mul,ite_mul,sum_sub_distrib]

/-- A finite sum supported at one actual natural-coordinate index has its genuine indexed value, or zero outside the finite block.
Use: bidiagonal_column_sum handles the physical boundary columns of the rectangular deletion without an informal missing-index convention.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: evaluation of a singleton-supported finite sum.
Proof: inside the actual finite block use the unique subtype index; outside it every original finite coordinate is different. -/
theorem sum_at_coordinate (n m : ℕ) (f : Fin n → ℝ) :
    (∑ i:Fin n,if (i:ℕ)=m then f i else 0)=if hm:m<n then f ⟨m,hm⟩ else 0 := by
  -- The genuine index exists only inside the block; otherwise every summand is zero.
  by_cases hm : m<n
  · rw [dite_eq_left hm]
    have he (i:Fin n) : (i:ℕ)=m ↔ i=⟨m,hm⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [he,sum_ite_eq',mem_univ,ite_true]
  · rw [dite_eq_right hm]
    apply sum_eq_zero
    intro i _
    have hne : (i:ℕ)≠m := fun h => hm (h ▸ i.isLt)
    exact ite_eq_right hne

/-- Multiplying any genuine finite column against an original bidiagonal column has exactly its two original adjacent contributions, with the genuine zero boundary terms retained.
Use: the larger actual Darboux Gram matrix is identified with the original support matrix, including its first and last rows.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: finite matrix multiplication and singleton-supported sums.
Proof: distribute the original two indicator terms. Each is a genuine singleton at its physical index; the lower one is absent at zero, and the upper one is absent at the final column. -/
theorem bidiagonal_column_sum (n : ℕ) (p q : ℕ → ℝ) (j : Fin (n+1)) (f : Fin n → ℝ) :
    (∑ i:Fin n,bidiagonal n p q i j*f i)=
      (if hj:(j:ℕ)<n then p j*f ⟨j,hj⟩ else 0)-
      (if hj:0<(j:ℕ) then q ((j:ℕ)-1)*f ⟨(j:ℕ)-1,by omega⟩ else 0) := by
  -- The boundary cases are handled in the original finite sum, before any adjacent index is constructed.
  have he1 (i:Fin n) : j=i.castSucc ↔ (i:ℕ)=(j:ℕ) := by simp only [Fin.ext_iff,Fin.val_castSucc,eq_comm]
  have he2 (i:Fin n) : j=i.succ ↔ (i:ℕ)+1=(j:ℕ) := by simp only [Fin.ext_iff,Fin.val_succ,eq_comm]
  simp only [bidiagonal,sub_mul,ite_mul,zero_mul,sum_sub_distrib,he1,he2]
  rw [sum_at_coordinate]
  congr 1
  by_cases hj : 0<(j:ℕ)
  · have he (i:Fin n) : (i:ℕ)+1=(j:ℕ) ↔ (i:ℕ)=(j:ℕ)-1 := by omega
    simp only [he,sum_at_coordinate,dite_eq_left hj,show (j:ℕ)-1<n by omega,dite_eq_left]
  · have hz : (j:ℕ)=0 := by omega
    simp only [hz,Nat.add_one_ne_zero,ite_false,sum_const_zero,lt_self_iff_false,dite_false]

/-- The smaller actual Darboux Gram diagonal is the sum of the original two squared row factors.
Use: the original shifted diagonal sine identity identifies this with the smaller original support matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the row has exactly its two original adjacent nonzero entries; their genuine squared values give the diagonal. -/
theorem bidiagonal_rows_diagonal (n : ℕ) (p q : ℕ → ℝ) (i : Fin n) :
    (bidiagonal n p q*(bidiagonal n p q).transpose) i i=(p i)^2+(q i)^2 := by
  rw [mul_apply,bidiagonal_row_sum]
  have hi : i.castSucc≠i.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
  simp only [transpose_apply,bidiagonal,ite_true,ite_eq_right hi,ite_eq_right (Ne.symm hi),sub_zero,zero_sub]
  ring

/-- The smaller actual Darboux Gram upper adjacent entry is minus the product of the genuine overlapping original factors.
Use: coefficient_darboux_product identifies this with the shifted support coupling after the exact endpoint deletion.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the two original neighboring rows overlap at their unique common physical column. -/
theorem bidiagonal_rows_upper (n : ℕ) (p q : ℕ → ℝ) (i j : Fin n) (hij : (i:ℕ)+1=j) :
    (bidiagonal n p q*(bidiagonal n p q).transpose) i j= -q i*p j := by
  rw [mul_apply,bidiagonal_row_sum]
  have h1 : i.castSucc≠j.castSucc := by intro h; have := congrArg Fin.val h; dsimp at this; omega
  have h2 : i.castSucc≠j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
  have h3 : i.succ=j.castSucc := Fin.ext hij
  have h4 : i.succ≠j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
  simp only [transpose_apply,bidiagonal,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3,
    ite_eq_right h4,sub_self,mul_zero,sub_zero,zero_sub,neg_mul]

end
end jacobi.Support
