import jacobi.Analytic.ShiftedMatrixIdentity
import jacobi.Comparison.ParameterReflection

/-!
Article: jacobi, Theorem C.5.
The actual original complex matrix resolvent reflects exactly under
parameter exchange. Its physical diagonal acquires precisely the printed
minus sign. This identity is exact at every complex point, and hence
transfers all proved compact right-edge bounds and limits to the left.
Use: targetResolvent_reflection computes the actual reflected inverse without adding a finite invertibility hypothesis to the identity itself.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Matrix jacobi.Finite jacobi.Comparison

/-- Negating an arbitrary complex finite matrix negates its genuine
nonsingular inverse, also under the community zero convention at singularity.
Use: targetResolvent_reflection computes the actual reflected inverse
without adding a finite invertibility hypothesis to the identity itself.
Article: jacobi, Theorem C.5.
Source: mathlib's exact matrix product-inverse law.
Proof: factor the actual negation as multiplication by minus the identity;
its genuine inverse is itself, and product inversion reverses factors. -/
theorem complex_matrix_inv_neg {N:ℕ} (A:Matrix (Fin N) (Fin N) ℂ) :
    (-A)⁻¹= -A⁻¹ := by
  have he : -A=((-1:ℂ) • (1:Matrix (Fin N) (Fin N) ℂ))*A := by simp
  have hi : (((-1:ℂ) • (1:Matrix (Fin N) (Fin N) ℂ)))⁻¹=
      (-1:ℂ) • (1:Matrix (Fin N) (Fin N) ℂ) := by
    apply Matrix.inv_eq_left_inv
    simp
  rw [he,Matrix.mul_inv_rev,hi]
  simp

/-- The actual target complex matrix resolvent has precisely the
source's alternating-conjugation parameter-reflection formula.
Use: targetResolvent_diagonal_reflection transfers all of Theorem C.5
to the actual left spectral edge with the original minus sign.
Article: jacobi, Theorem C.5.
Proof: complexify the already proved exact original target matrix swap.
The actual alternating diagonal has square and inverse equal to one.
The original reflected pencil is its negative conjugate; exact matrix
product inversion and negation give the same conjugate inverse. -/
theorem targetResolvent_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (z:ℂ) :
    ((-z) • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
      (targetChain a b ha hb n).matrix.map Complex.ofRealHom)⁻¹=
      -(Matrix.diagonal (fun i:Fin (n+1) => (-1:ℂ)^i.val)*
        (z • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
          (targetChain b a hb ha n).matrix.map Complex.ofRealHom)⁻¹*
        Matrix.diagonal (fun i:Fin (n+1) => (-1:ℂ)^i.val)) := by
  -- Every sign is the original physical sign, not an arbitrary eigenvector phase.
  let D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := Matrix.diagonal (fun i => (-1:ℂ)^i.val)
  have hD : D*D=1 := by
    rw [show D*D=Matrix.diagonal (fun i:Fin (n+1) => (-1:ℂ)^i.val*(-1:ℂ)^i.val) from
      Matrix.diagonal_mul_diagonal _ _]
    have hs (i:Fin (n+1)) : (-1:ℂ)^i.val*(-1:ℂ)^i.val=1 := by
      rw [← pow_two,← pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    simp only [hs,Matrix.diagonal_one]
  have hDi : D⁻¹=D := Matrix.inv_eq_left_inv hD
  have hJ : (targetChain a b ha hb n).matrix.map Complex.ofRealHom=
      -(D*(targetChain b a hb ha n).matrix.map Complex.ofRealHom*D) := by
    ext i j
    simp only [D,Matrix.map_apply,Matrix.neg_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
    change ((targetChain a b ha hb n).matrix i j:ℂ)=
      -((-1:ℂ)^i.val*((targetChain b a hb ha n).matrix i j:ℂ)*(-1:ℂ)^j.val)
    have hh := congrArg Complex.ofReal (congrArg (fun M:Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M i j)
      (targetChain_swap_matrix a b ha hb n))
    simpa only [alternatingMatrix,Matrix.neg_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one] using hh
  have hp : (-z) • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
      (targetChain a b ha hb n).matrix.map Complex.ofRealHom=
      -(D*(z • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
        (targetChain b a hb ha n).matrix.map Complex.ofRealHom)*D) := by
    rw [hJ,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hD]
    module
  rw [hp,complex_matrix_inv_neg,Matrix.mul_inv_rev,Matrix.mul_inv_rev,hDi]
  simp only [D,Matrix.mul_assoc]

/-- The actual reflected target resolvent diagonal is the negative
of the same original right-edge diagonal with exchanged parameters.
Use: this is the exact left-edge identity printed in Theorem C.5; all
proved right-edge bounds, profiles and energies apply after this rewrite.
Article: jacobi, Theorem C.5.
Proof: take the physical diagonal in the genuine matrix reflection;
the two original alternating signs multiply to one. -/
theorem targetResolvent_diagonal_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (z:ℂ) (i:Fin (n+1)) :
    (((-z) • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
      (targetChain a b ha hb n).matrix.map Complex.ofRealHom)⁻¹) i i=
      -(((z • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
        (targetChain b a hb ha n).matrix.map Complex.ofRealHom)⁻¹) i i) := by
  -- The physical diagonal contains the square of one unchanged alternating sign.
  rw [targetResolvent_reflection]
  simp only [Matrix.neg_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hs : (-1:ℂ)^i.val*(-1:ℂ)^i.val=1 := by
    rw [← pow_two,← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  congr 1
  calc
    _=((-1:ℂ)^i.val*(-1:ℂ)^i.val)*_ := by ring
    _=_ := by rw [hs,one_mul]

end
end jacobi.EdgeResolvent
