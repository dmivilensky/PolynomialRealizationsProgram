import jacobi.Jacobi.StandardPolynomial
import jacobi.Jacobi.StandardNorm
import jacobi.Finite.StandardGreen
import chebyshev2.Green.Bidiagonal

/-!
The exact standard Jacobi Green matrix, with the pencil identification proved.
Its lower bidiagonal factor has diagonal sqrt(v_i) and subdiagonal -sqrt(w_i).
The genuine norm balance converts that factor to a weighted difference
operator, so the existing tail inverse formula applies to the actual chain.
Use: StandardJacobi estimates these true inverse-conductance tails; the
standard matrix is not specified by an assumed Green-kernel identity.
Article: jacobi, Theorem 5.4, Equation (5.9).
Article role: identification of the actual standard endpoint pencil with its conductance
factorization.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Matrix chebyshev1 chebyshev2 jacobi.Finite
set_option backward.isDefEq.respectTransparency false

/-- Positive endpoint value of the genuine probability-orthonormal Jacobi family.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
def standardEndpoint (a b : ℝ) (i : ℕ) : ℝ := sqrt (standardEndpointSquare a b i)

/-- The conductance is u_i^2 times the endpoint-normalized forward
coefficient; norm balance also identifies it with a_(i+1)*u_i*u_(i+1).
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
def standardConductance (a b : ℝ) (i : ℕ) : ℝ :=
  standardEndpointSquare a b i*standardForward a b i

/-- All endpoint values are genuinely positive.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardEndpoint_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (i : ℕ) :
    0<standardEndpoint a b i := sqrt_pos.mpr (standardEndpointSquare_pos ha hb i)

/-- All finite conductances are genuinely positive, including the final
one representing the next orthogonal-polynomial recurrence step.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardConductance_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (i : ℕ) :
    0<standardConductance a b i :=
  mul_pos (standardEndpointSquare_pos ha hb i) (standardForward_pos ha hb i)

/-- The true endpoint values have the true norm squares.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardEndpoint_sq {a b : ℝ} (ha : -1<a) (hb : -1<b) (i : ℕ) :
    standardEndpoint a b i^2=standardEndpointSquare a b i :=
  sq_sqrt (standardEndpointSquare_pos ha hb i).le

/-- The conductance square root gives the diagonal factor exactly.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardConductance_sqrt {a b : ℝ} (ha : -1<a) (hb : -1<b) (i : ℕ) :
    sqrt (standardConductance a b i)=standardEndpoint a b i*sqrt (standardForward a b i) :=
  sqrt_mul (standardEndpointSquare_pos ha hb i).le _

/-- At each incoming edge the same conductance gives the lower factor.
This is precisely the genuine adjacent-norm identity in square-root form.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardConductance_sqrt_next {a b : ℝ} (ha : -1<a) (hb : -1<b) (i : ℕ) :
    sqrt (standardConductance a b i)=standardEndpoint a b (i+1)*sqrt (standardBackward a b (i+1)) := by
  change sqrt (standardEndpointSquare a b i*standardForward a b i)=_
  rw [← standardEndpointSquare_balance ha hb i]
  exact sqrt_mul (standardEndpointSquare_pos ha hb (i+1)).le _

/-- Concrete lower bidiagonal factor of the standard endpoint pencil.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
def standardLower (a b : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Bidiagonal.matrix (fun i => sqrt (standardForward a b i))
    (fun i => -sqrt (standardBackward a b i))

/-- The actual symmetric standard pencil is the genuine bidiagonal
Gram matrix. The initial missing lower entry contributes zero.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standard_pencil_lower {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    1-(standardChain a b ha hb N).matrix=standardLower a b N*(standardLower a b N)ᵀ := by
  ext i j
  rw [Matrix.sub_apply,Jacobi.matrix,JacobiData.matrix_apply]
  simp only [Nat.zero_add,standardLower,Bidiagonal.mul_transpose_apply]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,ite_eq_left rfl,Matrix.one_apply_eq,
      standardChain_diagonal ha hb i.isLt,sq_sqrt (standardForward_pos ha hb i).le,neg_sq]
    by_cases hi : 0 < i.val
    · rw [ite_eq_left hi,sq_sqrt (standardBackward_pos ha hb hi).le]
      ring
    · have hi0 : i.val=0 := by omega
      simp [hi0,standardBackward]
  · rw [ite_eq_right hij,ite_eq_right hij,Matrix.one_apply_ne hij]
    by_cases hu : i.val+1=j.val
    · have hj : 0 < j.val := by omega
      rw [ite_eq_left hu,ite_eq_left hu,standardChain_coupling ha hb hj j.isLt,
        show j.val-1=i.val by omega,sqrt_mul (standardForward_pos ha hb i).le]
      ring
    · rw [ite_eq_right hu,ite_eq_right hu]
      by_cases hl : j.val+1=i.val
      · have hi : 0 < i.val := by omega
        rw [ite_eq_left hl,ite_eq_left hl,standardChain_coupling ha hb hi i.isLt,
          show i.val-1=j.val by omega,sqrt_mul (standardForward_pos ha hb j).le]
        ring
      · simp [hl]

/-- The true bidiagonal factor is the endpoint-conjugated difference
factor. Its subdiagonal equality is the already proved norm balance.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standard_lower_difference {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    standardLower a b N=diagonal (fun i:Fin N => (standardEndpoint a b i)⁻¹)*
      (StandardGreen.differenceMatrix N)ᵀ*
        diagonal (fun i:Fin N => sqrt (standardConductance a b i)) := by
  ext i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [standardLower,Bidiagonal.matrix,Matrix.transpose_apply,
    StandardGreen.differenceMatrix,Matrix.sub_apply,Matrix.one_apply,StandardGreen.shiftMatrix]
  by_cases hij : i=j
  · subst j
    have hi : ¬i.val+1=i.val := by omega
    simp only [ite_true,hi,ite_false,sub_zero,add_zero]
    rw [standardConductance_sqrt ha hb i]
    field_simp [(standardEndpoint_pos ha hb i).ne']
  · have hji : j≠i := Ne.symm hij
    simp only [hij,hji,ite_false,zero_sub,zero_add]
    by_cases hl : j.val+1=i.val
    · simp only [hl,ite_true]
      rw [standardConductance_sqrt_next ha hb j,show j.val+1=i.val from hl]
      field_simp [(standardEndpoint_pos ha hb i).ne']
    · simp [hl]

/-- The full weighted-difference pencil equals I-J for the constructed
standard matrix. Thus the Green tail formula has no identification premise.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standard_pencil {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    1-(standardChain a b ha hb N).matrix=
      StandardGreen.pencil (fun i:Fin N => standardEndpoint a b i)
        (fun i:Fin N => standardConductance a b i) := by
  rw [standard_pencil_lower ha hb,standard_lower_difference ha hb]
  simp only [Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.transpose_transpose]
  have hc : diagonal (fun i:Fin N => sqrt (standardConductance a b i))*
      diagonal (fun i:Fin N => sqrt (standardConductance a b i))=
        diagonal (fun i:Fin N => standardConductance a b i) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_self_sqrt (standardConductance_pos ha hb i).le
  calc
    _ = diagonal (fun i:Fin N => (standardEndpoint a b i)⁻¹)*
        (StandardGreen.differenceMatrix N)ᵀ*
          (diagonal (fun i:Fin N => sqrt (standardConductance a b i))*
            diagonal (fun i:Fin N => sqrt (standardConductance a b i)))*
              StandardGreen.differenceMatrix N*diagonal (fun i:Fin N => (standardEndpoint a b i)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc]; rfl

/-- Exact Green tail formula for the actual standard Jacobi matrix.
All polynomial, normalization and inverse obligations are discharged.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standard_green_entry {a b : ℝ} (ha : -1<a) (hb : -1<b) {N : ℕ}
    (i j : Fin N) (hij : i≤j) :
    (standardChain a b ha hb N).green i j=
      standardEndpoint a b i*standardEndpoint a b j*
        ∑ l:Fin N,if j≤l then (standardConductance a b l)⁻¹ else 0 :=
  StandardGreen.green_entry _ _ _ (fun k => (standardEndpoint_pos ha hb k).ne')
    (fun k => (standardConductance_pos ha hb k).ne') (standard_pencil ha hb N) i j hij

end
end jacobi.Jacobi
