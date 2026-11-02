import jacobi.Jacobi.GeneralRecurrence
import jacobi.Reference.GeneralJacobiNorm

/-!
The standard recurrence is symmetric after the genuine Jacobi norm scaling.
The same weighted integral is evaluated in the two adjacent recurrences;
orthogonality supplies the norm ratio without assuming a coefficient formula.
Use: StandardJacobi identifies its positive endpoint solution with actual
orthonormal Jacobi values and then uses the proved Gamma norm asymptotics.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the genuine Jacobi norm and its leading power normalization.
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Real jacobi.Reference
set_option backward.isDefEq.respectTransparency false

/-- Integration against an actual Jacobi polynomial is linear under
constant polynomial multiplication. This keeps the recurrence proof algebraic.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem weightedIntegralMap_const_mul {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n : ℕ) (c : ℝ) (p : ℝ[X]) :
    weightedIntegralMap a b ha hb n (C c*p)=c*weightedIntegralMap a b ha hb n p := by
  rw [← smul_eq_C_mul,LinearMap.map_smul,smul_eq_mul]

/-- The actual Jacobi weighted pairing is diagonal, with the genuine
squared norm on its diagonal. It is valid for every pair of degrees.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem weightedIntegralMap_pair {a b : ℝ} (ha : -1<a) (hb : -1<b) (i j : ℕ) :
    weightedIntegralMap a b ha hb i (shiftedPolynomial a b j)=
      if i=j then jacobiNorm a b i else 0 := by
  split_ifs with h
  · subst j
    simp only [weightedIntegralMap,LinearMap.coe_mk,AddHom.coe_mk,jacobiNorm,pow_two]
  · exact shiftedPolynomial_orthogonal ha hb h

/-- Adjacent genuine norms symmetrize the actual endpoint recurrence.
Both sides are the same weighted integral of x*p_n*p_(n+1).
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem standard_norm_balance {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    standardForward a b n*jacobiNorm a b (n+1)=
      standardBackward a b (n+1)*jacobiNorm a b n := by
  let L := weightedIntegralMap a b ha hb n
  let M := weightedIntegralMap a b ha hb (n+1)
  have hr := congrArg M (standard_polynomial_recurrence ha hb n)
  have hs := congrArg L (standard_polynomial_recurrence ha hb (n+1))
  simp only [sub_mul,map_sub,weightedIntegralMap_const_mul,weightedIntegralMap_pair,
    Nat.add_sub_cancel,ite_eq_right (by omega : n+1≠n),
    ite_eq_right (by omega : n+1≠n-1),ite_eq_right (by omega : n≠n+2),
    ite_eq_right (by omega : n≠n+1),ite_true,mul_zero,sub_zero,L,M] at hr hs
  have hcomm : M ((1-2*X)*shiftedPolynomial a b n)=
      L ((1-2*X)*shiftedPolynomial a b (n+1)) := by
    change (∫ t in (0:ℝ)..1,weight a b t*
      ((shiftedPolynomial a b (n+1)).eval t*((1-2*X)*shiftedPolynomial a b n).eval t))=_
    apply intervalIntegral.integral_congr
    intro t _
    simp only [eval_mul,eval_sub,eval_one,eval_ofNat,eval_X]
    ring
  simp only [sub_mul,map_sub,L,M] at hcomm
  linear_combination hr-hs+hcomm

/-- Squared endpoint value of the standard orthonormal family for the
probability Jacobi weight. Its zeroth value is one. A common weight
normalization cancels from every Green entry.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
def standardEndpointSquare (a b : ℝ) (n : ℕ) : ℝ :=
  jacobiNorm a b 0/jacobiNorm a b n

/-- Every genuine squared endpoint value is strictly positive.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem standardEndpointSquare_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    0<standardEndpointSquare a b n :=
  div_pos (jacobiNorm_pos ha hb 0) (jacobiNorm_pos ha hb n)

/-- The initial endpoint value uses exactly probability normalization.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem standardEndpointSquare_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    standardEndpointSquare a b 0=1 := div_self (jacobiNorm_pos ha hb 0).ne'

/-- The actual orthonormal endpoint squares satisfy the recurrence
ratio required by the symmetric standard off-diagonals.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem standardEndpointSquare_balance {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    standardEndpointSquare a b (n+1)*standardBackward a b (n+1)=
      standardEndpointSquare a b n*standardForward a b n := by
  have h := standard_norm_balance ha hb n
  unfold standardEndpointSquare
  field_simp [(jacobiNorm_pos ha hb n).ne',(jacobiNorm_pos ha hb (n+1)).ne']
  linear_combination -jacobiNorm a b 0*h

end
end jacobi.Jacobi
