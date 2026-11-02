import jacobi.Jacobi.ChebyshevSecond
import jacobi.Jacobi.FibreLimit
import jacobi.Finite.PolynomialIdentification
import jacobi.Finite.AffineFibre

/-!
Article: jacobi, Proposition 6.1.
The original Jacobi nodes at (1/2,1/2) are precisely the roots of U_n.
Their positive affine image has exactly the printed monic polynomial,
and the actual complete scaled resolvent spectrum has the same l1
limit as the independently verified Laguerre family.
Use: uNodes_polynomial identifies exactly the source's p_n^U fibre, and uEdge_l1_limit proves its complete original edge limit.
-/
namespace jacobi.Counterexample
noncomputable section
open Polynomial Polynomial.Chebyshev Matrix Set Filter jacobi.Finite
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original U-family source nodes as the positive affine image of the genuine half-integer Jacobi nodes.
Use: uNodes_polynomial identifies exactly the source's p_n^U fibre, and uEdge_l1_limit proves its complete original edge limit.
Article: jacobi, Proposition 6.1.
-/
def uNodes (theta:ℝ) (ht:0 < theta) (htop:theta≤1) (n:ℕ) : Nodes n where
  value i:=theta*(jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).value i+(1-theta)
  strictAnti:=by
    intro i j hij
    have hh:=mul_lt_mul_of_pos_left
      ((jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).strictAnti hij) ht
    linarith
  interval i:=by
    have hh:=(jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).interval i
    have hl:=mul_lt_mul_of_pos_left hh.1 ht
    have hr:=mul_lt_mul_of_pos_left hh.2 ht
    constructor <;> nlinarith

/-- The literal original monic Chebyshev U counterexample polynomial.
Use: uNodes_polynomial transfers every full finite-fibre limit to the exact source polynomial.
Article: jacobi, Proposition 6.1.
-/
def uPolynomial (theta:ℝ) (n:ℕ) : Polynomial ℝ :=
  C ((theta/2)^n)*(U ℝ (n:ℤ)).comp (C theta⁻¹*(X-C (1-theta)))

/-- The original full Jacobi node polynomial at U is exactly the monic classical U_n.
Use: uNodes_polynomial identifies the source's affine U family without a special-function or polynomial hypothesis.
Article: jacobi, Proposition 6.1.
Proof: the genuine shifted Jacobi identity gives every original U
zero. The actual polynomial (1/2)^n*U_n is monic of degree n by the
community Chebyshev coefficient theorem. Complete node-product uniqueness applies. -/
theorem u_base_polynomial (n:ℕ) :
    (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).polynomial=
      C ((1/2:ℝ)^n)*U ℝ (n:ℤ) := by
  -- All original finite roots and the exact leading coefficient are checked before identifying the fibre.
  apply Eq.symm
  apply Nodes.eq_polynomial
  · rw [Polynomial.Monic,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_U_natCast,← mul_pow]
    norm_num
  · rw [natDegree_C_mul (by positivity),natDegree_U_natCast]
  · intro i
    let ha:(-1:ℝ)<1/2:=by norm_num
    have hz:(jacobi.Jacobi.shiftedPolynomial (1/2) (1/2) n).eval
        (jacobi.Jacobi.shiftedRoots (1/2) (1/2) ha ha n i)=0 :=
      (mem_roots (jacobi.Jacobi.shiftedPolynomial_ne_zero ha ha n)).mp
        (jacobi.Jacobi.shiftedRoots_properties ha ha i).1
    rw [jacobi.Jacobi.shiftedPolynomial_half_sine,eval_mul,eval_C,eval_comp,
      eval_sub,eval_one,eval_mul,eval_C,eval_X] at hz
    have hu:=(mul_eq_zero.mp hz).resolve_left (by positivity : 1/((n:ℝ)+1)≠0)
    rw [eval_mul,eval_C]
    change (1/2:ℝ)^n*(U ℝ (n:ℤ)).eval
      (1-2* jacobi.Jacobi.shiftedRoots (1/2) (1/2) ha ha n i)=0
    rw [hu,mul_zero]

/-- The original affine U node polynomial equals the exact literal source polynomial in every finite dimension.
Use: u_polynomial_energy_limit and uEdge_l1_limit concern precisely the source's p_n^U, including its entire original finite fibre.
Article: jacobi, Proposition 6.1.
Proof: the complete affine node-product identity gives theta^n.
The actual monic U normalization gives (1/2)^n. Multiplying them
yields exactly the printed (theta/2)^n and its original affine argument. -/
theorem uNodes_polynomial {theta:ℝ} (ht:0 < theta) (htop:theta≤1) (n:ℕ) :
    (uNodes theta ht htop n).polynomial=uPolynomial theta n := by
  -- The exact scalar factor is retained; equality of zero sets alone is not used as polynomial equality.
  apply Polynomial.funext
  intro x
  rw [Nodes.affine_eval
    (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n)
    (uNodes theta ht htop n) ht.ne' (fun _=>rfl) x,u_base_polynomial]
  simp only [uPolynomial,eval_mul,eval_C,eval_comp,eval_sub,eval_X]
  have hc:theta^n*(1/2:ℝ)^n=(theta/2)^n:=by rw [← mul_pow]; congr 1; ring
  rw [← mul_assoc,hc]
  congr 1
  congr 1
  ring

/-- The original U-family zero-padded scaled resolvent spectrum.
Use: uEdge_l1_limit verifies the whole actual finite spectrum, not just finitely many top nodes.
Article: jacobi, Proposition 6.1.
-/
def uEdge (theta:ℝ) (n k:ℕ) : ℝ :=
  if hk:k < n then 1/((n:ℝ)^2*(1-(theta*
    (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).value ⟨k,hk⟩+
      (1-theta)))) else 0

/-- The whole original U-family scaled reciprocal spectrum has exactly the inverse affine factor theta^(-1).
Use: uEdge_l1_limit reuses the complete original Jacobi-to-Bessel l1 theorem with no new tail assumption.
Article: jacobi, Proposition 6.1.
Proof: substitute the literal affine source node in each genuine
resolvent denominator. The two zero-padding conventions agree, and
every finite physical node lies strictly below one. -/
theorem uEdge_eq {theta:ℝ} (ht:0 < theta) (n k:ℕ) :
    uEdge theta n k=(1/theta)*
      jacobi.Jacobi.finiteLambdaAt (1/2) (1/2) (by norm_num) (by norm_num) n k := by
  -- The genuine dimension-squared normalization is kept unchanged.
  by_cases hk:k < n
  · rw [uEdge,dite_eq_left hk,jacobi.Jacobi.finiteLambdaAt_eq _ _ hk,
      jacobi.Jacobi.finiteLambda_node]
    have he:1-(theta*(jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).value ⟨k,hk⟩+
        (1-theta))=theta*(1-(jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) n).value ⟨k,hk⟩):=by ring
    rw [he]
    field_simp
  · rw [uEdge,dite_eq_right hk,jacobi.Jacobi.finiteLambdaAt_zero _ _ (not_lt.mp hk),mul_zero]

/-- The actual U counterexample family has the complete original l1 edge limit theta^(-1)*Lambda_U.
Use: uEdge_l1_printed and the independently verified Laguerre l1 limit give the identical-edge premise of the full source counterexample.
Article: jacobi, Proposition 6.1.
Proof: the exact finite inverse affine factor applies to every padded
mode. Factor its positive absolute value out of the genuine l1 sum
and use the already proved full original Jacobi spectral limit. -/
theorem uEdge_l1_limit {theta:ℝ} (ht:0 < theta) :
    Tendsto (fun n:ℕ=>∑'k,|uEdge theta (n+1) k-
      (1/theta)* jacobi.Bessel.edgeValue (1/2) (by norm_num) k|) atTop (𝓝 0) := by
  -- The existing full tail theorem is reused, rather than re-proving only fixed-index zero convergence.
  simp_rw [uEdge_eq ht,← mul_sub,abs_mul,abs_of_pos (by positivity : 0 < 1/theta),tsum_mul_left]
  simpa only [mul_zero,Function.comp_def] using
    ((jacobi.Jacobi.finiteLambdaAt_l1_tendsto (by norm_num : (-1:ℝ)<1/2)
      (by norm_num : (-1:ℝ)<1/2)).comp (tendsto_add_atTop_nat 1)).const_mul (1/theta)

end
end jacobi.Counterexample
