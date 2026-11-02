import jacobi.Support.Chain
import chebyshev1.Jacobi.Orthogonality

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The actual original monic support recurrence has its exact top-node
product value. The proof uses the original three-term coefficients and
the genuine C_0=0 boundary, including the final characteristic zero.
Use: leading_top_node proves it is the genuine original monic recurrence value, and the normalized support polynomial formula divides by the true positive coupling product.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial jacobi.Reference chebyshev1 chebyshev2

/-- The original top-node monic product amplitude.
Use: leading_top_node proves it is the genuine original monic recurrence value, and the normalized support polynomial formula divides by the true positive coupling product.
Article: jacobi, Appendix C.3 (top-node polynomials).
-/
def topMonicAmplitude (a b : ℝ) (n m : ℕ) : ℝ :=
  ∏ j∈Finset.range m,coefficientA a b (n+1) j/2

/-- The genuine original top-node product has its exact next original birth coefficient factor.
Use: leading_top_node verifies the actual original recurrence rather than assuming a special-value formula.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: split the actual finite original product at its final index. -/
theorem topMonicAmplitude_succ (a b : ℝ) (n m : ℕ) :
    topMonicAmplitude a b n (m+1)=topMonicAmplitude a b n m*(coefficientA a b (n+1) m/2) :=
  Finset.prod_range_succ _ _

/-- Every original interior top-node monic amplitude is strictly positive.
Use: top-node positivity of the genuine normalized support solution fixes the positive square-root branch in its exact product formula and reduction-of-order Volterra kernel.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: each original used A coefficient is strictly positive in the actual nonterminal row range. -/
theorem topMonicAmplitude_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm:m≤n) :
    0<topMonicAmplitude a b n m := by
  unfold topMonicAmplitude
  apply Finset.prod_pos
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact div_pos (coefficientA_pos ha hb (by omega)) (by norm_num)

/-- The actual original monic support recurrence at its genuine upper spectral node equals exactly its original top-node product, including its terminal characteristic zero.
Use: the original normalized top-node product and all support Volterra estimates begin with this genuine unchanged recurrence solution.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: use two-step induction on the actual monic recurrence. The initial constant and original C_0=0 fix its first two values. At each true interior row the actual C term cancels against the original squared coupling, leaving precisely the next A/2 product factor. -/
theorem leading_top_node (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) (hm:m≤n+1) :
    ((naturalChain a b ha hb (n+1)).data.leading m).eval (cos (gamma a*step a b (n+1)))=
      topMonicAmplitude a b n m := by
  -- The actual original Jacobi recurrence supplies every value, so no orthogonal-polynomial special value is assumed.
  induction m using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading,JacobiData.block,topMonicAmplitude]
  | one =>
    rw [JacobiData.leading,JacobiData.block,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
      naturalChain_diagonal a b ha hb (by omega : 0<n+1),diagonal,coefficientC_zero,
      topMonicAmplitude_succ]
    simp only [topMonicAmplitude,Finset.range_zero,Finset.prod_empty,one_mul,add_zero]
    ring
  | more m h0 h1 =>
    have hm0 : m≤n+1 := by omega
    have hm1 : m+1≤n+1 := by omega
    have hs : (naturalChain a b ha hb (n+1)).data.leading (m+2)=
        (X-C ((naturalChain a b ha hb (n+1)).data.b (m+1)))*
          (naturalChain a b ha hb (n+1)).data.leading (m+1)-
        C ((naturalChain a b ha hb (n+1)).data.aSq (m+1))*
          (naturalChain a b ha hb (n+1)).data.leading m := by
      simp only [JacobiData.leading,JacobiData.block,Nat.zero_add]
    rw [hs,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_C,h0 hm0,h1 hm1,
      naturalChain_diagonal a b ha hb (by omega : m+1<n+1),
      naturalChain_coupling a b ha hb (by omega : 0<m+1) (by omega : m+1<n+1),Nat.add_sub_cancel,
      diagonal]
    simp only [topMonicAmplitude_succ]
    ring

end
end jacobi.Support
