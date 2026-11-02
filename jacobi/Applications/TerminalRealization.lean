import jacobi.Applications.EndpointRealization
import jacobi.Applications.NesterovFull
import jacobi.Jacobi.FiniteProduct

/-!
Article: jacobi, Theorem 5.1.
Use: nesterov_terminal_realization allows every original factor realization, without special spectral weights or an extra terminal-identity premise.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Matrix jacobi.Finite jacobi.Jacobi chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- Every matrix in the original Jacobi polynomial fibre has exactly the genuine normalized source terminal residual.
Use: nesterov_terminal_realization allows every original factor realization, without special spectral weights or an extra terminal-identity premise.
Article: jacobi, Proposition A.1.
Proof: the characteristic polynomial is the full original node product. Divide its affine evaluation by its nonzero value at one; factorwise cancellation gives exactly the already proved normalized Jacobi root product. -/
theorem endpoint_terminal_exact {a b : ℝ} (ha : -1<a) (hb : -1<b) {m : ℕ}
    {J : Jacobi m} (hJ : InFiber J (nodes a b ha hb m).polynomial) :
    endpointResidual J m=shiftedPolynomial a b m := by
  -- The argument uses all original finite roots and their exact endpoint normalization.
  have hp : J.data.leading m=(nodes a b ha hb m).polynomial := by
    rw [JacobiData.leading,J.data.block_eq_charpoly J.coupling_nonneg]
    exact hJ.2
  apply Polynomial.funext
  intro t
  rw [endpointResidual_eval,hp,shiftedPolynomial_product ha hb m]
  simp only [Nodes.polynomial,eval_prod,eval_sub,eval_X,eval_C,nodes]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi := (shiftedRoots_properties ha hb i).2.1.ne'
  field_simp
  ring

/-- Every actual endpoint-normalized Jacobi prefix has its genuine operator-polynomial action on a fixed operator.
Use: nesterov_terminal_realization transfers the original arbitrary Jacobi realization to the same operator before the Landweber stage.
Article: jacobi, Proposition A.1.
Proof: reuse the earlier general realization polynomial semantics and substitute the proved actual prefix polynomial identity. -/
theorem endpoint_operator_exact {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) (n : ℕ) (hn : n≤N)
    {d : Type*} [Fintype d] [DecidableEq d] (H : Matrix d d ℝ) :
    (endpointMethod J).realization.operatorTransfer n (fun _ => H)=aeval H (endpointResidual J n) := by
  rw [Realization.operatorTransfer_eq_aeval,endpoint_prefix_exact S hJ n hn]

/-- Literal repeated Landweber updates equal the exact power of the fixed residual operator.
Use: nesterov_terminal_realization treats the appended stage as actual iterations, including d=0, rather than only as a formal polynomial multiplier.
Article: jacobi, Proposition A.1.
Proof: induction on the actual iterate count uses the same fixed operator and the community matrix-vector product composition identity. -/
theorem landweber_iterate {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (v : d → ℝ) (n : ℕ) :
    (fun w : d → ℝ => w-H.mulVec w)^[n] v=((1-H)^n).mulVec v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,pow_succ',← Matrix.mulVec_mulVec]
    simp only [Matrix.sub_mulVec,Matrix.one_mulVec]

/-- Any realization in the original Jacobi-factor fibre followed by the source number of literal Landweber steps has exactly the original Nesterov terminal residual on every fixed operator.
Use: completes the realization assertion of Proposition A.1, and allows the already proved fibre energy bounds to concern its actual Jacobi stage.
Article: jacobi, Proposition A.1.
Proof: the earlier TwoTerm error theorem identifies the actual Jacobi iterates with their genuine normalized terminal polynomial. Repeated Landweber updates are the exact power of I-H, which is evaluation of the source's integer polynomial factor. Multiply these same operator evaluations. -/
theorem nesterov_terminal_realization {b : ℝ} (hb : -1<b) (e m : ℕ)
    {J : Jacobi m} (hJ : InFiber J
      (nodes (b/2) ((e:ℝ)-1/2) (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 m).polynomial)
    {d : Type*} [Fintype d] [DecidableEq d] (H : Matrix d d ℝ) (v : d → ℝ) :
    (fun w : d → ℝ => w-H.mulVec w)^[m+1+e]
      ((endpointMethod J).quadraticError H v m)=
        (aeval H (nesterovResidual b m e)).mulVec v := by
  -- Both stages are the already defined actual iterations, not only a symbolic product of their desired residuals.
  rw [landweber_iterate,TwoTerm.quadraticError_eq_transfer,
    endpoint_operator_exact _ hJ m le_rfl,endpoint_terminal_exact _ _ hJ]
  rw [nesterovResidual,nesterovFactor,map_mul,map_pow,map_sub,map_one,aeval_X,
    Matrix.mulVec_mulVec]

end
end jacobi.Applications
