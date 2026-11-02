import jacobi.Applications.TerminalRealization

/-!
Article: jacobi, Proposition A.1.
Use: linearIterates_eq_aeval gives the existing TwoTerm polynomial semantics on general vector spaces, so the source's fixed operator need not be a finite matrix.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial jacobi.Finite jacobi.Jacobi chebyshev1 chebyshev2
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The literal two-step iteration on any real linear operator.
Use: linearIterates_eq_aeval gives the existing TwoTerm polynomial semantics on general vector spaces, so the source's fixed operator need not be a finite matrix.
Article: jacobi, Proposition A.1.
-/
def linearIterates (S : TwoTerm) (H : E →ₗ[ℝ] E) (v : E) : ℕ → E
  | 0 => v
  | 1 => v-S.gamma 0 • H v
  | n+2 => S.a (n+1) • linearIterates S H v (n+1)+
      S.b (n+1) • linearIterates S H v n-S.gamma (n+1) • H (linearIterates S H v (n+1))

/-- The actual two-step iterates on every real linear operator are evaluation of the earlier verified residual polynomial at that same operator.
Use: nesterov_linear_terminal_realization proves the application on arbitrary Hilbert spaces as well as finite dimensions.
Article: jacobi, Proposition A.1.
Proof: the previously proved TwoTerm residual recurrence and its two initial values are identities of actual polynomials. Evaluate them in the algebra of linear endomorphisms and apply them to the original vector; linearity gives the literal iteration recurrence. -/
theorem linearIterates_eq_aeval (S : TwoTerm) (H : E →ₗ[ℝ] E) (v : E) (n : ℕ) :
    linearIterates S H v n=(aeval H (S.realization.residualPolynomial n)) v := by
  -- The polynomial identities are reused before evaluation in the general endomorphism algebra.
  induction n using Nat.twoStepInduction with
  | zero => simp [linearIterates,TwoTerm.residual_zero]
  | one => simp [linearIterates,TwoTerm.residual_one,Algebra.algebraMap_eq_smul_one]
  | more n h0 h1 =>
    rw [linearIterates,h0,h1,TwoTerm.residual_recurrence]
    simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,LinearMap.add_apply,
      LinearMap.sub_apply,Module.End.mul_apply,Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply,Module.End.one_apply]
    abel

/-- Actual Landweber iterations on every real linear operator equal the corresponding power of I-H.
Use: the appended source stage acts on the same arbitrary operator as the Jacobi realization, including the zero-degree factor case.
Article: jacobi, Proposition A.1.
Proof: induct on the actual count and compose the same linear endomorphism at each update. -/
theorem landweber_linear_iterate (H : E →ₗ[ℝ] E) (v : E) (n : ℕ) :
    (fun w : E => w-H w)^[n] v=((1-H)^n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,pow_succ',Module.End.mul_apply]
    rfl

/-- Every original Jacobi-factor fibre realization followed by the exact Landweber stage has the source Nesterov residual on every real linear operator, without a dimension restriction.
Use: completes the full fixed-operator assertion of Proposition A.1, including bounded A*A on infinite-dimensional Hilbert spaces and the m=0 case.
Article: jacobi, Proposition A.1.
Proof: apply the genuine TwoTerm polynomial semantics on the endomorphism algebra, substitute the already proved arbitrary-fibre terminal polynomial, and compose the actual Landweber iterations. Polynomial evaluation preserves the exact integer factorization. -/
theorem nesterov_linear_terminal_realization {b : ℝ} (hb : -1<b) (e m : ℕ)
    {J : Jacobi m} (hJ : InFiber J
      (nodes (b/2) ((e:ℝ)-1/2) (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 m).polynomial)
    (H : E →ₗ[ℝ] E) (v : E) :
    (fun w : E => w-H w)^[m+1+e]
      (linearIterates (endpointMethod J) H v m)=(aeval H (nesterovResidual b m e)) v := by
  -- The same operator is used in both actual stages; the argument is purely algebraic.
  rw [landweber_linear_iterate,linearIterates_eq_aeval,
    endpoint_prefix_exact _ hJ m le_rfl,endpoint_terminal_exact _ _ hJ]
  rw [nesterovResidual,nesterovFactor,map_mul,map_pow,map_sub,map_one,aeval_X,
    Module.End.mul_apply]

end
end jacobi.Applications
