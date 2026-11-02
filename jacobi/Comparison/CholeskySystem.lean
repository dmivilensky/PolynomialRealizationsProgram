import jacobi.Comparison.Schur

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The actual original row coefficients solve the true preceding-coordinate
Gram system. The exact scaled residual equation used by the continuum
Cholesky comparison therefore concerns the genuine target polynomials.
Use: coercive-system bounds and the continuum GL residual comparison apply to the same original coefficients as targetPolynomial_schur.
-/
namespace jacobi.Comparison
noncomputable section
open jacobi.Finite jacobi.Support Matrix
open scoped InnerProductSpace

/-- The genuine original Cholesky row solves its exact actual principal
Gram linear system, in the printed row orientation.
Use: coercive-system bounds and the continuum GL residual comparison
apply to the same original coefficients as targetPolynomial_schur.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the original weighted support evaluations are independent. The
proved Gram projection system therefore holds; negate its coefficients
and use the true real Gram symmetry to obtain the printed row system. -/
theorem rowCoefficient_system (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (j:Fin i.val) :
    (∑ k:Fin i.val, rowCoefficient a b ha hb n i k*
      targetGram a b ha hb n (Gram.before i k) (Gram.before i j)) =
      -targetGram a b ha hb n i (Gram.before i j) := by
  -- Use independence of the actual target-weighted support evaluations to solve their Gram system.
  have hinj : Function.Injective (Gram.before i) := by
    intro k l hkl
    exact Fin.ext (congrArg (fun r:Fin (n+1) => r.val) hkl)
  have hf := (target_support_independent a b ha hb n).comp (Gram.before i) hinj
  have hh := congrFun (Gram.coefficients_system hf
    ((targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n i))) j
  rw [targetGram_eq]
  simp only [Matrix.mulVec,dotProduct,Matrix.gram_apply,Function.comp_def] at hh
  simp only [rowCoefficient,Matrix.gram_apply,neg_mul,Finset.sum_neg_distrib]
  congr 1
  rw [real_inner_comm]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm]
  ring

/-- The exact original coefficient row satisfies the printed identity
plus perturbation system, with its actual preceding-coordinate indices.
Use: quantitative coefficient estimates and the limiting GL residual
equation isolate each actual coefficient through this equality.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: insert the true identity-plus-perturbation decomposition into the
proved genuine Gram system. Its principal identity contribution is
exactly c_ij, while the original cross-row identity contribution is zero. -/
theorem rowCoefficient_perturbation_system (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (j:Fin i.val) :
    rowCoefficient a b ha hb n i j+gramPerturbation a b ha hb n i (Gram.before i j)+
      (∑ k:Fin i.val, rowCoefficient a b ha hb n i k*
        gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j))=0 := by
  -- The principal identity term is c_ij; the cross-row identity term is genuinely zero.
  classical
  have hsys := rowCoefficient_system a b ha hb n i j
  have hcross : i≠Gram.before i j := by
    intro h
    have hv := congrArg (fun k:Fin (n+1) => k.val) h
    have hj := j.isLt
    dsimp [Gram.before] at hv
    omega
  have hblock (k:Fin i.val) :
      gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j)=
      targetGram a b ha hb n (Gram.before i k) (Gram.before i j)-(if k=j then 1 else 0) := by
    have he : (Gram.before i k=Gram.before i j)↔k=j :=
      ⟨fun h => Fin.ext (congrArg (fun r:Fin (n+1) => r.val) h),fun h => congrArg _ h⟩
    simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply,he]
  have hc : gramPerturbation a b ha hb n i (Gram.before i j)=
      targetGram a b ha hb n i (Gram.before i j) := by
    simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply,hcross,ite_false,sub_zero]
  rw [hc]
  simp_rw [hblock,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hsys]
  ring

end
end jacobi.Comparison
