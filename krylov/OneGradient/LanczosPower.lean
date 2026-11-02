import krylov.OneGradient.LanczosFibre
import jacobi.Finite.NormalizedPolynomials
import Mathlib.Algebra.Polynomial.EraseLead
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(a).
Use: identify the exact missing-moment coefficient with the product of actual
positive Jacobi couplings from the genuine gradient spectral reconstruction.
Source: jacobi's proved normalized-leading/orthogonal-polynomial identity
and the true physical Lanczos polynomial action.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial krylov.Reference jacobi.Finite
variable {n : ℕ}

/-- The last actual physical power has the original Jacobi coupling-product
pairing with the genuine last Lanczos normal.
Use: the affine missing-moment coefficient is the printed product of squared
couplings, not a merely positive unspecified scalar.
Article: main_krylov, s5:moment(a).
Proof: remove the leading monomial from the actual last orthogonal polynomial.
Its lower-degree remainder lies in the known hyperplane. Its genuine leading
coefficient is the reciprocal actual Jacobi coupling product by the reused
normalized-leading reconstruction theorem. -/
theorem last_lanczos_power_pairing
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    inner ℝ (lastLanczosVector A hA g hg hc) (((cgOperator A)^n) g)=
      ‖g‖*(gradientSpectralData A hA g hg).reconstructed.data.linkProduct n := by
  let M := gradientSpectralData A hA g hg
  let j : Fin (activeSpectralValues A hA.1 g).card := ⟨n,by rw [hc];omega⟩
  let p := M.orthogonalPolynomial j
  let z := lastLanczosVector A hA g hg hc
  let L := M.reconstructed.data.linkProduct n
  have hdegree := M.orthogonalPolynomial_degree j
  have hp : p≠0 := leadingCoeff_ne_zero.mp hdegree.2.ne'
  have hdeg : p.degree=n := by rw [degree_eq_natDegree hp,hdegree.1]
  have hrem : CG.polynomialAction (cgOperator A) g p.eraseLead∈CG.krylovSpace (cgOperator A) g n := by
    exact ⟨p.eraseLead,Polynomial.mem_degreeLT.mpr ((degree_eraseLead_lt hp).trans_eq hdeg),rfl⟩
  have hzero := (krylov_last_lanczos_hyperplane A hA g hg hc _).mp hrem
  have hL : 0<L := linkProduct_pos M.reconstructed_irreducible j.isLt
  have hlead : p.leadingCoeff=L⁻¹ := by
    rw [show p=M.orthogonalPolynomial j from rfl,← normalizedLeading_eq_orthogonalPolynomial]
    rw [normalizedLeading,leadingCoeff_mul,leadingCoeff_C]
    have hm : (M.reconstructed.data.leading n).Monic :=
      M.reconstructed.data.block_monic M.reconstructed.coupling_nonneg 0 n
    change (M.reconstructed.data.linkProduct n)⁻¹*(M.reconstructed.data.leading n).leadingCoeff=_
    rw [hm.leadingCoeff,mul_one]
  have hnorm : CG.polynomialAction (cgOperator A) g p=‖g‖ • z := by
    change _=‖g‖ • (‖g‖⁻¹ • CG.polynomialAction (cgOperator A) g p)
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg),one_smul]
  have hzz : inner ℝ z z=1 := by rw [real_inner_self_eq_norm_sq,last_lanczos_unit A hA g hg hc,one_pow]
  have he := congrArg (fun q => inner ℝ z (CG.polynomialAction (cgOperator A) g q))
    (eraseLead_add_monomial_natDegree_leadingCoeff p)
  rw [map_add,inner_add_right,hzero,zero_add,hdegree.1,← C_mul_X_pow_eq_monomial,
    ← smul_eq_C_mul,map_smul,real_inner_smul_right,hnorm,real_inner_smul_right,hzz,mul_one,hlead] at he
  have hpower : CG.polynomialAction (cgOperator A) g (X^n)=((cgOperator A)^n) g := by
    simp only [CG.polynomialAction,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.apply_apply,map_pow,aeval_X]
  rw [hpower] at he
  change inner ℝ z (((cgOperator A)^n) g)=‖g‖*L
  have hm := congrArg (fun x : ℝ => L*x) he
  rw [← mul_assoc,mul_inv_cancel₀ hL.ne',one_mul] at hm
  simpa only [mul_comm] using hm

end
end krylov.OneGradient
