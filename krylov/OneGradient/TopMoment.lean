import krylov.OneGradient.PolynomialMoments
import jacobi.Finite.NormalizedPolynomials
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), exact first unfixed moment coefficient.
Use: isolate the first missing real moment of any actual polynomial integral,
with its coefficient tied to the original positive Jacobi link product.
Source: polynomial leading-monomial removal and the reused actual normalized
Lanczos--Stieltjes polynomial reconstruction.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial jacobi.Finite

/-- The first unshared moment controls exactly the integral of a polynomial
whose top degree is that first unshared order.
Use: the all-measures missing-moment affine formula follows from genuine
moment data rather than an assumed Jacobi moment field.
Article: main_krylov, s5:moment(b).
Proof: remove the actual leading monomial. The real lower-degree remainder
has equal integrals by the already proved finite moment comparison. -/
theorem top_moment_difference (F G : ℝ[X] →ₗ[ℝ] ℝ) (D : ℕ)
    (hm : ∀ k≤D,F (X^k)=G (X^k)) (p : ℝ[X]) (hp : p.natDegree=D+1) :
    F p-G p=p.leadingCoeff*(F (X^(D+1))-G (X^(D+1))) := by
  have hp0 : p≠0 := by intro he;rw [he,natDegree_zero] at hp;omega
  have hrem : p.eraseLead.natDegree≤D := by
    by_cases hz : p.eraseLead=0
    · rw [hz,natDegree_zero]
      exact Nat.zero_le D
    · have hd := degree_eraseLead_lt hp0
      rw [degree_eq_natDegree hz,degree_eq_natDegree hp0,hp] at hd
      have hn : p.eraseLead.natDegree<D+1 := by exact_mod_cast hd
      omega
  have he (L : ℝ[X] →ₗ[ℝ] ℝ) :
      L p=L p.eraseLead+p.leadingCoeff*L (X^(D+1)) := by
    have he := congrArg L (eraseLead_add_monomial_natDegree_leadingCoeff p)
    rw [map_add,hp,← smul_X_eq_monomial,map_smul,smul_eq_mul] at he
    exact he.symm
  rw [he F,he G,polynomial_integrals_eq_of_moments F G D hm p.eraseLead hrem]
  ring

/-- Every actual normalized spectral orthogonal polynomial has the reciprocal
positive Jacobi link product as its genuine leading coefficient.
Use: the printed missing-moment coefficient is exactly the square of that
actual link product, not an unspecified positive scale.
Article: main_krylov, s5:moment(b).
Proof: the existing genuine polynomial reconstruction is the monic leading
continuant multiplied by the reciprocal original positive coupling product. -/
theorem spectral_polynomial_leadingCoeff {N : ℕ} (M : DiscreteMeasure N) (i : Fin N) :
    (M.orthogonalPolynomial i).leadingCoeff=(M.reconstructed.data.linkProduct i.val)⁻¹ := by
  rw [← normalizedLeading_eq_orthogonalPolynomial,normalizedLeading,leadingCoeff_mul,leadingCoeff_C]
  have hm : (M.reconstructed.data.leading i.val).Monic :=
    M.reconstructed.data.block_monic M.reconstructed.coupling_nonneg 0 i.val
  rw [hm.leadingCoeff,mul_one]

end
end krylov.OneGradient
