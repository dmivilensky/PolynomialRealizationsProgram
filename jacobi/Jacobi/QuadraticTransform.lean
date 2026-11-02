import jacobi.Jacobi.EquationUniqueness
import jacobi.Jacobi.Gegenbauer
import jacobi.Jacobi.FiniteProduct

/-!
Article: jacobi, Proposition A.1.
Source: DLMF 18.7.15--18.7.16.
Use: quadratic_transform_complex transfers the real polynomial identity to every complex argument, without a square-root branch.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Complex

/-- Complex evaluation of the actual real shifted polynomial is the original normalized Jacobi function.
Use: quadratic_transform_complex transfers the real polynomial identity to every complex argument, without a square-root branch.
Article: jacobi, Proposition A.1.
Proof: reuse the already proved complex evaluation of the same real polynomial; algebra evaluation is exactly evaluation after its coefficient map. -/
theorem shiftedPolynomial_aeval (a b : ℝ) (n : ℕ) (z : ℂ) :
    aeval z (shiftedPolynomial a b n)=normalized (a:ℂ) (b:ℂ) n (1-2*z) := by
  have hm : algebraMap ℝ ℂ=Complex.ofRealHom := by ext x; simp
  simpa only [aeval_def,eval₂_eq_eval_map,hm] using shiftedPolynomial_complex_eval a b n z

/-- Pulling back the shifted Jacobi equation by 4*t*(1-t) gives its even equal-parameter equation.
Use: quadratic_transform_even identifies the complete original polynomials by their actual differential equation.
Article: jacobi, Proposition A.1.
Proof: apply both polynomial chain rules and the inner Jacobi equation at 4*t*(1-t); the outer residual is exactly four times the inner one. -/
theorem quadratic_even_residual {a : ℝ} (ha : -1<a) (m : ℕ) :
    equationResidual a a (2*m)
      ((shiftedPolynomial a (-1/2) m).comp (C 4*X*(1-X)))=0 := by
  -- The pullback is an actual polynomial identity, including both endpoints.
  apply Polynomial.funext
  intro t
  rw [equationResidual_eval]
  simp [derivative_comp,derivative_mul]
  have h := congrArg (fun p : Polynomial ℝ => p.eval (4*t*(1-t)))
    (shiftedPolynomial_residual (b := -1/2) ha m)
  rw [equationResidual_eval,eval_zero] at h
  linear_combination 4*h

/-- The odd pullback has the additional factor 1-2*t and changes the inner Jacobi parameter to one half.
Use: quadratic_transform_odd supplies the parity factor in the literal Nesterov residual.
Article: jacobi, Proposition A.1.
Proof: differentiate the actual product and composition twice; the outer residual is four times 1-2*t times the original inner equation. -/
theorem quadratic_odd_residual {a : ℝ} (ha : -1<a) (m : ℕ) :
    equationResidual a a (2*m+1)
      ((1-C 2*X)*(shiftedPolynomial a (1/2) m).comp (C 4*X*(1-X)))=0 := by
  -- The remaining linear factor is retained, rather than absorbed into a chosen square root.
  apply Polynomial.funext
  intro t
  rw [equationResidual_eval]
  simp [derivative_comp,derivative_mul]
  have h := congrArg (fun p : Polynomial ℝ => p.eval (4*t*(1-t)))
    (shiftedPolynomial_residual (b := 1/2) ha m)
  rw [equationResidual_eval,eval_zero] at h
  simp only [one_div] at h
  linear_combination 4*(1-2*t)*h

/-- The normalized even equal-parameter polynomial is the exact quadratic Jacobi pullback.
Use: gegenbauer_quadratic_even proves Brakhage's literal residual formula and the even Nesterov factorization.
Article: jacobi, Proposition A.1.
Proof: the two genuine polynomials solve the same equation and equal one at zero; the previously proved coefficient uniqueness identifies them. -/
theorem quadratic_transform_even {a : ℝ} (ha : -1<a) (m : ℕ) :
    shiftedPolynomial a a (2*m)=
      (shiftedPolynomial a (-1/2) m).comp (C 4*X*(1-X)) := by
  apply equation_unique ha (2*m) _ _ (shiftedPolynomial_residual ha _) (quadratic_even_residual ha m)
  simp [shiftedPolynomial_zero]

/-- The normalized odd equal-parameter polynomial has the exact linear parity factor.
Use: gegenbauer_quadratic_odd proves the extra square-root factor in the original Nesterov formula.
Article: jacobi, Proposition A.1.
Proof: both actual polynomial solutions have value one at zero, so the original Jacobi equation's coefficient uniqueness applies. -/
theorem quadratic_transform_odd {a : ℝ} (ha : -1<a) (m : ℕ) :
    shiftedPolynomial a a (2*m+1)=
      (1-C 2*X)*(shiftedPolynomial a (1/2) m).comp (C 4*X*(1-X)) := by
  apply equation_unique ha (2*m+1) _ _ (shiftedPolynomial_residual ha _) (quadratic_odd_residual ha m)
  simp [shiftedPolynomial_zero]

/-- Both quadratic transformations hold at every complex point with their exact parity and normalization.
Use: gegenbauer_quadratic and the Nesterov application use this identity without introducing an analytic square-root choice.
Article: jacobi, Proposition A.1.
Proof: evaluate the proved real polynomial identity at (1-z)/2; its inner argument becomes 1-z squared. -/
theorem quadratic_transform_complex {a : ℝ} (ha : -1<a) {e : ℕ} (he : e≤1)
    (m : ℕ) (z : ℂ) :
    normalized (a:ℂ) (a:ℂ) (2*m+e) z=
      z^e*normalized (a:ℂ) ((e:ℂ)-1/2) m (2*z^2-1) := by
  -- The two parity cases follow from full polynomial identities, not only real-axis equalities.
  have harg : 1-2*((1-z)/2)=z := by ring
  have hinner : 1-2*(4*((1-z)/2)*(1-(1-z)/2))=2*z^2-1 := by ring
  interval_cases e
  · have h := congrArg (fun p : Polynomial ℝ => aeval ((1-z)/2) p) (quadratic_transform_even ha m)
    simp only [map_mul,aeval_C,aeval_X,aeval_comp,aeval_one,map_sub] at h
    norm_num only [map_ofNat] at h
    rw [shiftedPolynomial_aeval,harg,shiftedPolynomial_aeval,hinner] at h
    norm_num at h ⊢
    exact h
  · have h := congrArg (fun p : Polynomial ℝ => aeval ((1-z)/2) p) (quadratic_transform_odd ha m)
    simp only [map_mul,aeval_C,aeval_X,aeval_comp,aeval_one,map_sub] at h
    norm_num only [map_ofNat] at h
    rw [shiftedPolynomial_aeval,harg,shiftedPolynomial_aeval,hinner] at h
    norm_num at h ⊢
    exact h

end
end jacobi.Jacobi
