import krylov.Reference.PolynomialAction
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Use: transfer actual measured CG coefficients and original residual polynomials through equality of true normalized polynomial moments.
Source: genuine polynomial actions, the actual exact-line executor and real normalized physical polynomial Gram pairings.
-/

namespace krylov.Reference.CG
noncomputable section
open Polynomial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual normalized physical polynomial Gram form of the genuine operator and initial gradient.
Use: The actual normalized physical polynomial Gram form of the genuine operator and initial gradient.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Use the real polynomial actions and actual nonzero initial normalization. -/
def normalizedPolynomialGram (Q : E →L[ℝ] E) (g : E) (p q : ℝ[X]) : ℝ :=
  inner ℝ (polynomialAction Q g p) (polynomialAction Q g q)/‖g‖^2

/-- The actual polynomial action of X times a polynomial is the true original operator action on its actual polynomial vector.
Use: The actual polynomial action of X times a polynomial is the true original operator action on its actual polynomial vector.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Use the genuine operator functional calculus homomorphism. -/
theorem polynomialAction_X_mul (Q : E →L[ℝ] E) (g : E) (p : ℝ[X]) :
    polynomialAction Q g (X*p)=Q (polynomialAction Q g p) := by
  simp [polynomialAction,map_mul,aeval_X]

/-- Every actual measured CG line length is the genuine quotient of two normalized physical polynomial moments.
Use: Every actual measured CG line length is the genuine quotient of two normalized physical polynomial moments.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Identify the actual computed gradient, direction and probe polynomial actions and cancel the true nonzero initial norm factor. -/
theorem length_normalizedGram (Q : E →L[ℝ] E) (g : E) (hg : g≠0) (k : ℕ) :
    length Q g k= -normalizedPolynomialGram Q g (directionPolynomial Q g k) (residualPolynomial Q g k)/
      normalizedPolynomialGram Q g (directionPolynomial Q g k) (X*directionPolynomial Q g k) := by
  simp only [normalizedPolynomialGram,polynomialAction_X_mul,polynomialAction_pair]
  rw [neg_div,div_div_div_cancel_right₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))]
  exact neg_div _ _

/-- Every actual measured CG recurrence ratio is the genuine quotient of normalized polynomial residual energies.
Use: Every actual measured CG recurrence ratio is the genuine quotient of normalized polynomial residual energies.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Identify both true computed residual polynomial actions and cancel the actual nonzero common normalization. -/
theorem beta_normalizedGram (Q : E →L[ℝ] E) (g : E) (hg : g≠0) (k : ℕ) :
    beta Q g k=normalizedPolynomialGram Q g (residualPolynomial Q g (k+1)) (residualPolynomial Q g (k+1))/
      normalizedPolynomialGram Q g (residualPolynomial Q g k) (residualPolynomial Q g k) := by
  simp only [normalizedPolynomialGram,polynomialAction_pair,real_inner_self_eq_norm_sq]
  rw [div_div_div_cancel_right₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))]

/-- Genuine equality of all normalized physical polynomial moments gives exactly the same actual CG residual and direction polynomials through every real iteration.
Use: Genuine equality of all normalized physical polynomial moments gives exactly the same actual CG residual and direction polynomials through every real iteration.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Induct through actual measured line and recurrence ratios, using only true normalized polynomial moments. -/
theorem polynomials_of_normalizedGram (Q : E →L[ℝ] E) (P : F →L[ℝ] F) (g : E) (h : F)
    (hg : g≠0) (hh : h≠0)
    (hGram : ∀ p q,normalizedPolynomialGram Q g p q=normalizedPolynomialGram P h p q) (k : ℕ) :
    residualPolynomial Q g k=residualPolynomial P h k ∧
      directionPolynomial Q g k=directionPolynomial P h k := by
  -- The genuine line ratio fixes the next true residual before its actual energy ratio fixes the next direction.
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have hα : length Q g k=length P h k := by
      rw [length_normalizedGram Q g hg k,length_normalizedGram P h hh k,hGram,hGram,ih.1,ih.2]
    have hr : residualPolynomial Q g (k+1)=residualPolynomial P h (k+1) := by
      rw [residualPolynomial_succ,residualPolynomial_succ,ih.1,ih.2,hα]
    have hβ : beta Q g k=beta P h k := by
      rw [beta_normalizedGram Q g hg k,beta_normalizedGram P h hh k,hGram,hGram,hr,ih.1]
    exact ⟨hr,by rw [directionPolynomial_succ,directionPolynomial_succ,hr,ih.2,hβ]⟩

/-- Genuine equality of normalized physical polynomial moments gives the same actual CG line lengths and recurrence ratios, including stopped tails.
Use: Genuine equality of normalized physical polynomial moments gives the same actual CG line lengths and recurrence ratios, including stopped tails.
Article: main_krylov, prop:phi(b,c), genuine CG dependence on the original spectral measure.
Proof: Use the true polynomial transcript equality in the actual measured moment quotients. -/
theorem coefficients_of_normalizedGram (Q : E →L[ℝ] E) (P : F →L[ℝ] F) (g : E) (h : F)
    (hg : g≠0) (hh : h≠0)
    (hGram : ∀ p q,normalizedPolynomialGram Q g p q=normalizedPolynomialGram P h p q) (k : ℕ) :
    length Q g k=length P h k ∧ beta Q g k=beta P h k := by
  have hpol := polynomials_of_normalizedGram Q P g h hg hh hGram
  constructor
  · rw [length_normalizedGram Q g hg k,length_normalizedGram P h hh k,hGram,hGram,(hpol k).1,(hpol k).2]
  · rw [beta_normalizedGram Q g hg k,beta_normalizedGram P h hh k,hGram,hGram,(hpol (k+1)).1,(hpol k).1]
end
end krylov.Reference.CG
