import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
Article: chebyshev2, Lemma 23.
Lemma 23's exact translated polynomial, reusing mathlib's Hasse/Taylor theory.
Result: `chebyshev2.Numerics.translatePolynomial_eval` supplies the stated article conclusion.
Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients. The needed form is proved here.
-/
namespace chebyshev2.Numerics
noncomputable section
open Polynomial
set_option autoImplicit false

/--
Defines `translatePolynomial` of type `ℚ[X]` by `taylor c p`.

Use: `chebyshev2.Numerics.translatePolynomial_eval` uses this definition to establish exact
identity `(translatePolynomial p c).eval (q-c)=p.eval q`.

Article: chebyshev2, Lemma 23 via `chebyshev2.Numerics.translatePolynomial_binomial`.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.
-/
def translatePolynomial (p : ℚ[X]) (c : ℚ) : ℚ[X] := taylor c p

 /--
Exact identity `(translatePolynomial p c).coeff j=(hasseDeriv j p).eval c`.

Use: `chebyshev2.Numerics.translatePolynomial_binomial` rewrites with this identity to
establish the stated quantitative bound `(translatePolynomial p c).coeff j= p.sum (fun i a =>
(i.choose j:ℚ)*a*c^(i-j))`.

Article: chebyshev2, Lemma 23.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem translatePolynomial_coeff (p : ℚ[X]) (c : ℚ) (j : ℕ) :
    (translatePolynomial p c).coeff j=(hasseDeriv j p).eval c := taylor_coeff c p j

 /--
The stated quantitative bound `(translatePolynomial p c).coeff j= p.sum (fun i a => (i.choose
j:ℚ)*a*c^(i-j))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 23.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem translatePolynomial_binomial (p : ℚ[X]) (c : ℚ) (j : ℕ) :
    (translatePolynomial p c).coeff j=
      p.sum (fun i a => (i.choose j:ℚ)*a*c^(i-j)) := by
  rw [translatePolynomial_coeff,hasseDeriv_apply,eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

 /--
Exact identity `(translatePolynomial p c).eval (q-c)=p.eval q`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 23.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem translatePolynomial_eval (p : ℚ[X]) (c q : ℚ) :
    (translatePolynomial p c).eval (q-c)=p.eval q := by simpa [translatePolynomial] using taylor_eval c p (q-c)

 /--
Exact identity `(translatePolynomial p c).eval₂ (Rat.castHom ℝ) (q-c)=p.eval₂ (Rat.castHom ℝ)
q`.

Use: `chebyshev2.Numerics.translatedPolynomial_sound` uses this identity to establish exact
identity `translated.eval₂ (Rat.castHom ℝ) (q-c)=p.eval₂ (Rat.castHom ℝ) q`.

Article: chebyshev2, Lemma 23.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem translatePolynomial_real (p : ℚ[X]) (c : ℚ) (q : ℝ) :
    (translatePolynomial p c).eval₂ (Rat.castHom ℝ) (q-c)=p.eval₂ (Rat.castHom ℝ) q := by simp [translatePolynomial,taylor_apply,eval₂_comp]

 /--
Exact identity `translated.eval₂ (Rat.castHom ℝ) (q-c)=p.eval₂ (Rat.castHom ℝ) q`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 23.

Source: mathlib, Mathlib.Algebra.Polynomial.Taylor — Taylor/Hasse translation and binomial
coefficients.

Proof: Use the identities/estimates `chebyshev2.Numerics.translatePolynomial_real` with the
arguments shown in the proof.
-/
theorem translatedPolynomial_sound {p translated : ℚ[X]} {c : ℚ}
    (he : translated=translatePolynomial p c) (q : ℝ) :
    translated.eval₂ (Rat.castHom ℝ) (q-c)=p.eval₂ (Rat.castHom ℝ) q := by
  rw [he]
  exact translatePolynomial_real p c q

end
end chebyshev2.Numerics
