import jacobi.Jacobi.FiniteTrace
import jacobi.Jacobi.FiniteSpectrum

/-!
Article: jacobi, Theorem 5.1.
The actual normalized finite Jacobi function is exactly the product over
its genuine complete finite spectral zeros, at every complex argument.
This is the finite identity used to pass to the actual Bessel product.
Source: the proved real splitting, endpoint normalization and polynomial mapping to the complex field.
Use: applies polynomial factorization without introducing another enumeration of spectral zeros.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Complex Set
set_option backward.isDefEq.respectTransparency false

/-- Products over the actual full Jacobi root multiset equal products over the canonical finite ordering.
Use: applies polynomial factorization without introducing another enumeration of spectral zeros.
Article: jacobi, Theorem 5.1.
Proof: map the genuine product factors through the proved exact root multiset identity. -/
theorem shiftedRoots_prod {M : Type*} [CommMonoid M] {a b : ℝ}
    (ha : -1<a) (hb : -1<b) (n : ℕ) (f : ℝ → M) :
    ((shiftedPolynomial a b n).roots.map f).prod=∏ i:Fin n,f (shiftedRoots a b ha hb n i) := by
  have h := congrArg (fun s : Multiset ℝ => (s.map f).prod) (shiftedRoots_multiset ha hb n)
  simpa only [Multiset.map_map,Function.comp_def,Finset.prod] using h.symm

/-- The actual shifted real Jacobi polynomial is the product of its factors normalized to one at zero.
Use: gives the finite source canonical-product identity with its genuine normalization.
Article: jacobi, Proposition A.1.
Proof: the actual real splitting theorem gives the full root product.
Each root is positive, so normalize each factor by its nonzero value at
zero. The polynomial's actual value one at zero fixes the remaining constant. -/
theorem shiftedPolynomial_product {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (t : ℝ) :
    (shiftedPolynomial a b n).eval t=∏ i:Fin n,(1-t/shiftedRoots a b ha hb n i) := by
  -- The original endpoint normalization fixes the leading factor exactly.
  let p := shiftedPolynomial a b n
  have hsplit := (shiftedPolynomial_roots ha hb n).2.2.2
  have ht := hsplit.eval_eq_prod_roots t
  have h0 := hsplit.eval_eq_prod_roots 0
  rw [shiftedPolynomial_zero,shiftedRoots_prod ha hb n] at h0
  rw [shiftedRoots_prod ha hb n] at ht
  have he : (∏ i:Fin n,(t-shiftedRoots a b ha hb n i))=
      (∏ i:Fin n,(0-shiftedRoots a b ha hb n i))*(∏ i:Fin n,(1-t/shiftedRoots a b ha hb n i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    field_simp [(shiftedRoots_properties ha hb i).2.1.ne']
    ring
  rw [ht,he,← mul_assoc,← h0,one_mul]

/-- Mapping the actual shifted real polynomial to the complex field gives exactly the original terminating Jacobi function.
Use: the real factorization determines the source's entire complex finite function with no alternative special-function definition.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: map and evaluate its literal finite real coefficient expansion.
Conjugate symmetry identifies each embedded real coefficient with the
original complex coefficient; the affine argument reduces exactly to z. -/
theorem shiftedPolynomial_complex_eval (a b : ℝ) (n : ℕ) (z : ℂ) :
    ((shiftedPolynomial a b n).map Complex.ofRealHom).eval z=
      normalized (a:ℂ) (b:ℂ) n (1-2*z) := by
  -- The actual coefficient identity holds at every complex argument.
  rw [normalized_eq_sum]
  simp only [shiftedPolynomial,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_pow,Polynomial.map_X,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,ofRealHom_eq_coe]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (1-(1-2*z))/2=z by ring]
  rw [Complex.conj_eq_iff_re.mp (coefficient_conj a b n k)]

/-- The original entire complex Jacobi polynomial has the exact normalized product over its actual finite real zeros.
Use: establishes the genuine finite complex products whose Mehler--Heine limit is the source Bessel function.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the real identity is an equality of actual real polynomials.
Map that equality to the complex field and evaluate, using the proved
identification with the original complex hypergeometric polynomial. -/
theorem normalized_product {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (z : ℂ) :
    normalized (a:ℂ) (b:ℂ) n (1-2*z)=
      ∏ i:Fin n,(1-z/(shiftedRoots a b ha hb n i:ℂ)) := by
  -- Polynomial equality transfers the complete real factorization, including the exact scalar normalization.
  have hp : shiftedPolynomial a b n=
      ∏ i:Fin n,(1-C ((shiftedRoots a b ha hb n i)⁻¹)*X:Polynomial ℝ) := by
    apply Polynomial.funext
    intro t
    rw [shiftedPolynomial_product ha hb n]
    simp only [eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [← shiftedPolynomial_complex_eval,hp]
  simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X,ofRealHom_eq_coe,ofReal_inv]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The genuine squared-edge Jacobi function is the exact finite product over its actual squared spectral zeros at every complex point.
Use: the finite-to-infinite product and Rayleigh-sum proofs retain the original source special functions.
Article: jacobi, Theorem 5.1.
Proof: apply the actual complex normalized product at z/(4*n^2).
The proved positive finite roots and nonzero degree justify each exact spectral rescaling. -/
theorem normalized_scaled_product {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (z : ℂ) :
    normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2))=
      ∏ i:Fin n,(1-z/(finiteSigma a b ha hb n i:ℂ)) := by
  -- The same literal scaled finite polynomial appears in Mehler--Heine.
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  rw [show 1-z/(2*(n:ℂ)^2)=1-2*(z/(4*(n:ℂ)^2)) by ring,normalized_product ha hb n]
  apply Finset.prod_congr rfl
  intro i _
  have hi : (shiftedRoots a b ha hb n i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (shiftedRoots_properties ha hb i).2.1.ne'
  unfold finiteSigma
  push_cast
  field_simp [hnC,hi]

end
end jacobi.Jacobi
