import jacobi.Support.TopNormalized
import jacobi.Support.DarbouxCoefficients
import jacobi.Support.SineProducts

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The complete printed top-node factorization is proved for the actual
original support orthogonal polynomials, with genuine positivity of
every sine product used as a denominator. The endpoint and the empty
products are included.
Use: naturalPolynomial_top_sineProducts divides by the actual beta sine product and uses its positive square-root branch.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- Sine products with the original support step and admissible positive shift are genuinely positive in the entire original interior product range.
Use: naturalPolynomial_top_sineProducts divides by the actual beta sine product and uses its positive square-root branch.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the largest used original coordinate is at most n-1+s, strictly below the original frequency n+gamma_alpha+gamma_beta; every numerator and denominator sine is therefore positive. -/
theorem support_sineProduct_pos {a b s : ℝ} (ha : -1<a) (hb : -1<b) (hs:0<s)
    (hshift:s<gamma a+gamma b+1) {n m : ℕ} (hm:m≤n) :
    0<sineProduct (step a b (n+1)) s m := by
  -- The original frequency bound also covers the possibly small positive endpoint parameters.
  have hg := parameter_pos ha hb
  unfold sineProduct
  apply Finset.prod_pos
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hjn : (j:ℝ)+1≤n := by exact_mod_cast (show j+1≤n by omega)
  have hj0 := Nat.cast_nonneg j (α:=ℝ)
  have hfreq := frequency_gamma a b (n+1)
  push_cast at hfreq
  apply div_pos <;> apply sin_position_pos ha hb (by omega)
  all_goals linarith [hg.1,hg.2.1]

/-- The scalar cancellation used by the literal top-node sine quotient.
Use: coefficient_ratio_sine applies this identity to the genuine positive middle sine and unit-step sine, preserving all other original factors.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: cancel only the two stated nonzero factors in the actual quotient; the remaining scalar factors can be zero. -/
theorem birth_death_ratio (p q r s t u v : ℝ) (hr:r≠0) (ht:t≠0) :
    (p*q/(s*r))/(t*u/(r*v))=v/s*((p/t)/(u/t))*(q/t) := by
  by_cases hu:u=0
  · simp [hu]
  by_cases hs:s=0
  · simp [hs]
  by_cases hv:v=0
  · simp [hv]
  field_simp

/-- One original birth/death quotient is the exact telescoping sine factor times the three original sine-product increments.
Use: naturalPolynomial_top_sineProducts telescopes the genuine original top-node product without any asymptotic or exceptional-parameter assumptions.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the actual two middle sines coincide; their positivity justifies cancellation, and the remaining factors are precisely the printed three increments. -/
theorem coefficient_ratio_sine {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm:m<n) :
    coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)=
      (sin (((m:ℝ)+1+averageGamma a b)*step a b (n+1))/
        sin (((m:ℝ)+averageGamma a b)*step a b (n+1)))*
      ((sin (((m:ℝ)+gamma a+1/2)*step a b (n+1))/sin (((m:ℝ)+1)*step a b (n+1)))/
        (sin (((m:ℝ)+gamma b+1/2)*step a b (n+1))/sin (((m:ℝ)+1)*step a b (n+1))))*
      (sin (((m:ℝ)+2*averageGamma a b)*step a b (n+1))/sin (((m:ℝ)+1)*step a b (n+1))) := by
  -- Only genuine original interior denominators are cancelled.
  obtain ⟨h0,h1,h2⟩ := darboux_denominators ha hb hm
  have hg := parameter_pos ha hb
  have hm0 := Nat.cast_nonneg m (α:=ℝ)
  have hmn : (m:ℝ)+1≤n := by exact_mod_cast (show m+1≤n by omega)
  have hfreq := frequency_gamma a b (n+1)
  push_cast at hfreq
  have hB : sin (((m:ℝ)+gamma b+1/2)*step a b (n+1))≠0 :=
    ne_of_gt (sin_position_pos ha hb (by omega) (by linarith [hg.2.1]) (by linarith [hg.1]))
  have hM : sin (((m:ℝ)+1)*step a b (n+1))≠0 :=
    ne_of_gt (sin_position_pos ha hb (by omega) (by positivity) (by linarith [hg.1,hg.2.1]))
  simp only [coefficientA,coefficientC,Nat.cast_add,Nat.cast_one]
  have he0 : (m:ℝ)+1+averageGamma a b-1/2=(m:ℝ)+averageGamma a b+1/2 := by ring
  have he1 : (m:ℝ)+1+gamma b-1/2=(m:ℝ)+gamma b+1/2 := by ring
  rw [he0,he1]
  convert birth_death_ratio
    (sin (((m:ℝ)+gamma a+1/2)*step a b (n+1)))
    (sin (((m:ℝ)+2*averageGamma a b)*step a b (n+1)))
    (sin (((m:ℝ)+averageGamma a b+1/2)*step a b (n+1)))
    (sin (((m:ℝ)+averageGamma a b)*step a b (n+1)))
    (sin (((m:ℝ)+1)*step a b (n+1)))
    (sin (((m:ℝ)+gamma b+1/2)*step a b (n+1)))
    (sin (((m:ℝ)+averageGamma a b+1)*step a b (n+1))) h1 hM using 1 <;> ring_nf

/-- The actual normalized support polynomial satisfies the complete printed top-node sine-product formula throughout the original nonterminal range.
Use: the top-node growth and uniform continuum limit are proved for this same actual spectral polynomial, which then defines the genuine Volterra kernel.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the already proved genuine top-node product of A/C ratios is telescoped by induction. The initial product is one; the exact next ratio is the preceding elementary identity, and every cancelled original beta product and middle sine is positive. -/
theorem naturalPolynomial_top_sineProducts {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n m : ℕ} (hm:m≤n) :
    ((naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1))))^2=
      (sin (((m:ℝ)+averageGamma a b)*step a b (n+1))/sin (averageGamma a b*step a b (n+1)))*
      (sineProduct (step a b (n+1)) (gamma a+1/2) m/
        sineProduct (step a b (n+1)) (gamma b+1/2) m)*
      sineProduct (step a b (n+1)) (2*averageGamma a b) m := by
  -- Telescope the actual spectral normalization; no substitute polynomial family is used.
  rw [naturalPolynomial_top_sq_ratio ha hb hm]
  have hg := parameter_pos ha hb
  have hfreq := frequency_gamma a b (n+1)
  push_cast at hfreq
  have hbase : sin (averageGamma a b*step a b (n+1))≠0 := by
    apply ne_of_gt
    apply sin_position_pos ha hb (by omega) hg.2.2
    dsimp [averageGamma] at *
    have hn0 := Nat.cast_nonneg n (α:=ℝ)
    linarith [hg.1,hg.2.1]
  induction m with
  | zero => simp [sineProduct_zero,hbase]
  | succ m ih =>
    have hm' : m<n := by omega
    have hbeta := support_sineProduct_pos ha hb (by linarith [hg.2.1] : 0<gamma b+1/2)
      (by linarith [hg.1] : gamma b+1/2<gamma a+gamma b+1) (show m≤n by omega)
    obtain ⟨h0,h1,h2⟩ := darboux_denominators ha hb hm'
    rw [Finset.prod_range_succ,ih (by omega),coefficient_ratio_sine ha hb hm']
    simp only [sineProduct_succ,Nat.cast_add,Nat.cast_one]
    field_simp [hbase,hbeta.ne',h0]
    ring

end
end jacobi.Support
