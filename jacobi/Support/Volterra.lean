import jacobi.Support.TopSineProducts
import jacobi.Finite.DiscreteVolterra

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
Use: volterraKernel is the actual reduction-of-order kernel, and naturalWave_volterra identifies its solution with the original spectral wave.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial jacobi.Reference jacobi.Finite chebyshev1 chebyshev2

/-- The genuine original positive support polynomial value at the original top spectral node.
Use: volterraKernel is the actual reduction-of-order kernel, and naturalWave_volterra identifies its solution with the original spectral wave.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def topValue (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) : ℝ :=
  (naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1)))

/-- The actual complex support wave agrees with the genuine real polynomial at its original top node.
Use: naturalWave_volterra supplies the same positive reference solution to the general complex discrete Green identity.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: evaluation at a real point commutes with the actual real-to-complex algebra map. -/
theorem naturalWave_top (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) :
    naturalWave a b ha hb n m (cos (gamma a*step a b (n+1)):ℝ)=topValue a b ha hb n m := by
  exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _

/-- The genuine original support reduction-of-order kernel, with its actual positive couplings and actual top-node polynomial solution.
Use: naturalWave_volterra is the original exact spectral-variable Volterra equation, and the uniform support estimates bound this same original kernel.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def volterraKernel (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m j : ℕ) : ℝ :=
  topValue a b ha hb n m*topValue a b ha hb n j*
    ∑l∈Finset.Ico j m,(Real.sqrt ((naturalChain a b ha hb (n+1)).data.aSq (l+1))*
      topValue a b ha hb n l*topValue a b ha hb n (l+1))⁻¹

/-- The original reduction-of-order support kernel vanishes on and above its true Volterra diagonal.
Use: finite iterations of the genuine original Volterra equation are strictly triangular and terminate.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the original summation interval is empty when its lower endpoint is at least its upper endpoint. -/
theorem volterraKernel_zero (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m j : ℕ) (h:m≤j) :
    volterraKernel a b ha hb n m j=0 := by
  simp [volterraKernel,Finset.Ico_eq_empty_of_le h]

/-- The genuine original support reduction-of-order kernel is nonnegative at every actual interior polynomial coordinate.
Use: the original finite Volterra iterates preserve positivity, supplying the coefficientwise cosh and complex envelope estimates.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the genuine top-node values and each actual used coupling are positive. Every original inverse factor in the finite reduction-of-order sum is therefore nonnegative. -/
theorem volterraKernel_nonneg {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m j : ℕ}
    (hm:m≤n) (hj:j≤n) : 0≤volterraKernel a b ha hb n m j := by
  -- Every factor is an actual original support value, with no auxiliary positivity certificate.
  apply mul_nonneg
  · exact mul_nonneg (naturalPolynomial_top_pos ha hb hm).le (naturalPolynomial_top_pos ha hb hj).le
  · apply Finset.sum_nonneg
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    apply inv_nonneg.mpr
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (naturalPolynomial_top_pos ha hb (by omega)).le) (naturalPolynomial_top_pos ha hb (by omega)).le

/-- The actual original support wave satisfies the complete exact original Volterra equation at every complex energy and every genuine nonterminal degree.
Use: uniform Volterra iteration, frequency envelopes and the support edge limit apply to the same actual spectral orthogonal polynomials used in the finite target Gram matrix.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the actual normalized recurrence supplies both complex recurrence equations and their common initial value. Genuine top-node positivity and actual irreducible couplings discharge every nonzero factor. The general proved discrete Green formula then gives precisely this original real reduction-of-order kernel. -/
theorem naturalWave_volterra (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) (hm:m≤n) (y : ℂ) :
    naturalWave a b ha hb n m y=topValue a b ha hb n m+
      (y-(cos (gamma a*step a b (n+1)):ℝ))*
        ∑j∈Finset.range m,(volterraKernel a b ha hb n m j:ℂ)*naturalWave a b ha hb n j y := by
  -- All hypotheses below refer to the actual original matrix and original polynomials already reconstructed from its spectral measure.
  let J := naturalChain a b ha hb (n+1)
  let y₀ : ℂ := (cos (gamma a*step a b (n+1)):ℝ)
  let ac : ℕ→ℂ := fun k => (Real.sqrt (J.data.aSq k):ℂ)
  let bc : ℕ→ℂ := fun k => (J.data.b k:ℂ)
  let u : ℕ→ℂ := fun k => naturalWave a b ha hb n k y₀
  let v : ℕ→ℂ := fun k => naturalWave a b ha hb n k y
  have hrec (z : ℂ) (k : ℕ) (hk:k<n) :=
    normalizedLeading_recurrence J (naturalChain_irreducible a b ha hb (n+1)) z k (by omega)
  have h := discreteVolterra ac bc u v y₀ y n (fun k hk => hrec y₀ k hk) (fun k hk => hrec y k hk)
    (fun k hk => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (naturalChain_irreducible a b ha hb (n+1) (k+1) (by omega) (by omega))).ne')
    (normalizedLeading_zero J y₀) (normalizedLeading_zero J y)
    (fun k hk => by
      dsimp [u,y₀]
      rw [naturalWave_top]
      exact Complex.ofReal_ne_zero.mpr (naturalPolynomial_top_pos ha hb hk).ne') hm
  simpa only [u,v,discreteGreen,ac,J,y₀,naturalWave_top,volterraKernel,
    Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv] using h

end
end jacobi.Support
