import jacobi.Jacobi.BesselScaling
import Mathlib.Analysis.Complex.RealDeriv

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual terminating hypergeometric polynomial is real on the real axis.
Its real restriction therefore detects genuine complex polynomial zeros.
Source: the classical real rising-factorial Jacobi coefficients, DLMF 18.5.7.
Use: verifies reality of the actual finite Jacobi coefficients without a second polynomial definition.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Polynomial
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- Evaluation of every rising Pochhammer polynomial commutes with complex conjugation.
Use: verifies reality of the actual finite Jacobi coefficients without a second polynomial definition.
Article: jacobi, Proposition A.1.
Proof: induction uses the literal next-factor evaluation formula; both the natural shift and the initial value are real. -/
theorem pochhammer_conj (z : ℂ) (k : ℕ) :
    conj ((ascPochhammer ℂ k).eval z)=(ascPochhammer ℂ k).eval (conj z) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [ascPochhammer_succ_eval,_root_.map_mul,_root_.map_add,ih,conj_natCast]

/-- Every actual normalized Jacobi coefficient for real parameters is real.
Use: proves reality of the entire finite polynomial, including all its real-axis evaluations.
Article: jacobi, Proposition A.1.
Proof: conjugate the literal hypergeometric coefficient formula and
use the genuine Pochhammer conjugation identity on all three factors. -/
theorem coefficient_conj (a b : ℝ) (n k : ℕ) :
    conj (coefficient (a:ℂ) (b:ℂ) n k)=coefficient (a:ℂ) (b:ℂ) n k := by
  unfold coefficient ordinaryHypergeometricCoefficient
  simp only [_root_.map_mul,_root_.map_inv₀,pochhammer_conj,_root_.map_neg,_root_.map_add,
    conj_natCast,conj_ofReal,_root_.map_one]

/-- The actual normalized Jacobi polynomial is real on the real axis.
Use: the real intermediate value argument produces zeros of the original finite polynomial.
Article: jacobi, Proposition A.1.
Proof: conjugate the genuine terminating expansion. Every original
coefficient and every real argument power is fixed by conjugation. -/
theorem normalized_conj (a b x : ℝ) (n : ℕ) :
    conj (normalized (a:ℂ) (b:ℂ) n (x:ℂ))=normalized (a:ℂ) (b:ℂ) n (x:ℂ) := by
  simp only [normalized_eq_sum,_root_.map_sum,_root_.map_mul,_root_.map_pow,
    coefficient_conj,_root_.map_div₀,_root_.map_sub,_root_.map_one,conj_ofReal,conj_ofNat]

/-- The real restriction of the actual normalized Jacobi polynomial.
Use: finite real zero transfer while retaining the original entire polynomial as the mathematical object.
Article: jacobi, Proposition B.1.
-/
def realNormalized (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (normalized (a:ℂ) (b:ℂ) n (x:ℂ)).re

/-- A zero of the real restriction is a zero of the original complex Jacobi polynomial, and conversely.
Use: the intermediate value theorem proves actual finite polynomial zeros rather than zeros of a projection.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: reality makes the imaginary part zero, so the original value equals its embedded real part. -/
theorem realNormalized_zero_iff (a b x : ℝ) (n : ℕ) :
    realNormalized a b n x=0 ↔ normalized (a:ℂ) (b:ℂ) n (x:ℂ)=0 := by
  have he : normalized (a:ℂ) (b:ℂ) n (x:ℂ)=(realNormalized a b n x:ℂ) :=
    (Complex.conj_eq_iff_re.mp (normalized_conj a b x n)).symm
  rw [he,Complex.ofReal_eq_zero]

/-- The actual real Jacobi restriction is continuous everywhere.
Use: discharges the continuity premise for every compact interval used in finite-zero transfer.
Article: jacobi, Proposition A.1.
Proof: restrict the actual entire polynomial to real inputs and take its continuous real part. -/
theorem realNormalized_continuous (a b : ℝ) (n : ℕ) : Continuous (realNormalized a b n) := by
  have h : Continuous (normalized (a:ℂ) (b:ℂ) n) :=
    continuous_iff_continuousAt.mpr fun x => (normalized_analytic (a:ℂ) (b:ℂ) n x).continuousAt
  exact Complex.continuous_re.comp (h.comp Complex.continuous_ofReal)

end
end jacobi.Jacobi
