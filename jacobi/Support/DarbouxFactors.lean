import jacobi.Support.Chain
import jacobi.Support.Bidiagonal

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The endpoint Darboux factor uses the genuine original positive square
roots sqrt(A_m/2), sqrt(C_(m+1)/2). Their actual finite boundary and
coupling identities connect rectangular Gram products with exactly the
original symmetric support matrices.
Use: supportDarbouxFactor retains the genuine original A coefficients and its terminal zero.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference chebyshev2

/-- The actual original upper square-root factor of the endpoint Darboux matrix.
Use: supportDarbouxFactor retains the genuine original A coefficients and its terminal zero.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def upperFactor (a b : ℝ) (n m : ℕ) : ℝ := Real.sqrt (coefficientA a b (n+1) m/2)

/-- The actual original lower square-root factor of the endpoint Darboux matrix.
Use: supportDarbouxFactor retains the genuine original C coefficients at their unchanged adjacent indices.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def lowerFactor (a b : ℝ) (n m : ℕ) : ℝ := Real.sqrt (coefficientC a b (n+1) (m+1)/2)

/-- The genuine rectangular endpoint-deletion matrix of the original natural support chain.
Use: supportDarboux_original and supportDarboux_shifted prove its exact two actual Gram factorizations, yielding the complete original support spectrum.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def supportDarbouxFactor (a b : ℝ) (n : ℕ) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  bidiagonal n (upperFactor a b n) (lowerFactor a b n)

/-- The genuine original upper birth coefficient is nonnegative through the entire original finite block, including its terminal zero.
Use: upperFactor_sq discharges the actual square-root cancellation in the original Gram diagonal.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: every original interior coefficient is proved positive; the genuine final coefficient is proved zero. -/
theorem coefficientA_nonneg {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m≤n) :
    0≤coefficientA a b (n+1) m := by
  by_cases h : m=n
  · subst m
    simpa only [Nat.add_sub_cancel] using
      (show 0≤coefficientA a b (n+1) ((n+1)-1) from le_of_eq (coefficientA_terminal ha hb (by omega)).symm)
  · exact (coefficientA_pos ha hb (by omega)).le

/-- The actual upper factor square is exactly half its genuine original coefficient, including its actual terminal row.
Use: the larger and smaller actual Darboux Gram diagonals have their unchanged original A contributions.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: cancel the genuine square root using the independently proved original coefficient nonnegativity. -/
theorem upperFactor_sq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m≤n) :
    (upperFactor a b n m)^2=coefficientA a b (n+1) m/2 :=
  Real.sq_sqrt (div_nonneg (coefficientA_nonneg ha hb hm) (by norm_num))

/-- The actual lower factor square is exactly half its genuine original adjacent coefficient.
Use: both original Darboux Gram diagonals retain their actual C contributions.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the original positive interior C coefficient discharges the genuine square-root cancellation. -/
theorem lowerFactor_sq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    (lowerFactor a b n m)^2=coefficientC a b (n+1) (m+1)/2 :=
  Real.sq_sqrt (div_nonneg (coefficientC_pos ha hb (by omega) (by omega)).le (by norm_num))

/-- The actual original upper factor at the terminal boundary is zero.
Use: supportDarboux_original treats its last column exactly, including the one-dimensional case.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the genuine original terminal birth coefficient is zero. -/
theorem upperFactor_terminal (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    upperFactor a b n n=0 := by
  have h := coefficientA_terminal ha hb (show 0<n+1 by omega)
  simpa only [Nat.add_sub_cancel,upperFactor,h,zero_div,Real.sqrt_zero] using
    (show Real.sqrt (coefficientA a b (n+1) ((n+1)-1)/2)=0 by rw [h,zero_div,Real.sqrt_zero])

/-- The two genuine overlapping rectangular factors give exactly the original symmetric Jacobi coupling.
Use: both actual Darboux Gram upper diagonals are identified with the printed positive support couplings.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: combine the actual nonnegative square roots and multiply their original arguments; this is precisely the original squared support coupling. -/
theorem factor_product {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    upperFactor a b n m*lowerFactor a b n m=
      Real.sqrt (coefficientA a b (n+1) m*coefficientC a b (n+1) (m+1)/4) := by
  rw [upperFactor,lowerFactor,← Real.sqrt_mul (div_nonneg (coefficientA_nonneg ha hb hm.le) (by norm_num))]
  congr 1
  ring

end
end jacobi.Support
