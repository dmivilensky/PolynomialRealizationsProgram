import jacobi.Support.Coefficients
import jacobi.Finite.Basic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The concrete original trigonometric coefficients are packaged in the
existing finite Jacobi type, with genuine nonnegative couplings, fixed
zero tails and strict interior irreducibility. No spectral or asymptotic
property is built into the definition.
Use: naturalChain retains the literal original three-term recurrence.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference chebyshev2

/-- The original natural support diagonal, before its fixed finite zero tail.
Use: naturalChain retains the literal original three-term recurrence.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def diagonal (a b : ℝ) (n m : ℕ) : ℝ :=
  cos (gamma a*step a b n)-(coefficientA a b n m+coefficientC a b n m)/2

/-- The actual original n-dimensional natural support Jacobi chain.
Use: its exact Darboux factorization proves the original support spectrum, and the finite spectral-weight theory constructs the support polynomial system for the persymmetric limit.
Article: jacobi, Appendix C.3 (coefficient bounds).
-/
def naturalChain (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : Jacobi n where
  data := {
    b := fun m => if m<n then diagonal a b n m else 0
    aSq := fun m => if 0<m ∧ m<n then coefficientA a b n (m-1)*coefficientC a b n m/4 else 0 }
  coupling_nonneg m := by
    dsimp
    split_ifs with hm
    · exact (div_pos (mul_pos (coefficientA_pos ha hb (by omega)) (coefficientC_pos ha hb hm.1 hm.2)) (by norm_num)).le
    · exact le_rfl
  coupling_zero := by simp
  diagonal_tail m hm := by simp [not_lt.mpr hm]
  coupling_tail m hm := by simp [not_lt.mpr hm]

/-- Every actual natural support diagonal entry has exactly the printed original value.
Use: the matrix Darboux and reversal identities compare the same literal original finite coefficients.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: its index lies in the genuine original finite block, so the unused tail branch does not contribute. -/
theorem naturalChain_diagonal (a b : ℝ) (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    (naturalChain a b ha hb n).data.b m=diagonal a b n m := by
  exact ite_eq_left hm

/-- Every actual natural support interior squared coupling is the printed original product A_(m-1)*C_m/4.
Use: the actual symmetric matrix has the source's original positive square-root couplings.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: its positive genuine interior index selects the original finite coefficient branch. -/
theorem naturalChain_coupling (a b : ℝ) (ha : -1<a) (hb : -1<b) {n m : ℕ}
    (hm : 0<m) (hmn : m<n) :
    (naturalChain a b ha hb n).data.aSq m=coefficientA a b n (m-1)*coefficientC a b n m/4 := by
  exact ite_eq_left ⟨hm,hmn⟩

/-- The actual original natural support chain is irreducible at every finite dimension.
Use: the finite inverse-spectral theorem and positive top-node polynomial system apply to the actual original chain, including all small dimensions.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: both independently proved original birth coefficients are strictly positive at every genuine interior edge. -/
theorem naturalChain_irreducible (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalChain a b ha hb n).Irreducible := by
  intro m hm hmn
  rw [naturalChain_coupling a b ha hb hm hmn]
  exact div_pos (mul_pos (coefficientA_pos ha hb (by omega)) (coefficientC_pos ha hb hm hmn)) (by norm_num)

end
end jacobi.Support
