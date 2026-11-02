import jacobi.Support.Coefficients

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual support birth coefficients reverse into each other by the
exact original period identity. Both genuine boundary zeros are
included, so the eventual matrix persymmetry has no endpoint exception.
Use: naturalChain_persymmetric proves literal reversal symmetry of the original support matrix and supports the actual finite spectral weight formula.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- Reversing the actual original support index exchanges its original A and C coefficients.
Use: naturalChain_persymmetric proves literal reversal symmetry of the original support matrix and supports the actual finite spectral weight formula.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: at the initial row both sides are the independently proved genuine boundary zeros. At every other row each original reversed sine angle is pi minus its actual matching lower-coefficient angle; sine reflection and commutativity finish the identity. -/
theorem coefficientA_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    coefficientA a b n (n-1-m)=coefficientC a b n m := by
  -- The same exact finite period handles every original row, including the actual terminal cancellation.
  have hn : 0<n := by omega
  by_cases hm0 : m=0
  · subst m
    simpa only [Nat.sub_zero,coefficientC_zero] using coefficientA_terminal ha hb hn
  have hcast : ((n-1-m:ℕ):ℝ)+(m:ℝ)+1=(n:ℝ) := by exact_mod_cast (show n-1-m+m+1=n by omega)
  have hcast' : ((n-1-m:ℕ):ℝ)=(n:ℝ)-1-m := by linarith
  have hperiod : ((n:ℝ)-1+gamma a+gamma b)*step a b n=Real.pi := by
    rw [← frequency_gamma]
    exact frequency_mul_step ha hb hn
  have h1 : (((n-1-m:ℕ):ℝ)+gamma a+1/2)*step a b n=
      Real.pi-((m:ℝ)+gamma b-1/2)*step a b n := by
    rw [hcast']
    linear_combination hperiod
  have h2 : (((n-1-m:ℕ):ℝ)+2*averageGamma a b)*step a b n=
      Real.pi-(m:ℝ)*step a b n := by rw [hcast']; dsimp [averageGamma]; linear_combination hperiod
  have h3 : (((n-1-m:ℕ):ℝ)+averageGamma a b)*step a b n=
      Real.pi-((m:ℝ)+averageGamma a b)*step a b n := by rw [hcast']; dsimp [averageGamma]; linear_combination hperiod
  have h4 : (((n-1-m:ℕ):ℝ)+averageGamma a b+1/2)*step a b n=
      Real.pi-((m:ℝ)+averageGamma a b-1/2)*step a b n := by rw [hcast']; dsimp [averageGamma]; linear_combination hperiod
  simp only [coefficientA,h1,h2,h3,h4,Real.sin_pi_sub,coefficientC]
  ring

/-- Reversing the original lower support coefficients recovers the actual upper coefficients, with both boundary values unchanged.
Use: naturalChain_persymmetric proves the original diagonal and adjacent coupling reversal identities.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: apply the proved actual A reflection at the reversed genuine original row and undo the index reversal. -/
theorem coefficientC_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    coefficientC a b n (n-1-m)=coefficientA a b n m := by
  have h := coefficientA_reflection ha hb (show n-1-m<n by omega)
  simpa only [show n-1-(n-1-m)=m by omega] using h.symm

end
end jacobi.Support
