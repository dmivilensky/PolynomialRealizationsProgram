import jacobi.Support.Coefficients
import jacobi.Support.DarbouxTrigonometry

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual support coefficients satisfy the exact endpoint Darboux
deletion identities: the smaller chain has alpha shifted by two and
the same original lattice step. These identities hold throughout the
full parameter range, including the exceptional average parameter.
Use: the rectangular factorization identifies the smaller actual Jacobi chain after deleting the original top eigenvalue.
-/
namespace jacobi.Support
noncomputable section
open Real Set jacobi.Reference

/-- The actual neighboring support coupling products have precisely the original Darboux parameter shift.
Use: the rectangular factorization identifies the smaller actual Jacobi chain after deleting the original top eigenvalue.
Article: jacobi, Appendix C.3 (top-node polynomials).
Source: elementary finite Darboux factorization, proved here from the original sine formulas.
Proof: after the exact unchanged-step and gamma-shift substitutions, both sides contain the same four genuine numerator and denominator sine factors. -/
theorem coefficient_darboux_product (a b : ℝ) (n m : ℕ) :
    coefficientA (a+2) b n m*coefficientC (a+2) b n (m+1)=
      coefficientA a b (n+1) (m+1)*coefficientC a b (n+1) (m+1) := by
  -- The identity only permutes the original four sine factors; it therefore needs no exceptional denominator exclusions.
  simp only [coefficientA,coefficientC,step_darboux,averageGamma,gamma,Nat.cast_add,Nat.cast_one]
  ring_nf

/-- All three actual interior denominator sines of the endpoint Darboux deletion are nonzero.
Use: coefficient_darboux_diagonal cancels only genuine positive original sine factors, with no generic-position restriction.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: their shifted original coordinates lie strictly between zero and N at every actual row of the smaller chain. -/
theorem darboux_denominators {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    sin (((m:ℝ)+averageGamma a b)*step a b (n+1))≠0 ∧
      sin (((m:ℝ)+averageGamma a b+1/2)*step a b (n+1))≠0 ∧
      sin (((m:ℝ)+averageGamma a b+1)*step a b (n+1))≠0 := by
  have hg := parameter_pos ha hb
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hmn : (m:ℝ)+1≤n := by exact_mod_cast (show m+1≤n by omega)
  have hfreq := frequency_gamma a b (n+1)
  push_cast at hfreq
  refine ⟨?_,?_,?_⟩
  all_goals apply ne_of_gt; apply sin_position_pos ha hb (by omega)
  all_goals dsimp [averageGamma] at *; linarith [hg.1,hg.2.1,hfreq]

/-- The actual original shifted diagonal birth sums have the exact top-node cosine difference required by Darboux deletion.
Use: the rectangular factorization identifies the entire smaller actual matrix, so induction determines the original full support spectrum.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: endpoint Christoffel transformation, proved directly using the preceding sine quotient identity.
Proof: express the four genuine original coefficients in the common center u=(m+bar_gamma)*h. The proved nonzero original sines discharge every quotient cancellation. The remaining sine expression is exactly twice the original neighboring-node cosine gap. -/
theorem coefficient_darboux_diagonal {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    coefficientA a b (n+1) m+coefficientC a b (n+1) (m+1)-
      (coefficientA (a+2) b n m+coefficientC (a+2) b n m)=
      2*(cos (gamma a*step a b (n+1))-cos (gamma (a+2)*step a b (n+1))) := by
  -- A single elementary identity handles the actual terminal rows and the original exceptional average parameter as well as all other rows.
  let h := step a b (n+1)
  let u := ((m:ℝ)+averageGamma a b)*h
  let v := ((gamma a-gamma b+1)/2)*h
  let w := averageGamma a b*h
  let t := h/2
  obtain ⟨hU,hM,hP⟩ := darboux_denominators ha hb hm
  have hmid : sin (u+t)≠0 := by convert hM using 1; congr 1; dsimp [u,t,h]; ring
  have hlast : sin (u+2*t)≠0 := by convert hP using 1; congr 1; dsimp [u,t,h]; ring
  have hquot := sine_quotient_darboux u v w t hU hmid hlast
  have hraw : coefficientA a b (n+1) m+coefficientC a b (n+1) (m+1)-
      (coefficientA (a+2) b n m+coefficientC (a+2) b n m)=4*sin (v+w)*sin t := by
    convert hquot using 1
    simp only [coefficientA,coefficientC,step_darboux,averageGamma,gamma,Nat.cast_add,Nat.cast_one,u,v,w,t,h]
    ring_nf
  rw [hraw]
  have hA := Real.cos_sub ((gamma a+1/2)*h) (h/2)
  have hB := Real.cos_add ((gamma a+1/2)*h) (h/2)
  have heA : (gamma a+1/2)*h-h/2=gamma a*h := by ring
  have heB : (gamma a+1/2)*h+h/2=gamma (a+2)*h := by dsimp [gamma]; ring
  rw [heA] at hA
  rw [heB] at hB
  have hsum : v+w=(gamma a+1/2)*h := by dsimp [v,w,averageGamma]; ring
  rw [hsum]
  change 4*sin ((gamma a+1/2)*h)*sin (h/2)=2*(cos (gamma a*h)-cos (gamma (a+2)*h))
  linear_combination -2*hA+2*hB

end
end jacobi.Support
