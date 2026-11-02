import jacobi.Reference.BetaIntegral

/-!
Article: jacobi, Lemma C.1.
The genuine Jacobi norm is evaluated in Gamma functions from its proved
Sturm energy recurrence and the original convergent Beta integral. The
parameter-sum restriction used here holds for every reference exponent.
Source: the classical Jacobi norm formula, proved here for the actual
endpoint-normalized hypergeometric polynomials.
Use: evaluates the literal Poeschl--Teller norming constants after the proved cosine substitution.
-/
namespace jacobi.Reference
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/-- The actual weighted squared Jacobi norm has the exact classical Gamma value in the whole reference parameter range.
Use: evaluates the literal Poeschl--Teller norming constants after the proved cosine substitution.
Article: jacobi, Lemma C.1.
Proof: start from the actual convergent degree-zero Beta integral.
The proved Sturm norm recurrence shifts both parameters by one and
decreases the degree. Gamma(s+1)=s*Gamma(s) and factorial recurrence
identify each genuine next norm with the displayed closed formula.
All Gamma and scalar denominators are proved strictly positive. -/
theorem jacobiNorm_formula {a b : ℝ} (ha : -1<a) (hb : -1<b) (hab : 0<a+b+1) (n : ℕ) :
    jacobiNorm a b n=(n.factorial:ℝ)*Real.Gamma (a+1)^2*Real.Gamma (n+b+1)/
      ((2*n+a+b+1)*Real.Gamma (n+a+1)*Real.Gamma (n+a+b+1)) := by
  -- The induction concerns actual convergent norms, so it supplies rather than assumes the original special-function normalization.
  induction n generalizing a b with
  | zero =>
    rw [jacobiNorm_zero ha hb]
    norm_num only [Nat.cast_zero,Nat.factorial_zero,Nat.cast_one,one_mul,mul_zero,zero_add]
    have hsum : a+b+2=(a+b+1)+1 := by ring
    rw [hsum,Real.Gamma_add_one hab.ne']
    field_simp [(Real.Gamma_pos_of_pos (show 0<a+1 by linarith)).ne',
      (Real.Gamma_pos_of_pos hab).ne',hab.ne']
  | succ n ih =>
    rw [jacobiNorm_recurrence ha hb n,ih (by linarith) (by linarith) (by linarith)]
    have hA : 0<a+1 := by linarith
    have hB : 0<(n:ℝ)+b+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hAn : 0<(n:ℝ)+a+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hS : 0<(n:ℝ)+a+b+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hD : 0<2*(n:ℝ)+a+b+3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hG1 : Real.Gamma (a+1+1)=(a+1)*Real.Gamma (a+1) := Real.Gamma_add_one hA.ne'
    have hG2 : Real.Gamma ((n:ℝ)+(a+1)+(b+1)+1)=
        ((n:ℝ)+a+b+2)*Real.Gamma ((n:ℝ)+a+b+2) := by
      rw [show (n:ℝ)+(a+1)+(b+1)+1=((n:ℝ)+a+b+2)+1 by ring,Real.Gamma_add_one hS.ne']
    rw [hG1,hG2]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hnum : (n:ℝ)+(b+1)+1=(n:ℝ)+1+b+1 := by ring
    have hden1 : (n:ℝ)+(a+1)+1=(n:ℝ)+1+a+1 := by ring
    have hden2 : (n:ℝ)+a+b+2=(n:ℝ)+1+a+b+1 := by ring
    have hscalar : 2*(n:ℝ)+(a+1)+(b+1)+1=2*((n:ℝ)+1)+a+b+1 := by ring
    rw [hnum,hden1,hden2,hscalar]
    field_simp [hA.ne',show (n:ℝ)+1+a+b+1≠0 by linarith,
      show 2*((n:ℝ)+1)+a+b+1≠0 by linarith,
      (Real.Gamma_pos_of_pos (show 0<(n:ℝ)+1+a+1 by linarith)).ne',
      (Real.Gamma_pos_of_pos (show 0<(n:ℝ)+1+a+b+1 by linarith)).ne']

end
end jacobi.Reference
