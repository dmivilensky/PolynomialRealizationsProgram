import jacobi.Reference.JacobiNorm

/-!
The Jacobi norm formula at every positive degree for the full parameter range.
The initial Beta norm is kept separately, so removable singularities at
parameter sum minus one never become zero denominators. One genuine Sturm
norm recurrence moves to shifted parameters already covered by the proved
Gamma formula.
Use: StandardJacobi normalizes the standard family without restricting the
sum of its two parameters or omitting its initial row.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the genuine Jacobi norm and its leading power normalization.
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
namespace jacobi.Reference
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/-- The actual norm in every positive degree has the classical Gamma
value throughout a,b>-1. The degree-zero value is the already proved
Beta integral `jacobiNorm_zero`, which remains regular at a+b=-1.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.3: the classical Jacobi squared-norm formula.
-/
theorem jacobiNorm_formula_succ {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    jacobiNorm a b (n+1)=((n+1).factorial:ℝ)*Gamma (a+1)^2*Gamma ((n+1:ℕ)+b+1)/
      ((2*((n+1:ℕ):ℝ)+a+b+1)*Gamma ((n+1:ℕ)+a+1)*Gamma ((n+1:ℕ)+a+b+1)) := by
  rw [jacobiNorm_recurrence ha hb n,jacobiNorm_formula (by linarith : -1<a+1) (by linarith : -1<b+1) (by linarith : 0<(a+1)+(b+1)+1) n]
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
