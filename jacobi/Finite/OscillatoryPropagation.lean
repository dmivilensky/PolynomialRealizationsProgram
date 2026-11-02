import jacobi.Finite.PrefixGronwall

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The inverse-square recurrence error has a finite total effect after
the original transition index. A telescoping reciprocal majorant gives
the exponential estimate directly on the actual finite prefix.
Source: multiplicative discrete Gronwall inequality.
Use: inverse_square_propagation has the exact original summable perturbation exponent with no infinite-tail hypothesis.
-/
namespace jacobi.Finite
noncomputable section
open Real

/-- The actual inverse-square step error is bounded by the telescoping reciprocal difference.
Use: inverse_square_propagation has the exact original summable perturbation exponent with no infinite-tail hypothesis.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the reciprocal difference is 1/((m+1)*(m+2)), which is at least 1/(m+2)^2. -/
theorem inverse_square_step (m:ℕ) :
    1/((m:ℝ)+2)^2≤1/((m:ℝ)+1)-1/((m:ℝ)+2) := by
  have h1 : 0<(m:ℝ)+1 := by positivity
  have h2 : 0<(m:ℝ)+2 := by positivity
  rw [one_div,one_div,one_div]
  field_simp
  nlinarith

/-- An actual finite multiplicative inverse-square perturbation has the full original exponential propagation bound from its genuine transition index.
Use: the support oscillatory envelope applies this to the original two-component free-wave state, with A proportional to the inverse free spectral gap.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: multiplicative discrete Gronwall inequality, proved here by a telescoping reciprocal majorant.
Proof: bound each factor 1+A/(m+2)^2 by the exponential of A*(1/(m+1)-1/(m+2)). Induction makes those reciprocal differences telescope exactly. Dropping the final nonnegative reciprocal term gives the printed uniform finite-prefix bound. -/
theorem inverse_square_propagation (v:ℕ→ℝ) (L M:ℕ) (hLM:L≤M) {rho A:ℝ}
    (hA:0≤A) (hv:∀m≤M,0≤v m)
    (hstep:∀m,L≤m→m<M→v (m+1)≤exp rho*(1+A/((m:ℝ)+2)^2)*v m) :
    v M≤v L*exp (rho*((M-L:ℕ):ℝ)+A/((L:ℝ)+1)) := by
  -- The exact original transition index remains in the telescoping exponent until the final nonnegative term is discarded.
  let r : ℕ→ℝ := fun m => 1/((m:ℝ)+1)
  have hall : ∀k,L+k≤M→v (L+k)≤v L*exp (rho*(k:ℝ)+
      A*(r L-r (L+k))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hpoint := hstep (L+k) (by omega) (by omega)
      have hrec := inverse_square_step (L+k)
      have hexp : 1+A/(((L+k:ℕ):ℝ)+2)^2≤exp (A*(r (L+k)-r (L+k+1))) := by
        have hlin : A/(((L+k:ℕ):ℝ)+2)^2≤A*(r (L+k)-r (L+k+1)) := by
          simpa only [r,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num,mul_one_div] using
            mul_le_mul_of_nonneg_left hrec hA
        exact (add_le_add le_rfl hlin).trans
          (by simpa only [add_comm] using add_one_le_exp (A*(r (L+k)-r (L+k+1))))
      calc
        _ ≤ exp rho*(1+A/(((L+k:ℕ):ℝ)+2)^2)*v (L+k) := by simpa only [Nat.add_assoc] using hpoint
        _ ≤ exp rho*exp (A*(r (L+k)-r (L+k+1)))*
            (v L*exp (rho*(k:ℝ)+A*(r L-r (L+k)))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexp (exp_pos _).le
          · exact hprev
          · exact hv _ (by omega)
          · positivity
        _ = v L*exp (rho+A*(r (L+k)-r (L+k+1))+rho*(k:ℝ)+A*(r L-r (L+k))) := by
          simp only [exp_add]
          ring
        _ = _ := by congr 1; simp only [Nat.cast_add,Nat.cast_one,Nat.add_assoc]; ring
  have h := hall (M-L) (by omega)
  rw [Nat.add_sub_of_le hLM] at h
  have hfinal : rho*((M-L:ℕ):ℝ)+A*(r L-r M)≤rho*((M-L:ℕ):ℝ)+A/((L:ℝ)+1) := by
    have hrM : 0≤r M := by dsimp [r]; positivity
    calc
      _ = rho*((M-L:ℕ):ℝ)+A/((L:ℝ)+1)-A*r M := by dsimp [r]; ring
      _ ≤ _ := sub_le_self _ (mul_nonneg hA hrM)
  exact h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hfinal) (hv L hLM))

end
end jacobi.Finite
