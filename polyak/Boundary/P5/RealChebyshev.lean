import polyak.Spiral.KernelPolynomial

/-!
Article: Proposition p5divslack, the four active critical lags.
Use: exact small Chebyshev identities for the independently defined real source slacks.
-/
namespace polyak.Boundary.P5
open Spectral

private theorem T_one_eval (x : ℝ) : chebT 1 x=x := by simp [chebT]
private theorem T_two_eval (x : ℝ) : chebT 2 x=2*x^2-1 := by
  simp [chebT,Polynomial.Chebyshev.T_two]

@[simp] theorem chebT_three (x : ℝ) : chebT 3 x=4*x^3-3*x := by
  have h := Spiral.chebT_recurrence x 1
  change chebT 3 x=2*x*chebT 2 x-chebT 1 x at h
  rw [T_two_eval,T_one_eval] at h
  rw [h]
  ring

@[simp] theorem chebT_four (x : ℝ) : chebT 4 x=8*x^4-8*x^2+1 := by
  have h := Spiral.chebT_recurrence x 2
  change chebT 4 x=2*x*chebT 3 x-chebT 2 x at h
  rw [chebT_three,T_two_eval] at h
  rw [h]
  ring

@[simp] theorem chebT_five (x : ℝ) : chebT 5 x=16*x^5-20*x^3+5*x := by
  have h := Spiral.chebT_recurrence x 3
  change chebT 5 x=2*x*chebT 4 x-chebT 3 x at h
  rw [chebT_four,chebT_three] at h
  rw [h]
  ring

/-- Article: scalar U recurrence with natural lag indexing. -/
theorem chebU_recurrence (x : ℝ) (n : ℕ) : chebU (n+2) x=2*x*chebU (n+1) x-chebU n x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.U_add_two ℝ (n : ℤ))
  simpa only [chebU,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using h

private theorem U_one_eval (x : ℝ) : chebU 1 x=2*x := by simp [chebU]
private theorem U_two_eval (x : ℝ) : chebU 2 x=4*x^2-1 := by
  simp [chebU,Polynomial.Chebyshev.U_two]

@[simp] theorem chebU_three (x : ℝ) : chebU 3 x=8*x^3-4*x := by
  have h := chebU_recurrence x 1
  change chebU 3 x=2*x*chebU 2 x-chebU 1 x at h
  rw [U_two_eval,U_one_eval] at h
  rw [h]
  ring

@[simp] theorem chebU_four (x : ℝ) : chebU 4 x=16*x^4-12*x^2+1 := by
  have h := chebU_recurrence x 2
  change chebU 4 x=2*x*chebU 3 x-chebU 2 x at h
  rw [chebU_three,U_two_eval] at h
  rw [h]
  ring

end polyak.Boundary.P5
