import polyak.Boundary.P5.SystemSource

/-!
Article: (p5system), small Chebyshev source identities in the exact polynomial ring.
Use: expand precisely the four active primal lags and the central dual numerator.
-/
namespace polyak.Boundary.P5
noncomputable section

@[simp] theorem sourceT_one (a : SourcePolynomial) : sourceT 1 a=a := by
  simp [sourceT]
@[simp] theorem sourceT_two (a : SourcePolynomial) : sourceT 2 a=2*a^2-1 := by
  simp [sourceT,Polynomial.Chebyshev.T_two]
@[simp] theorem sourceU_zero (a : SourcePolynomial) : sourceU 0 a=1 := by
  simp [sourceU]
@[simp] theorem sourceU_one (a : SourcePolynomial) : sourceU 1 a=2*a := by
  simp [sourceU]
@[simp] theorem sourceU_two (a : SourcePolynomial) : sourceU 2 a=4*a^2-1 := by
  simp [sourceU,Polynomial.Chebyshev.U_two]

theorem sourceT_recurrence (a : SourcePolynomial) (n : ℕ) :
    sourceT (n+2) a=2*a*sourceT (n+1) a-sourceT n a := by
  have h := congrArg (Polynomial.eval₂RingHom MvPolynomial.C a)
    (Polynomial.Chebyshev.T_add_two ℚ (n : ℤ))
  simpa only [sourceT,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,map_sub,map_mul,
    map_ofNat,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using h

theorem sourceU_recurrence (a : SourcePolynomial) (n : ℕ) :
    sourceU (n+2) a=2*a*sourceU (n+1) a-sourceU n a := by
  have h := congrArg (Polynomial.eval₂RingHom MvPolynomial.C a)
    (Polynomial.Chebyshev.U_add_two ℚ (n : ℤ))
  simpa only [sourceU,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,map_sub,map_mul,
    map_ofNat,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using h

@[simp] theorem sourceT_three (a : SourcePolynomial) : sourceT 3 a=4*a^3-3*a := by
  have h := sourceT_recurrence a 1
  norm_num at h
  rw [h]
  ring

@[simp] theorem sourceT_four (a : SourcePolynomial) : sourceT 4 a=8*a^4-8*a^2+1 := by
  have h := sourceT_recurrence a 2
  norm_num at h
  rw [h]
  ring

@[simp] theorem sourceT_five (a : SourcePolynomial) : sourceT 5 a=16*a^5-20*a^3+5*a := by
  have h := sourceT_recurrence a 3
  norm_num at h
  rw [h]
  ring

@[simp] theorem sourceU_three (a : SourcePolynomial) : sourceU 3 a=8*a^3-4*a := by
  have h := sourceU_recurrence a 1
  norm_num at h
  rw [h]
  ring

@[simp] theorem sourceU_four (a : SourcePolynomial) : sourceU 4 a=16*a^4-12*a^2+1 := by
  have h := sourceU_recurrence a 2
  norm_num at h
  rw [h]
  ring

/-- Article: exact formal differentiation of the separately defined central dual source. -/
theorem dualSource_derivative : dualSource.derivative=dualDerivativeSource := by
  simp only [dualSource,dualDerivativeSource]
  simp only [Polynomial.derivative_neg,Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_mul,
    Polynomial.derivative_pow,Polynomial.derivative_C,Polynomial.derivative_X,
    Polynomial.derivative_ofNat]
  norm_num
  simp only [Polynomial.C_ofNat]
  generalize (Polynomial.C (W₂*(sourceU 2 G*sourceU 4 G*MvPolynomial.C (1/2))) :
    Polynomial SourcePolynomial) = a₂
  generalize (Polynomial.C (W₃*(G*sourceU 4 G)) : Polynomial SourcePolynomial) = a₃
  generalize (Polynomial.C (W₅*(G*sourceU 2 G)) : Polynomial SourcePolynomial) = a₅
  generalize (Polynomial.C dualDenominator : Polynomial SourcePolynomial) = d
  generalize (Polynomial.C G : Polynomial SourcePolynomial) = g
  generalize (Polynomial.C U : Polynomial SourcePolynomial) = u
  ring

end
end polyak.Boundary.P5
