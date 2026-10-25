import polyak.Boundary.P2.MomentSource

/-! Article: exact finite Chebyshev expansions for the source lag certificates. -/
namespace polyak.Boundary.P2
noncomputable section
open Polynomial
/-- Article: exact T0 polynomial in the finite lag prefix. -/
theorem Tpoly0 : Chebyshev.T ℝ 0=((1)*X^0) := by
  norm_num [Chebyshev.T]

/-- Article: exact T1 polynomial in the finite lag prefix. -/
theorem Tpoly1 : Chebyshev.T ℝ 1=((1)*X^1) := by
  norm_num [Chebyshev.T]

/-- Article: exact T2 polynomial in the finite lag prefix. -/
theorem Tpoly2 : Chebyshev.T ℝ 2=((2)*X^2+(-1)*X^0) := by
  have h := Chebyshev.T_add_two ℝ (0 : ℤ)
  change Chebyshev.T ℝ 2=2*X*Chebyshev.T ℝ 1-Chebyshev.T ℝ 0 at h
  rw [Tpoly1,Tpoly0] at h
  linear_combination h

/-- Article: exact T3 polynomial in the finite lag prefix. -/
theorem Tpoly3 : Chebyshev.T ℝ 3=((4)*X^3+(-3)*X^1) := by
  have h := Chebyshev.T_add_two ℝ (1 : ℤ)
  change Chebyshev.T ℝ 3=2*X*Chebyshev.T ℝ 2-Chebyshev.T ℝ 1 at h
  rw [Tpoly2,Tpoly1] at h
  linear_combination h

/-- Article: exact T4 polynomial in the finite lag prefix. -/
theorem Tpoly4 : Chebyshev.T ℝ 4=((8)*X^4+(-8)*X^2+(1)*X^0) := by
  have h := Chebyshev.T_add_two ℝ (2 : ℤ)
  change Chebyshev.T ℝ 4=2*X*Chebyshev.T ℝ 3-Chebyshev.T ℝ 2 at h
  rw [Tpoly3,Tpoly2] at h
  linear_combination h

/-- Article: exact T5 polynomial in the finite lag prefix. -/
theorem Tpoly5 : Chebyshev.T ℝ 5=((16)*X^5+(-20)*X^3+(5)*X^1) := by
  have h := Chebyshev.T_add_two ℝ (3 : ℤ)
  change Chebyshev.T ℝ 5=2*X*Chebyshev.T ℝ 4-Chebyshev.T ℝ 3 at h
  rw [Tpoly4,Tpoly3] at h
  linear_combination h

/-- Article: exact T6 polynomial in the finite lag prefix. -/
theorem Tpoly6 : Chebyshev.T ℝ 6=((32)*X^6+(-48)*X^4+(18)*X^2+(-1)*X^0) := by
  have h := Chebyshev.T_add_two ℝ (4 : ℤ)
  change Chebyshev.T ℝ 6=2*X*Chebyshev.T ℝ 5-Chebyshev.T ℝ 4 at h
  rw [Tpoly5,Tpoly4] at h
  linear_combination h

/-- Article: exact T7 polynomial in the finite lag prefix. -/
theorem Tpoly7 : Chebyshev.T ℝ 7=((64)*X^7+(-112)*X^5+(56)*X^3+(-7)*X^1) := by
  have h := Chebyshev.T_add_two ℝ (5 : ℤ)
  change Chebyshev.T ℝ 7=2*X*Chebyshev.T ℝ 6-Chebyshev.T ℝ 5 at h
  rw [Tpoly6,Tpoly5] at h
  linear_combination h

/-- Article: exact T8 polynomial in the finite lag prefix. -/
theorem Tpoly8 : Chebyshev.T ℝ 8=((128)*X^8+(-256)*X^6+(160)*X^4+(-32)*X^2+(1)*X^0) := by
  have h := Chebyshev.T_add_two ℝ (6 : ℤ)
  change Chebyshev.T ℝ 8=2*X*Chebyshev.T ℝ 7-Chebyshev.T ℝ 6 at h
  rw [Tpoly7,Tpoly6] at h
  linear_combination h

/-- Article: exact T9 polynomial in the finite lag prefix. -/
theorem Tpoly9 : Chebyshev.T ℝ 9=((256)*X^9+(-576)*X^7+(432)*X^5+(-120)*X^3+(9)*X^1) := by
  have h := Chebyshev.T_add_two ℝ (7 : ℤ)
  change Chebyshev.T ℝ 9=2*X*Chebyshev.T ℝ 8-Chebyshev.T ℝ 7 at h
  rw [Tpoly8,Tpoly7] at h
  linear_combination h

/-- Article: exact T10 polynomial in the finite lag prefix. -/
theorem Tpoly10 : Chebyshev.T ℝ 10=((512)*X^10+(-1280)*X^8+(1120)*X^6+(-400)*X^4+(50)*X^2+(-1)*X^0) := by
  have h := Chebyshev.T_add_two ℝ (8 : ℤ)
  change Chebyshev.T ℝ 10=2*X*Chebyshev.T ℝ 9-Chebyshev.T ℝ 8 at h
  rw [Tpoly9,Tpoly8] at h
  linear_combination h

/-- Article: exact U0 polynomial in the finite lag prefix. -/
theorem Upoly0 : Chebyshev.U ℝ 0=((1)*X^0) := by
  norm_num [Chebyshev.U]

/-- Article: exact U1 polynomial in the finite lag prefix. -/
theorem Upoly1 : Chebyshev.U ℝ 1=((2)*X^1) := by
  norm_num [Chebyshev.U]

/-- Article: exact U2 polynomial in the finite lag prefix. -/
theorem Upoly2 : Chebyshev.U ℝ 2=((4)*X^2+(-1)*X^0) := by
  have h := Chebyshev.U_add_two ℝ (0 : ℤ)
  change Chebyshev.U ℝ 2=2*X*Chebyshev.U ℝ 1-Chebyshev.U ℝ 0 at h
  rw [Upoly1,Upoly0] at h
  linear_combination h

/-- Article: exact U3 polynomial in the finite lag prefix. -/
theorem Upoly3 : Chebyshev.U ℝ 3=((8)*X^3+(-4)*X^1) := by
  have h := Chebyshev.U_add_two ℝ (1 : ℤ)
  change Chebyshev.U ℝ 3=2*X*Chebyshev.U ℝ 2-Chebyshev.U ℝ 1 at h
  rw [Upoly2,Upoly1] at h
  linear_combination h

/-- Article: exact U4 polynomial in the finite lag prefix. -/
theorem Upoly4 : Chebyshev.U ℝ 4=((16)*X^4+(-12)*X^2+(1)*X^0) := by
  have h := Chebyshev.U_add_two ℝ (2 : ℤ)
  change Chebyshev.U ℝ 4=2*X*Chebyshev.U ℝ 3-Chebyshev.U ℝ 2 at h
  rw [Upoly3,Upoly2] at h
  linear_combination h

/-- Article: exact U5 polynomial in the finite lag prefix. -/
theorem Upoly5 : Chebyshev.U ℝ 5=((32)*X^5+(-32)*X^3+(6)*X^1) := by
  have h := Chebyshev.U_add_two ℝ (3 : ℤ)
  change Chebyshev.U ℝ 5=2*X*Chebyshev.U ℝ 4-Chebyshev.U ℝ 3 at h
  rw [Upoly4,Upoly3] at h
  linear_combination h

/-- Article: exact U6 polynomial in the finite lag prefix. -/
theorem Upoly6 : Chebyshev.U ℝ 6=((64)*X^6+(-80)*X^4+(24)*X^2+(-1)*X^0) := by
  have h := Chebyshev.U_add_two ℝ (4 : ℤ)
  change Chebyshev.U ℝ 6=2*X*Chebyshev.U ℝ 5-Chebyshev.U ℝ 4 at h
  rw [Upoly5,Upoly4] at h
  linear_combination h

/-- Article: exact U7 polynomial in the finite lag prefix. -/
theorem Upoly7 : Chebyshev.U ℝ 7=((128)*X^7+(-192)*X^5+(80)*X^3+(-8)*X^1) := by
  have h := Chebyshev.U_add_two ℝ (5 : ℤ)
  change Chebyshev.U ℝ 7=2*X*Chebyshev.U ℝ 6-Chebyshev.U ℝ 5 at h
  rw [Upoly6,Upoly5] at h
  linear_combination h

/-- Article: exact U8 polynomial in the finite lag prefix. -/
theorem Upoly8 : Chebyshev.U ℝ 8=((256)*X^8+(-448)*X^6+(240)*X^4+(-40)*X^2+(1)*X^0) := by
  have h := Chebyshev.U_add_two ℝ (6 : ℤ)
  change Chebyshev.U ℝ 8=2*X*Chebyshev.U ℝ 7-Chebyshev.U ℝ 6 at h
  rw [Upoly7,Upoly6] at h
  linear_combination h

/-- Article: exact U9 polynomial in the finite lag prefix. -/
theorem Upoly9 : Chebyshev.U ℝ 9=((512)*X^9+(-1024)*X^7+(672)*X^5+(-160)*X^3+(10)*X^1) := by
  have h := Chebyshev.U_add_two ℝ (7 : ℤ)
  change Chebyshev.U ℝ 9=2*X*Chebyshev.U ℝ 8-Chebyshev.U ℝ 7 at h
  rw [Upoly8,Upoly7] at h
  linear_combination h

end
end polyak.Boundary.P2
