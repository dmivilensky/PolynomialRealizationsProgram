import polyak.Boundary.P5.CriticalSystem

/-!
Article: Theorem p5h0, the two genuine critical Jacobian blocks.
Use: all entries are the actual formal partial derivatives of the h=0 system;
exact identities in ℚ(y₀) identify their finite algebraic representations.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5

/-- Article: the actual critical Jacobian, before any coefficient representation. -/
def criticalJacobian : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => polynomialValue (MvPolynomial.pderiv j (criticalSource i)) criticalPoint

/-- Article: exact algebraic representation of critical primal block entry (0,0). -/
def primalEntry00 : ℚ[X] := Polynomial.C (-3 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_0_0 : criticalJacobian 0 0=Polynomial.aeval y₀ primalEntry00 := by
  norm_num [criticalJacobian,criticalSource_0,C0,C0Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry00]

/-- Article: exact algebraic representation of critical primal block entry (0,1). -/
def primalEntry01 : ℚ[X] := Polynomial.C (0 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_0_1 : criticalJacobian 0 1=Polynomial.aeval y₀ primalEntry01 := by
  norm_num [criticalJacobian,criticalSource_0,C0,C0Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry01]

/-- Article: exact algebraic representation of critical primal block entry (0,2). -/
def primalEntry02 : ℚ[X] := Polynomial.C (1 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_0_2 : criticalJacobian 0 4=Polynomial.aeval y₀ primalEntry02 := by
  norm_num [criticalJacobian,criticalSource_0,C0,C0Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry02]

/-- Article: exact algebraic representation of critical primal block entry (0,3). -/
def primalEntry03 : ℚ[X] := Polynomial.C ((-1/4) : ℚ)+Polynomial.C ((-3/4) : ℚ)*Polynomial.X+Polynomial.C (1 : ℚ)*Polynomial.X^3

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_0_3 : criticalJacobian 0 3=Polynomial.aeval y₀ primalEntry03 := by
  norm_num [criticalJacobian,criticalSource_0,C0,C0Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry03]

/-- Article: exact algebraic representation of critical primal block entry (1,0). -/
def primalEntry10 : ℚ[X] := Polynomial.C (-6 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_1_0 : criticalJacobian 1 0=Polynomial.aeval y₀ primalEntry10 := by
  norm_num [criticalJacobian,criticalSource_1,C1,C1Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry10]

/-- Article: exact algebraic representation of critical primal block entry (1,1). -/
def primalEntry11 : ℚ[X] := Polynomial.C (6 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_1_1 : criticalJacobian 1 1=Polynomial.aeval y₀ primalEntry11 := by
  norm_num [criticalJacobian,criticalSource_1,C1,C1Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry11]

/-- Article: exact algebraic representation of critical primal block entry (1,2). -/
def primalEntry12 : ℚ[X] := Polynomial.C (-4 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_1_2 : criticalJacobian 1 4=Polynomial.aeval y₀ primalEntry12 := by
  norm_num [criticalJacobian,criticalSource_1,C1,C1Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry12]

/-- Article: exact algebraic representation of critical primal block entry (1,3). -/
def primalEntry13 : ℚ[X] := Polynomial.C (3 : ℚ)+Polynomial.C (4 : ℚ)*Polynomial.X+Polynomial.C (-7 : ℚ)*Polynomial.X^2+Polynomial.C (-4 : ℚ)*Polynomial.X^3+Polynomial.C (4 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_1_3 : criticalJacobian 1 3=Polynomial.aeval y₀ primalEntry13 := by
  norm_num [criticalJacobian,criticalSource_1,C1,C1Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry13]

/-- Article: exact algebraic representation of critical primal block entry (2,0). -/
def primalEntry20 : ℚ[X] := Polynomial.C (0 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_2_0 : criticalJacobian 2 0=Polynomial.aeval y₀ primalEntry20 := by
  norm_num [criticalJacobian,criticalSource_2,C2,C2Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry20]

/-- Article: exact algebraic representation of critical primal block entry (2,1). -/
def primalEntry21 : ℚ[X] := Polynomial.C (-12 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_2_1 : criticalJacobian 2 1=Polynomial.aeval y₀ primalEntry21 := by
  norm_num [criticalJacobian,criticalSource_2,C2,C2Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry21]

/-- Article: exact algebraic representation of critical primal block entry (2,2). -/
def primalEntry22 : ℚ[X] := Polynomial.C (-12 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_2_2 : criticalJacobian 2 4=Polynomial.aeval y₀ primalEntry22 := by
  norm_num [criticalJacobian,criticalSource_2,C2,C2Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry22]

/-- Article: exact algebraic representation of critical primal block entry (2,3). -/
def primalEntry23 : ℚ[X] := Polynomial.C ((-5/2) : ℚ)+Polynomial.C (15 : ℚ)*Polynomial.X+Polynomial.C (19 : ℚ)*Polynomial.X^2+Polynomial.C (-32 : ℚ)*Polynomial.X^3+Polynomial.C (4 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_2_3 : criticalJacobian 2 3=Polynomial.aeval y₀ primalEntry23 := by
  norm_num [criticalJacobian,criticalSource_2,C2,C2Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry23]
  linear_combination (1/2) * y₀_equation

/-- Article: exact algebraic representation of critical primal block entry (3,0). -/
def primalEntry30 : ℚ[X] := Polynomial.C (-12 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_3_0 : criticalJacobian 3 0=Polynomial.aeval y₀ primalEntry30 := by
  norm_num [criticalJacobian,criticalSource_3,C3,C3Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry30]

/-- Article: exact algebraic representation of critical primal block entry (3,1). -/
def primalEntry31 : ℚ[X] := Polynomial.C (24 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_3_1 : criticalJacobian 3 1=Polynomial.aeval y₀ primalEntry31 := by
  norm_num [criticalJacobian,criticalSource_3,C3,C3Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry31]

/-- Article: exact algebraic representation of critical primal block entry (3,2). -/
def primalEntry32 : ℚ[X] := Polynomial.C (-20 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_3_2 : criticalJacobian 3 4=Polynomial.aeval y₀ primalEntry32 := by
  norm_num [criticalJacobian,criticalSource_3,C3,C3Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry32]

/-- Article: exact algebraic representation of critical primal block entry (3,3). -/
def primalEntry33 : ℚ[X] := Polynomial.C ((161/8) : ℚ)+Polynomial.C (-69 : ℚ)*Polynomial.X+Polynomial.C ((-329/4) : ℚ)*Polynomial.X^2+Polynomial.C (177 : ℚ)*Polynomial.X^3+Polynomial.C (-59 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem primal_entry_3_3 : criticalJacobian 3 3=Polynomial.aeval y₀ primalEntry33 := by
  norm_num [criticalJacobian,criticalSource_3,C3,C3Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,primalEntry33]
  linear_combination (2*y₀^2 + y₀/2 - 35/8) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (0,0). -/
def dualEntry00 : ℚ[X] := Polynomial.C (0 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_0_0 : criticalJacobian 4 2=Polynomial.aeval y₀ dualEntry00 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry00]
  linear_combination (-374025600*y₀^4/43243231 - 627170400*y₀^3/43243231 - 138912480*y₀^2/43243231 + 155937300*y₀/43243231 + 57677070/43243231) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (0,1). -/
def dualEntry01 : ℚ[X] := Polynomial.C ((-3/8) : ℚ)+Polynomial.C ((-201/4) : ℚ)*Polynomial.X+Polynomial.C ((-309/4) : ℚ)*Polynomial.X^2+Polynomial.C (48 : ℚ)*Polynomial.X^3+Polynomial.C (45 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_0_1 : criticalJacobian 4 5=Polynomial.aeval y₀ dualEntry01 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry01]
  linear_combination (-3*y₀/2 - 15/8) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (0,2). -/
def dualEntry02 : ℚ[X] := Polynomial.C ((97/8) : ℚ)+Polynomial.C (-34 : ℚ)*Polynomial.X+Polynomial.C ((-429/4) : ℚ)*Polynomial.X^2+Polynomial.C (33 : ℚ)*Polynomial.X^3+Polynomial.C (65 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_0_2 : criticalJacobian 4 6=Polynomial.aeval y₀ dualEntry02 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry02]
  linear_combination (-3*y₀/2 - 15/8) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (1,0). -/
def dualEntry10 : ℚ[X] := Polynomial.C (0 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_1_0 : criticalJacobian 5 2=Polynomial.aeval y₀ dualEntry10 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry10]

/-- Article: exact algebraic representation of critical dual block entry (1,1). -/
def dualEntry11 : ℚ[X] := Polynomial.C (-3 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_1_1 : criticalJacobian 5 5=Polynomial.aeval y₀ dualEntry11 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry11]

/-- Article: exact algebraic representation of critical dual block entry (1,2). -/
def dualEntry12 : ℚ[X] := Polynomial.C (22 : ℚ)

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_1_2 : criticalJacobian 5 6=Polynomial.aeval y₀ dualEntry12 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry12]

/-- Article: exact algebraic representation of critical dual block entry (2,0). -/
def dualEntry20 : ℚ[X] := Polynomial.C ((4238173710/43243231) : ℚ)+Polynomial.C ((-11869154640/43243231) : ℚ)*Polynomial.X+Polynomial.C ((-18355172040/43243231) : ℚ)*Polynomial.X^2+Polynomial.C ((6613229280/43243231) : ℚ)*Polynomial.X^3+Polynomial.C ((-46281456000/43243231) : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_2_0 : criticalJacobian 6 2=Polynomial.aeval y₀ dualEntry20 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry20]
  linear_combination (-1870128000*y₀^3/43243231 - 3135852000*y₀^2/43243231 - 1716899040*y₀/43243231 - 1229124420/43243231) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (2,1). -/
def dualEntry21 : ℚ[X] := Polynomial.C ((-21/4) : ℚ)+Polynomial.C (-204 : ℚ)*Polynomial.X+Polynomial.C (27 : ℚ)*Polynomial.X^2+Polynomial.C (528 : ℚ)*Polynomial.X^3+Polynomial.C (-360 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_2_1 : criticalJacobian 6 5=Polynomial.aeval y₀ dualEntry21 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry21]
  linear_combination (-9) * y₀_equation

/-- Article: exact algebraic representation of critical dual block entry (2,2). -/
def dualEntry22 : ℚ[X] := Polynomial.C (11 : ℚ)+Polynomial.C (-264 : ℚ)*Polynomial.X+Polynomial.C (-18 : ℚ)*Polynomial.X^2+Polynomial.C (608 : ℚ)*Polynomial.X^3+Polynomial.C (-360 : ℚ)*Polynomial.X^4

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem dual_entry_2_2 : criticalJacobian 6 6=Polynomial.aeval y₀ dualEntry22 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,dualEntry22]
  linear_combination (-9) * y₀_equation

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_4_0 : criticalJacobian 4 0=0 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_4_1 : criticalJacobian 4 1=0 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_4_4 : criticalJacobian 4 4=0 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_4_3 : criticalJacobian 4 3=0 := by
  norm_num [criticalJacobian,criticalSource_4,C4,C4Part0,C4Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_5_0 : criticalJacobian 5 0=0 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_5_1 : criticalJacobian 5 1=0 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_5_4 : criticalJacobian 5 4=0 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_5_3 : criticalJacobian 5 3=0 := by
  norm_num [criticalJacobian,criticalSource_5,C5,C5Part0,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_6_0 : criticalJacobian 6 0=0 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_6_1 : criticalJacobian 6 1=0 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_6_4 : criticalJacobian 6 4=0 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_6_3 : criticalJacobian 6 3=0 := by
  norm_num [criticalJacobian,criticalSource_6,C6,C6Part0,C6Part1,polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

end polyak.Boundary.P5
