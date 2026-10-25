import polyak.Boundary.P5.System
import polyak.Boundary.P5.Differential

/-!
Article: Theorem p5h0, the exact decoupled system at h=0.
Use: the low-degree critical equations are proved equal to the actual
regularized system at zero, before their Jacobian or solution is used.
-/
noncomputable section
namespace polyak.Boundary.P5
open Certificates.P5

/-- Article: exact critical source coefficient block 0 in equation 0. -/
def C0Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C ((1/2) : ℚ)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (4 : Fin 7)+
  MvPolynomial.C ((-1/4) : ℚ)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C ((-3/4) : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-3 : ℚ)*MvPolynomial.X (0 : Fin 7)

/-- Article: critical equation 0 as a polynomial in the seven unknowns. -/
def C0 : MvPolynomial (Fin 7) ℚ := C0Part0

/-- Article: exact critical source coefficient block 0 in equation 1. -/
def C1Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (4 : ℚ)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (4 : Fin 7)+
  MvPolynomial.C (3 : ℚ)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-7 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (2 : Fin 7)^4*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (6 : ℚ)*MvPolynomial.X (1 : Fin 7)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (0 : Fin 7)

/-- Article: critical equation 1 as a polynomial in the seven unknowns. -/
def C1 : MvPolynomial (Fin 7) ℚ := C1Part0

/-- Article: exact critical source coefficient block 0 in equation 2. -/
def C2Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (18 : ℚ)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (4 : Fin 7)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (9 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (2 : Fin 7)^4*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (2 : Fin 7)^5*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (1 : Fin 7)

/-- Article: critical equation 2 as a polynomial in the seven unknowns. -/
def C2 : MvPolynomial (Fin 7) ℚ := C2Part0

/-- Article: exact critical source coefficient block 0 in equation 3. -/
def C3Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (50 : ℚ)+
  MvPolynomial.C (-20 : ℚ)*MvPolynomial.X (4 : Fin 7)+
  MvPolynomial.C (7 : ℚ)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-15 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-56 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (112 : ℚ)*MvPolynomial.X (2 : Fin 7)^4*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (2 : Fin 7)^5*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (2 : Fin 7)^6*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (2 : Fin 7)^7*MvPolynomial.X (3 : Fin 7)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (1 : Fin 7)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 7)

/-- Article: critical equation 3 as a polynomial in the seven unknowns. -/
def C3 : MvPolynomial (Fin 7) ℚ := C3Part0

/-- Article: exact critical source coefficient block 0 in equation 4. -/
def C4Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C ((-3/2) : ℚ)+
  MvPolynomial.C ((13/2) : ℚ)*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (21 : ℚ)*MvPolynomial.X (2 : Fin 7)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C ((-129/4) : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (63 : ℚ)*MvPolynomial.X (2 : Fin 7)^2+
  MvPolynomial.C (-78 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (2 : Fin 7)^3+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (27 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (5 : Fin 7)

/-- Article: exact critical source coefficient block 1 in equation 4. -/
def C4Part1 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (2 : Fin 7)^4+
  MvPolynomial.C (116 : ℚ)*MvPolynomial.X (2 : Fin 7)^4*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (2 : Fin 7)^4*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (2 : Fin 7)^6+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (2 : Fin 7)^6*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (2 : Fin 7)^6*MvPolynomial.X (5 : Fin 7)

/-- Article: critical equation 4 as a polynomial in the seven unknowns. -/
def C4 : MvPolynomial (Fin 7) ℚ := C4Part0+C4Part1

/-- Article: exact critical source coefficient block 0 in equation 5. -/
def C5Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (-12 : ℚ)+
  MvPolynomial.C (22 : ℚ)*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-3 : ℚ)*MvPolynomial.X (5 : Fin 7)

/-- Article: critical equation 5 as a polynomial in the seven unknowns. -/
def C5 : MvPolynomial (Fin 7) ℚ := C5Part0

/-- Article: exact critical source coefficient block 0 in equation 6. -/
def C6Part0 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (21 : ℚ)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C ((-129/4) : ℚ)*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (126 : ℚ)*MvPolynomial.X (2 : Fin 7)+
  MvPolynomial.C (-156 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (2 : Fin 7)*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (2 : Fin 7)^2+
  MvPolynomial.C (36 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (81 : ℚ)*MvPolynomial.X (2 : Fin 7)^2*MvPolynomial.X (5 : Fin 7)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (2 : Fin 7)^3+
  MvPolynomial.C (464 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (2 : Fin 7)^3*MvPolynomial.X (5 : Fin 7)

/-- Article: exact critical source coefficient block 1 in equation 6. -/
def C6Part1 : MvPolynomial (Fin 7) ℚ :=
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (2 : Fin 7)^5+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (2 : Fin 7)^5*MvPolynomial.X (6 : Fin 7)+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (2 : Fin 7)^5*MvPolynomial.X (5 : Fin 7)

/-- Article: critical equation 6 as a polynomial in the seven unknowns. -/
def C6 : MvPolynomial (Fin 7) ℚ := C6Part0+C6Part1

/-- Article: the seven critical source polynomials, in the original equation order. -/
def criticalSource : Fin 7 → MvPolynomial (Fin 7) ℚ := ![C0,C1,C2,C3,C4,C5,C6]

/-- Article: critical polynomial in equation slot 0. -/
@[simp] theorem criticalSource_0 : criticalSource 0=C0 := rfl

/-- Article: critical polynomial in equation slot 1. -/
@[simp] theorem criticalSource_1 : criticalSource 1=C1 := rfl

/-- Article: critical polynomial in equation slot 2. -/
@[simp] theorem criticalSource_2 : criticalSource 2=C2 := rfl

/-- Article: critical polynomial in equation slot 3. -/
@[simp] theorem criticalSource_3 : criticalSource 3=C3 := rfl

/-- Article: critical polynomial in equation slot 4. -/
@[simp] theorem criticalSource_4 : criticalSource 4=C4 := rfl

/-- Article: critical polynomial in equation slot 5. -/
@[simp] theorem criticalSource_5 : criticalSource 5=C5 := rfl

/-- Article: critical polynomial in equation slot 6. -/
@[simp] theorem criticalSource_6 : criticalSource 6=C6 := rfl

/-- Article: exact specialization of the actual regularized equation 0 at h=0. -/
theorem regularSystem_zero_0 (Z : Coordinates) : regularSystem (0,Z) 0=polynomialValue C0 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_0,F0,F0Part0,F0Part1,F0Part2,
    polynomialValue,C0,C0Part0]

/-- Article: exact specialization of the actual regularized equation 1 at h=0. -/
theorem regularSystem_zero_1 (Z : Coordinates) : regularSystem (0,Z) 1=polynomialValue C1 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_1,F1,F1Part0,F1Part1,F1Part2,F1Part3,F1Part4,
    polynomialValue,C1,C1Part0]

/-- Article: exact specialization of the actual regularized equation 2 at h=0. -/
theorem regularSystem_zero_2 (Z : Coordinates) : regularSystem (0,Z) 2=polynomialValue C2 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_2,F2,F2Part0,F2Part1,F2Part2,F2Part3,F2Part4,F2Part5,
    polynomialValue,C2,C2Part0]

/-- Article: exact specialization of the actual regularized equation 3 at h=0. -/
theorem regularSystem_zero_3 (Z : Coordinates) : regularSystem (0,Z) 3=polynomialValue C3 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_3,F3,F3Part0,F3Part1,F3Part2,F3Part3,F3Part4,F3Part5,F3Part6,F3Part7,F3Part8,
    polynomialValue,C3,C3Part0]

/-- Article: exact specialization of the actual regularized equation 4 at h=0. -/
theorem regularSystem_zero_4 (Z : Coordinates) : regularSystem (0,Z) 4=polynomialValue C4 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_4,F4,F4Part0,F4Part1,F4Part2,F4Part3,F4Part4,F4Part5,F4Part6,F4Part7,F4Part8,F4Part9,F4Part10,F4Part11,F4Part12,F4Part13,F4Part14,F4Part15,F4Part16,F4Part17,F4Part18,F4Part19,F4Part20,F4Part21,F4Part22,F4Part23,F4Part24,
    polynomialValue,C4,C4Part0,C4Part1]

/-- Article: exact specialization of the actual regularized equation 5 at h=0. -/
theorem regularSystem_zero_5 (Z : Coordinates) : regularSystem (0,Z) 5=polynomialValue C5 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_5,F5,F5Part0,F5Part1,F5Part2,F5Part3,F5Part4,F5Part5,F5Part6,F5Part7,F5Part8,F5Part9,F5Part10,F5Part11,F5Part12,F5Part13,F5Part14,F5Part15,F5Part16,F5Part17,F5Part18,F5Part19,
    polynomialValue,C5,C5Part0]

/-- Article: exact specialization of the actual regularized equation 6 at h=0. -/
theorem regularSystem_zero_6 (Z : Coordinates) : regularSystem (0,Z) 6=polynomialValue C6 Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_6,F6,F6Part0,F6Part1,F6Part2,F6Part3,F6Part4,F6Part5,F6Part6,F6Part7,F6Part8,F6Part9,F6Part10,F6Part11,F6Part12,F6Part13,F6Part14,F6Part15,F6Part16,F6Part17,F6Part18,F6Part19,
    polynomialValue,C6,C6Part0,C6Part1]

/-- Article: the entire actual h=0 system is the explicit decoupled critical system. -/
theorem regularSystem_zero (Z : Coordinates) :
    regularSystem (0,Z)=(fun i => polynomialValue (criticalSource i) Z) := by
  ext i
  fin_cases i
  · exact regularSystem_zero_0 Z
  · exact regularSystem_zero_1 Z
  · exact regularSystem_zero_2 Z
  · exact regularSystem_zero_3 Z
  · exact regularSystem_zero_4 Z
  · exact regularSystem_zero_5 Z
  · exact regularSystem_zero_6 Z

end polyak.Boundary.P5
