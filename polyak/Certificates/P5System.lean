import polyak.Boundary.P5.SourceChebyshev

/-!
Article: (blowup), exact finite coefficient certificates for the actual
regularized P₅ equations.  Every array is related by a checked polynomial
identity to the separately defined Chebyshev source system.
-/
noncomputable section
namespace polyak.Certificates.P5
open Boundary.P5

/-- Article: coefficient block 0 of regularized equation 0. -/
def F0Part0 : SourcePolynomial :=
  MvPolynomial.C ((1/2) : ℚ)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C ((-1/4) : ℚ)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C ((-3/4) : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-3 : ℚ)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C ((1/4) : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C ((-3/2) : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 0. -/
def F0Part1 : SourcePolynomial :=
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C ((-3/2) : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C ((3/2) : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C ((1/2) : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 0. -/
def F0Part2 : SourcePolynomial :=
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-2 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)

/-- Article: exact coefficients of regularized equation 0. -/
def F0 : SourcePolynomial := F0Part0+F0Part1+F0Part2

/-- Article: coefficient block 0 of regularized equation 1. -/
def F1Part0 : SourcePolynomial :=
  MvPolynomial.C (4 : ℚ)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (3 : ℚ)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-7 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (6 : ℚ)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 1. -/
def F1Part1 : SourcePolynomial :=
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (5 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-2 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-3 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 1. -/
def F1Part2 : SourcePolynomial :=
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-5 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 3 of regularized equation 1. -/
def F1Part3 : SourcePolynomial :=
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 4 of regularized equation 1. -/
def F1Part4 : SourcePolynomial :=
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)

/-- Article: exact coefficients of regularized equation 1. -/
def F1 : SourcePolynomial := F1Part0+F1Part1+F1Part2+F1Part3+F1Part4

/-- Article: coefficient block 0 of regularized equation 2. -/
def F2Part0 : SourcePolynomial :=
  MvPolynomial.C (18 : ℚ)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (-1 : ℚ)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (9 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C (-32 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (9 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 2. -/
def F2Part1 : SourcePolynomial :=
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (36 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (40 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-32 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (8 : ℚ)*MvPolynomial.X (0 : Fin 8)^2

/-- Article: coefficient block 2 of regularized equation 2. -/
def F2Part2 : SourcePolynomial :=
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-8 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-32 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2

/-- Article: coefficient block 3 of regularized equation 2. -/
def F2Part3 : SourcePolynomial :=
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (36 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-56 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)

/-- Article: coefficient block 4 of regularized equation 2. -/
def F2Part4 : SourcePolynomial :=
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (56 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-32 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2

/-- Article: coefficient block 5 of regularized equation 2. -/
def F2Part5 : SourcePolynomial :=
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)

/-- Article: exact coefficients of regularized equation 2. -/
def F2 : SourcePolynomial := F2Part0+F2Part1+F2Part2+F2Part3+F2Part4+F2Part5

/-- Article: coefficient block 0 of regularized equation 3. -/
def F3Part0 : SourcePolynomial :=
  MvPolynomial.C (50 : ℚ)+
  MvPolynomial.C (-20 : ℚ)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (7 : ℚ)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-15 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-56 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (112 : ℚ)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (3 : Fin 8)^7*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (1 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 3. -/
def F3Part1 : SourcePolynomial :=
  MvPolynomial.C (200 : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (25 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-100 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (100 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (50 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-100 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (20 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-104 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 3. -/
def F3Part2 : SourcePolynomial :=
  MvPolynomial.C (224 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (280 : ℚ)*MvPolynomial.X (0 : Fin 8)^2+
  MvPolynomial.C (-336 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (100 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (400 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-100 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-100 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2

/-- Article: coefficient block 3 of regularized equation 3. -/
def F3Part3 : SourcePolynomial :=
  MvPolynomial.C (-50 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-164 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (4 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (152 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-100 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (20 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-20 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^3

/-- Article: coefficient block 4 of regularized equation 3. -/
def F3Part4 : SourcePolynomial :=
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (140 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-560 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (560 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (100 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (164 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-88 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-560 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (-152 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3

/-- Article: coefficient block 5 of regularized equation 3. -/
def F3Part5 : SourcePolynomial :=
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (20 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (40 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^4+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (5 : Fin 8)+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-560 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-560 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (400 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (88 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 6 of regularized equation 3. -/
def F3Part6 : SourcePolynomial :=
  MvPolynomial.C (400 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-416 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-560 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-40 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2

/-- Article: coefficient block 7 of regularized equation 3. -/
def F3Part7 : SourcePolynomial :=
  MvPolynomial.C (560 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-400 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^6+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (416 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (448 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)

/-- Article: coefficient block 8 of regularized equation 3. -/
def F3Part8 : SourcePolynomial :=
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^6*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^7+
  MvPolynomial.C (-448 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^6+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^7*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^6*MvPolynomial.X (4 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (4 : Fin 8)

/-- Article: exact coefficients of regularized equation 3. -/
def F3 : SourcePolynomial := F3Part0+F3Part1+F3Part2+F3Part3+F3Part4+F3Part5+F3Part6+F3Part7+F3Part8

/-- Article: coefficient block 0 of regularized equation 4. -/
def F4Part0 : SourcePolynomial :=
  MvPolynomial.C ((-3/2) : ℚ)+
  MvPolynomial.C ((13/2) : ℚ)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-6 : ℚ)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (21 : ℚ)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C ((-129/4) : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (63 : ℚ)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-78 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (27 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 4. -/
def F4Part1 : SourcePolynomial :=
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (116 : ℚ)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (3 : Fin 8)^6+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C ((-83/2) : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C ((93/2) : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-61 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (110 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-230 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 4. -/
def F4Part2 : SourcePolynomial :=
  MvPolynomial.C (291 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-366 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-101 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-92 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (112 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (252 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-304 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (484 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (304 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 3 of regularized equation 4. -/
def F4Part3 : SourcePolynomial :=
  MvPolynomial.C (176 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^6+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (42 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (18 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (18 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (3 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (60 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-90 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 4 of regularized equation 4. -/
def F4Part4 : SourcePolynomial :=
  MvPolynomial.C (120 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-120 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-354 : ℚ)*MvPolynomial.X (0 : Fin 8)^2+
  MvPolynomial.C (88 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-182 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 5 of regularized equation 4. -/
def F4Part5 : SourcePolynomial :=
  MvPolynomial.C (145 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-156 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-589 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (772 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-564 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (140 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (308 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (720 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (656 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 6 of regularized equation 4. -/
def F4Part6 : SourcePolynomial :=
  MvPolynomial.C (176 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^6+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (562 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (98 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (108 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (240 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 7 of regularized equation 4. -/
def F4Part7 : SourcePolynomial :=
  MvPolynomial.C (196 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-416 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-516 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (296 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-656 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-296 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-272 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (272 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (272 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-352 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (352 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (352 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 8 of regularized equation 4. -/
def F4Part8 : SourcePolynomial :=
  MvPolynomial.C (18 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (27 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 9 of regularized equation 4. -/
def F4Part9 : SourcePolynomial :=
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1178 : ℚ)*MvPolynomial.X (0 : Fin 8)^3+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-222 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-672 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-356 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (448 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 10 of regularized equation 4. -/
def F4Part10 : SourcePolynomial :=
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (304 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (832 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (240 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (352 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-240 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^6+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^6*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 11 of regularized equation 4. -/
def F4Part11 : SourcePolynomial :=
  MvPolynomial.C (2432 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1300 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (368 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-708 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-88 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1096 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-144 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-848 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (144 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 12 of regularized equation 4. -/
def F4Part12 : SourcePolynomial :=
  MvPolynomial.C (-544 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (544 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (544 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (258 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (2 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (92 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (40 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (120 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 13 of regularized equation 4. -/
def F4Part13 : SourcePolynomial :=
  MvPolynomial.C (52 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-52 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (224 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1864 : ℚ)*MvPolynomial.X (0 : Fin 8)^4+
  MvPolynomial.C (16 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-120 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 14 of regularized equation 4. -/
def F4Part14 : SourcePolynomial :=
  MvPolynomial.C (-328 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-344 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2608 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (336 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (496 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (400 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 15 of regularized equation 4. -/
def F4Part15 : SourcePolynomial :=
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (4984 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (296 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2048 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (224 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-992 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-592 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1056 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 16 of regularized equation 4. -/
def F4Part16 : SourcePolynomial :=
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-416 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-448 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (448 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (448 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1256 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (248 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (404 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)

/-- Article: coefficient block 17 of regularized equation 4. -/
def F4Part17 : SourcePolynomial :=
  MvPolynomial.C (272 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (188 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (352 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (144 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-352 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (368 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-368 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-368 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5

/-- Article: coefficient block 18 of regularized equation 4. -/
def F4Part18 : SourcePolynomial :=
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2096 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (80 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (5472 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 19 of regularized equation 4. -/
def F4Part19 : SourcePolynomial :=
  MvPolynomial.C (1504 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-608 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1344 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-448 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-576 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (576 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 20 of regularized equation 4. -/
def F4Part20 : SourcePolynomial :=
  MvPolynomial.C (2936 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (296 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (896 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (544 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-544 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4

/-- Article: coefficient block 21 of regularized equation 4. -/
def F4Part21 : SourcePolynomial :=
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-608 : ℚ)*MvPolynomial.X (0 : Fin 8)^6+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (832 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (3296 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 22 of regularized equation 4. -/
def F4Part22 : SourcePolynomial :=
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (3680 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (864 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 23 of regularized equation 4. -/
def F4Part23 : SourcePolynomial :=
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (0 : Fin 8)^7+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (2528 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (896 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2

/-- Article: coefficient block 24 of regularized equation 4. -/
def F4Part24 : SourcePolynomial :=
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^9*MvPolynomial.X (1 : Fin 8)^2

/-- Article: exact coefficients of regularized equation 4. -/
def F4 : SourcePolynomial := F4Part0+F4Part1+F4Part2+F4Part3+F4Part4+F4Part5+F4Part6+F4Part7+F4Part8+F4Part9+F4Part10+F4Part11+F4Part12+F4Part13+F4Part14+F4Part15+F4Part16+F4Part17+F4Part18+F4Part19+F4Part20+F4Part21+F4Part22+F4Part23+F4Part24

/-- Article: coefficient block 0 of regularized equation 5. -/
def F5Part0 : SourcePolynomial :=
  MvPolynomial.C (-12 : ℚ)+
  MvPolynomial.C (22 : ℚ)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-3 : ℚ)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-116 : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C (146 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-74 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (66 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (21 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (36 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (14 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (9 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 5. -/
def F5Part1 : SourcePolynomial :=
  MvPolynomial.C (-624 : ℚ)*MvPolynomial.X (0 : Fin 8)^2+
  MvPolynomial.C (292 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (156 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (174 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (180 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-300 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-135 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (372 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (138 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (108 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 5. -/
def F5Part2 : SourcePolynomial :=
  MvPolynomial.C (-144 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (224 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (84 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (3 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1784 : ℚ)*MvPolynomial.X (0 : Fin 8)^3+
  MvPolynomial.C (232 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-424 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1368 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-4 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1320 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 3 of regularized equation 5. -/
def F5Part3 : SourcePolynomial :=
  MvPolynomial.C (588 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-1608 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-108 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (336 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-336 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1432 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (348 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (344 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-432 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (1072 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-208 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 4 of regularized equation 5. -/
def F5Part4 : SourcePolynomial :=
  MvPolynomial.C (-72 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (72 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (68 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (92 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-2672 : ℚ)*MvPolynomial.X (0 : Fin 8)^4+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-272 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 5 of regularized equation 5. -/
def F5Part5 : SourcePolynomial :=
  MvPolynomial.C (3304 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-208 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1960 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (456 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-2892 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (944 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-944 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-720 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (720 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (720 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 6 of regularized equation 5. -/
def F5Part6 : SourcePolynomial :=
  MvPolynomial.C (2648 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (424 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-416 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (1680 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1952 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-120 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (120 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 7 of regularized equation 5. -/
def F5Part7 : SourcePolynomial :=
  MvPolynomial.C (232 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-52 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (360 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-40 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (400 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (40 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-144 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (144 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (144 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-2112 : ℚ)*MvPolynomial.X (0 : Fin 8)^5+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (4336 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)

/-- Article: coefficient block 8 of regularized equation 5. -/
def F5Part8 : SourcePolynomial :=
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1136 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-2160 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2976 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (1504 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-2400 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (2400 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2400 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^5

/-- Article: coefficient block 9 of regularized equation 5. -/
def F5Part9 : SourcePolynomial :=
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (208 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-3392 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-2928 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2432 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3

/-- Article: coefficient block 10 of regularized equation 5. -/
def F5Part10 : SourcePolynomial :=
  MvPolynomial.C (-2432 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-2432 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (480 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (176 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (816 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2

/-- Article: coefficient block 11 of regularized equation 5. -/
def F5Part11 : SourcePolynomial :=
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-832 : ℚ)*MvPolynomial.X (0 : Fin 8)^6+
  MvPolynomial.C (3424 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (432 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-576 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2256 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2368 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)

/-- Article: coefficient block 12 of regularized equation 5. -/
def F5Part12 : SourcePolynomial :=
  MvPolynomial.C (-2000 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (2000 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2000 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1056 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (-1056 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1056 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1120 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1344 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-2240 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-576 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2

/-- Article: coefficient block 13 of regularized equation 5. -/
def F5Part13 : SourcePolynomial :=
  MvPolynomial.C (-2976 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (576 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1664 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-1664 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1664 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (592 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (304 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (672 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)

/-- Article: coefficient block 14 of regularized equation 5. -/
def F5Part14 : SourcePolynomial :=
  MvPolynomial.C (-512 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (704 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7+
  MvPolynomial.C (1472 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (576 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (576 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^3

/-- Article: coefficient block 15 of regularized equation 5. -/
def F5Part15 : SourcePolynomial :=
  MvPolynomial.C (896 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^5+
  MvPolynomial.C (-1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (-1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-512 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (960 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-512 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3

/-- Article: coefficient block 16 of regularized equation 5. -/
def F5Part16 : SourcePolynomial :=
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (448 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-448 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)

/-- Article: coefficient block 17 of regularized equation 5. -/
def F5Part17 : SourcePolynomial :=
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (768 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^5

/-- Article: coefficient block 18 of regularized equation 5. -/
def F5Part18 : SourcePolynomial :=
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (2 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-512 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-640 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (2 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2

/-- Article: coefficient block 19 of regularized equation 5. -/
def F5Part19 : SourcePolynomial :=
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (2 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: exact coefficients of regularized equation 5. -/
def F5 : SourcePolynomial := F5Part0+F5Part1+F5Part2+F5Part3+F5Part4+F5Part5+F5Part6+F5Part7+F5Part8+F5Part9+F5Part10+F5Part11+F5Part12+F5Part13+F5Part14+F5Part15+F5Part16+F5Part17+F5Part18+F5Part19

/-- Article: coefficient block 0 of regularized equation 6. -/
def F6Part0 : SourcePolynomial :=
  MvPolynomial.C (21 : ℚ)+
  MvPolynomial.C (-16 : ℚ)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C ((-129/4) : ℚ)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (126 : ℚ)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-156 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (36 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (81 : ℚ)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (464 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 1 of regularized equation 6. -/
def F6Part1 : SourcePolynomial :=
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-288 : ℚ)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (110 : ℚ)*MvPolynomial.X (0 : Fin 8)+
  MvPolynomial.C (-80 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-230 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (582 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-732 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-202 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-276 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (336 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (756 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 2 of regularized equation 6. -/
def F6Part2 : SourcePolynomial :=
  MvPolynomial.C (-1216 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (1936 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1216 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (240 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-240 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-240 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1056 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-1056 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1056 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (12 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (3 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 3 of regularized equation 6. -/
def F6Part3 : SourcePolynomial :=
  MvPolynomial.C (120 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-180 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (360 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-480 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-360 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-480 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (480 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (480 : ℚ)*MvPolynomial.X (0 : Fin 8)*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 4 of regularized equation 6. -/
def F6Part4 : SourcePolynomial :=
  MvPolynomial.C (145 : ℚ)*MvPolynomial.X (0 : Fin 8)^2+
  MvPolynomial.C (-156 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-589 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1544 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-1128 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (280 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (924 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2160 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-640 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (2624 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 5 of regularized equation 6. -/
def F6Part5 : SourcePolynomial :=
  MvPolynomial.C (880 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-880 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-880 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1152 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (240 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (392 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-832 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1032 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 6 of regularized equation 6. -/
def F6Part6 : SourcePolynomial :=
  MvPolynomial.C (888 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-1968 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-888 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1760 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-12 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (27 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 7 of regularized equation 6. -/
def F6Part7 : SourcePolynomial :=
  MvPolynomial.C (-24 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (24 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (144 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-144 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-144 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^2*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-96 : ℚ)*MvPolynomial.X (0 : Fin 8)^3+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-672 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 8 of regularized equation 6. -/
def F6Part8 : SourcePolynomial :=
  MvPolynomial.C (3520 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-712 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (896 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (576 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (912 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2496 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (960 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (1408 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (960 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-960 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 9 of regularized equation 6. -/
def F6Part9 : SourcePolynomial :=
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (3 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1300 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (368 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-708 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-1536 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-2192 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-432 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-2544 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (432 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 10 of regularized equation 6. -/
def F6Part10 : SourcePolynomial :=
  MvPolynomial.C (-2176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (2176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2176 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1920 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (40 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (120 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (104 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-104 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 11 of regularized equation 6. -/
def F6Part11 : SourcePolynomial :=
  MvPolynomial.C (672 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-672 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-672 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (704 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^3*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-328 : ℚ)*MvPolynomial.X (0 : Fin 8)^4+
  MvPolynomial.C (-36 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-344 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (5216 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-160 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (672 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 12 of regularized equation 6. -/
def F6Part12 : SourcePolynomial :=
  MvPolynomial.C (1488 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1200 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (2048 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (224 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1024 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 13 of regularized equation 6. -/
def F6Part13 : SourcePolynomial :=
  MvPolynomial.C (-1984 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-1184 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-2112 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-2304 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-1248 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (2304 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1792 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (1792 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1792 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-640 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^4*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 14 of regularized equation 6. -/
def F6Part14 : SourcePolynomial :=
  MvPolynomial.C (404 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (272 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (188 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (704 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (288 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-704 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1104 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-1104 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1104 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^4*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)

/-- Article: coefficient block 15 of regularized equation 6. -/
def F6Part15 : SourcePolynomial :=
  MvPolynomial.C (-224 : ℚ)*MvPolynomial.X (0 : Fin 8)^5+
  MvPolynomial.C (-64 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (4192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (160 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (960 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1504 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-608 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-2688 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)

/-- Article: coefficient block 16 of regularized equation 6. -/
def F6Part16 : SourcePolynomial :=
  MvPolynomial.C (-320 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-896 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1728 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (1728 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (896 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)

/-- Article: coefficient block 17 of regularized equation 6. -/
def F6Part17 : SourcePolynomial :=
  MvPolynomial.C (96 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-1088 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (768 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-768 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^5*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^3*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6+
  MvPolynomial.C (1664 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (512 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)

/-- Article: coefficient block 18 of regularized equation 6. -/
def F6Part18 : SourcePolynomial :=
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-1408 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (-384 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (864 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (48 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)+
  MvPolynomial.C (32 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (640 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-640 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (192 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2+
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (7 : Fin 8)

/-- Article: coefficient block 19 of regularized equation 6. -/
def F6Part19 : SourcePolynomial :=
  MvPolynomial.C (-192 : ℚ)*MvPolynomial.X (0 : Fin 8)^6*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)^2*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (256 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)+
  MvPolynomial.C (-256 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (384 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2+
  MvPolynomial.C (128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)+
  MvPolynomial.C (-128 : ℚ)*MvPolynomial.X (0 : Fin 8)^7*MvPolynomial.X (1 : Fin 8)^2*MvPolynomial.X (3 : Fin 8)*MvPolynomial.X (6 : Fin 8)+
  MvPolynomial.C (64 : ℚ)*MvPolynomial.X (0 : Fin 8)^8*MvPolynomial.X (1 : Fin 8)^2

/-- Article: exact coefficients of regularized equation 6. -/
def F6 : SourcePolynomial := F6Part0+F6Part1+F6Part2+F6Part3+F6Part4+F6Part5+F6Part6+F6Part7+F6Part8+F6Part9+F6Part10+F6Part11+F6Part12+F6Part13+F6Part14+F6Part15+F6Part16+F6Part17+F6Part18+F6Part19

/-- Article: exact division by h of the 1-lag primal equation at all real data. -/
theorem primal_division_0 (z : Fin 8 → ℝ) :
    sourceEval z H*sourceEval z F0 = 1*sourceEval z (primalNumerator 1 (-1)) := by
  norm_num [sourceEval,F0,F0Part0,F0Part1,F0Part2,primalNumerator,sourceRaw,
    H,U,X,Y,Probability,Charge,G,sourceVar]
  ring

/-- Article: exact division by h of the 2-lag primal equation at all real data. -/
theorem primal_division_1 (z : Fin 8 → ℝ) :
    sourceEval z H*sourceEval z F1 = 2*sourceEval z (primalNumerator 2 (1)) := by
  norm_num [sourceEval,F1,F1Part0,F1Part1,F1Part2,F1Part3,F1Part4,primalNumerator,sourceRaw,
    H,U,X,Y,Probability,Charge,G,sourceVar]
  ring

/-- Article: exact division by h of the 3-lag primal equation at all real data. -/
theorem primal_division_2 (z : Fin 8 → ℝ) :
    sourceEval z H*sourceEval z F2 = 4*sourceEval z (primalNumerator 3 (1)) := by
  norm_num [sourceEval,F2,F2Part0,F2Part1,F2Part2,F2Part3,F2Part4,F2Part5,primalNumerator,sourceRaw,
    H,U,X,Y,Probability,Charge,G,sourceVar]
  ring

/-- Article: exact division by h of the 5-lag primal equation at all real data. -/
theorem primal_division_3 (z : Fin 8 → ℝ) :
    sourceEval z H*sourceEval z F3 = 4*sourceEval z (primalNumerator 5 (1)) := by
  norm_num [sourceEval,F3,F3Part0,F3Part1,F3Part2,F3Part3,F3Part4,F3Part5,F3Part6,F3Part7,F3Part8,primalNumerator,sourceRaw,
    H,U,X,Y,Probability,Charge,G,sourceVar]
  ring

/-- Article: the regularized dual equation is the actual cleared source equation. -/
theorem dual_source_0 (z : Fin 8 → ℝ) : sourceEval z F4 = sourceEval z (dualNumerator 0) := by
  norm_num [sourceEval,F4,F4Part0,F4Part1,F4Part2,F4Part3,F4Part4,F4Part5,F4Part6,F4Part7,F4Part8,F4Part9,F4Part10,F4Part11,F4Part12,F4Part13,F4Part14,F4Part15,F4Part16,F4Part17,F4Part18,F4Part19,F4Part20,F4Part21,F4Part22,F4Part23,F4Part24,dualNumerator,dualSource,dualDenominator,
    H,U,X,Y,W₂,W₃,W₅,G,sourceVar]
  ring

/-- Article: the regularized dual equation is the actual cleared source equation. -/
theorem dual_source_1 (z : Fin 8 → ℝ) : sourceEval z F5 = sourceEval z (dualNumerator 1) := by
  change sourceEval z F5=sourceEval z (dualSource.derivative.eval X)
  rw [dualSource_derivative]
  norm_num [sourceEval,F5,F5Part0,F5Part1,F5Part2,F5Part3,F5Part4,F5Part5,F5Part6,F5Part7,F5Part8,F5Part9,F5Part10,F5Part11,F5Part12,F5Part13,F5Part14,F5Part15,F5Part16,F5Part17,F5Part18,F5Part19,dualDerivativeSource,dualDenominator,
    H,U,X,Y,W₂,W₃,W₅,G,sourceVar]
  ring

/-- Article: the regularized dual equation is the actual cleared source equation. -/
theorem dual_source_2 (z : Fin 8 → ℝ) : sourceEval z F6 = sourceEval z (dualNumerator 2) := by
  change sourceEval z F6=sourceEval z (dualSource.derivative.eval Y)
  rw [dualSource_derivative]
  norm_num [sourceEval,F6,F6Part0,F6Part1,F6Part2,F6Part3,F6Part4,F6Part5,F6Part6,F6Part7,F6Part8,F6Part9,F6Part10,F6Part11,F6Part12,F6Part13,F6Part14,F6Part15,F6Part16,F6Part17,F6Part18,F6Part19,dualDerivativeSource,dualDenominator,
    H,U,X,Y,W₂,W₃,W₅,G,sourceVar]
  ring

end polyak.Certificates.P5
