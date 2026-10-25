import polyak.CertifiedExamples.Exact313.Code

/-! The exact numerical reserves: coefficient-domain inequalities and the
finite residue kernels. These expressions encode source formulas, not outcomes. -/
namespace polyak.CertifiedExamples.Exact313.Code
open LeanCert.Core LeanCert.Engine

def psi (r c : Expr) : Expr := .div (numerator r c) (denominator r c)
def psiD (r c : Expr) : Expr := .div (derivativeNumerator r c) (.pow (denominator r c) 2)
def quadratic : Expr :=
  .div (.sub (.sub (psi (.var 1) (cosine 4)) (psi (.var 1) (cosine 6)))
    (.mul (psiD (.var 1) (cosine 6)) (.sub (cosine 4) (cosine 6))))
    (.pow (.sub (cosine 4) (cosine 6)) 2)
def linear : Expr :=
  .sub (psiD (.var 1) (cosine 6)) (.mul (.mul (.const 2) quadratic) (cosine 6))
def constant : Expr :=
  .add (.sub (psi (.var 1) (cosine 6))
    (.mul (psiD (.var 1) (cosine 6)) (cosine 6)))
    (.mul quadratic (.pow (cosine 6) 2))
def xi (c : Expr) : Expr :=
  .add (.add constant (.mul linear c)) (.mul quadratic (.pow c 2))
def angle (j : ℚ) : Expr := .mul (.const (2*j/13)) (.var 0)
def sine (j : ℚ) : Expr := .sin (angle j)
def cosineAt (j : ℚ) : Expr := .cos (angle j)
def lagNumerator (n : ℚ) (j : ℚ) : Expr :=
  .sub (.mul (xi (cosineAt j)) (.sub (.const 1) (cosineAt (n*j))))
    (.mul (sine j) (sine (n*j)))
def inactive (n : ℚ) : Expr :=
  .add (.mul (.neg (lagNumerator 1 2)) (lagNumerator n 3))
    (.mul (lagNumerator 1 3) (lagNumerator n 2))
def minimizer : Expr :=
  .add (.mul (.neg (lagNumerator 1 2)) (xi (cosineAt 3)))
    (.mul (lagNumerator 1 3) (xi (cosineAt 2)))
def sineNumerator (n j : ℚ) : Expr :=
  .sub (.mul (sine (n*j)) (xi (cosineAt j)))
    (.mul (cosineAt (n*j)) (sine j))
def determinant : Expr :=
  .sub (.mul (sineNumerator 1 3) (sineNumerator (-4) 2))
    (.mul (sineNumerator (-4) 3) (sineNumerator 1 2))

def reserves : Fin 17 → Expr := ![
  .var 1,
  .neg quadratic,
  .neg (xi (.const 1)),
  .neg (xi (.const (-1))),
  .neg (.add (.add linear (.const 1))
    (.mul (.mul (.const 2) quadratic) (.add (cosine 6) (cosine 4)))),
  inactive 2,inactive 3,inactive 4,inactive 5,inactive 6,inactive 7,inactive 8,
  inactive 10,inactive 11,inactive 12,minimizer,determinant]

end polyak.CertifiedExamples.Exact313.Code
