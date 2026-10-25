import polyak.CertifiedExamples.Plateaus.CoordinateCode

namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core LeanCert.Engine chebyshev2.Numerics

def tCode (n : ℕ) : QPoly :=
  qsub (QPoly.constant 1) (((QPoly.constant 1).add (qneg QPoly.X)).mul (wPair n).1)

def pinningExpr {d : ℕ} (L : ℕ) (X : Fin 3 → E d) (n : ℤ) (c : E d) : E d :=
  times (cst L)
    (minus (qpolyExpr (tCode n.natAbs) c)
      (times (times (cst n.sign) (coefficientValueExpr X c))
        (qpolyExpr (uPair (n.natAbs-1)).1 c)))

noncomputable section

theorem tCode_value (n : ℕ) (c : ℝ) :
    Polynomial.aeval c (tCode n).toPoly=Spectral.chebT n c := by
  simp only [tCode,qsub,qneg,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
    QPoly.toPoly_X,map_add,map_mul,Polynomial.aeval_X,(wPair_value n c).1,
    map_neg,map_one]
  linear_combination -(ModeLocking.TwoLag.W_identity n c)

def polynomialPinning (L : ℕ) (X : Fin 3 → ℝ) (n : ℤ) (c : ℝ) : ℝ :=
  (L:ℝ)*(Spectral.chebT n.natAbs c-
    (n.sign:ℝ)*coefficientValue X c*Spectral.chebU (n.natAbs-1) c)

theorem pinningExpr_value {d : ℕ} (L : ℕ) (X : Fin 3 → E d) (n : ℤ)
    (c : E d) (v : Fin d → ℝ) :
    (pinningExpr L X n c).value v =
      polynomialPinning L (fun i=>(X i).value v) n (c.value v) := by
  simp only [pinningExpr,polynomialPinning,times,cst,minus,IntervalExpr.value,
    qpolyExpr_value,tCode_value,coefficientValueExpr_value,(uPair_value _ _).1,
    Rat.cast_natCast,Rat.cast_intCast,sub_eq_add_neg]

end
end polyak.CertifiedExamples.Plateaus
