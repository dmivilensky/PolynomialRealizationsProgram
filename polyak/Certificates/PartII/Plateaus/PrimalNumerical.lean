import polyak.CertifiedExamples.Plateaus.PrimalExpressions
import polyak.Certificates.PartII.Plateaus.Data

/-! Every non-tight residue and the actual source minimizer have strict positive signs. -/
namespace polyak.Certificates.PartII.Plateaus
open polyak.CertifiedExamples.Plateaus LeanCert.Core chebyshev2.Numerics

def row18PrimalBox : Fin 7 → IntervalRat := ![row18Xi 0,row18Xi 1,row18Xi 2,row18Cosines 0,row18Cosines 1,row18Right 0,row18Right 1]

def row18PrimalLagExpr (n:ℤ) : E 7 :=
  primalLag2Expr ![.variable 0,.variable 1,.variable 2] ![.variable 3,.variable 4] ![.variable 5,.variable 6] n

def row18PrimalMinExpr : E 7 :=
  primalMin2Expr ![.variable 0,.variable 1,.variable 2] ![.variable 3,.variable 4] ![.variable 5,.variable 6]

theorem row18_primal_lag02_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 2)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag03_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 3)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag04_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 4)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag05_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 5)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag06_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 6)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag07_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 7)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag08_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 8)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag09_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 9)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag10_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 10)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag11_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 11)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag12_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 12)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag13_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 13)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag15_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 15)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag16_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 16)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_primal_lag17_positive_checked :
    (IntervalExpr.neg (row18PrimalLagExpr 17)).strictNegative row18PrimalBox=true := by kernel_decide

theorem row18_inactive_checked : ∀n:Fin 18,0<n.val→n.val≠1→n.val≠14→
    (IntervalExpr.neg (row18PrimalLagExpr n.val)).strictNegative row18PrimalBox=true := by
  intro n hn hn1 hn14
  fin_cases n
  · norm_num at *
  · norm_num at *
  · exact row18_primal_lag02_positive_checked
  · exact row18_primal_lag03_positive_checked
  · exact row18_primal_lag04_positive_checked
  · exact row18_primal_lag05_positive_checked
  · exact row18_primal_lag06_positive_checked
  · exact row18_primal_lag07_positive_checked
  · exact row18_primal_lag08_positive_checked
  · exact row18_primal_lag09_positive_checked
  · exact row18_primal_lag10_positive_checked
  · exact row18_primal_lag11_positive_checked
  · exact row18_primal_lag12_positive_checked
  · exact row18_primal_lag13_positive_checked
  · norm_num at *
  · exact row18_primal_lag15_positive_checked
  · exact row18_primal_lag16_positive_checked
  · exact row18_primal_lag17_positive_checked

theorem row18_minimizer_positive_checked :
    (IntervalExpr.neg row18PrimalMinExpr).strictNegative row18PrimalBox=true := by kernel_decide

def row21PrimalBox : Fin 9 → IntervalRat := ![row21Xi 0,row21Xi 1,row21Xi 2,row21Cosines 0,row21Cosines 1,row21Cosines 2,row21Right 0,row21Right 1,row21Right 2]

def row21PrimalLagExpr (n:ℤ) : E 9 :=
  primalLag3Expr ![.variable 0,.variable 1,.variable 2] ![.variable 3,.variable 4,.variable 5] ![.variable 6,.variable 7,.variable 8] n

def row21PrimalMinExpr : E 9 :=
  primalMin3Expr ![.variable 0,.variable 1,.variable 2] ![.variable 3,.variable 4,.variable 5] ![.variable 6,.variable 7,.variable 8]

theorem row21_primal_lag02_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 2)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag03_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 3)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag04_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 4)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag05_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 5)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag06_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 6)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag07_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 7)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag08_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 8)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag10_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 10)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag11_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 11)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag12_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 12)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag13_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 13)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag14_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 14)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag15_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 15)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag16_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 16)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag18_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 18)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag19_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 19)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_primal_lag20_positive_checked :
    (IntervalExpr.neg (row21PrimalLagExpr 20)).strictNegative row21PrimalBox=true := by kernel_decide

theorem row21_inactive_checked : ∀n:Fin 21,0<n.val→n.val≠1→n.val≠9→n.val≠17→
    (IntervalExpr.neg (row21PrimalLagExpr n.val)).strictNegative row21PrimalBox=true := by
  intro n hn hn1 hn9 hn17
  fin_cases n
  · norm_num at *
  · norm_num at *
  · exact row21_primal_lag02_positive_checked
  · exact row21_primal_lag03_positive_checked
  · exact row21_primal_lag04_positive_checked
  · exact row21_primal_lag05_positive_checked
  · exact row21_primal_lag06_positive_checked
  · exact row21_primal_lag07_positive_checked
  · exact row21_primal_lag08_positive_checked
  · norm_num at *
  · exact row21_primal_lag10_positive_checked
  · exact row21_primal_lag11_positive_checked
  · exact row21_primal_lag12_positive_checked
  · exact row21_primal_lag13_positive_checked
  · exact row21_primal_lag14_positive_checked
  · exact row21_primal_lag15_positive_checked
  · exact row21_primal_lag16_positive_checked
  · norm_num at *
  · exact row21_primal_lag18_positive_checked
  · exact row21_primal_lag19_positive_checked
  · exact row21_primal_lag20_positive_checked

theorem row21_minimizer_positive_checked :
    (IntervalExpr.neg row21PrimalMinExpr).strictNegative row21PrimalBox=true := by kernel_decide

end polyak.Certificates.PartII.Plateaus
