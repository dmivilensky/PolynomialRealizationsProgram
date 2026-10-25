import polyak.CertifiedExamples.Rational.ThirteenBounds
import polyak.Numerics.KernelDecide

/-! Exact arithmetic acceptance of the archived root-of-unity coordinate boxes.
The source formula and all integer-lag reduction are independent maintained proofs. -/
namespace polyak.Certificates.PartII.Rational
open CertifiedExamples.Rational Farey.Examples chebyshev2.Numerics

theorem thirteen_min_checked :
    (IntervalExpr.neg normalizedMinExpression).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag01_checked :
    (IntervalExpr.neg (normalizedLagExpression 1)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag02_checked :
    (IntervalExpr.neg (normalizedLagExpression 2)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag03_checked :
    (IntervalExpr.neg (normalizedLagExpression 3)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag04_checked :
    (IntervalExpr.neg (normalizedLagExpression 4)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag05_checked :
    (IntervalExpr.neg (normalizedLagExpression 5)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag06_checked :
    (IntervalExpr.neg (normalizedLagExpression 6)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag07_checked :
    (IntervalExpr.neg (normalizedLagExpression 7)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag08_checked :
    (IntervalExpr.neg (normalizedLagExpression 8)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag09_checked :
    (IntervalExpr.neg (normalizedLagExpression 9)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag10_checked :
    (IntervalExpr.neg (normalizedLagExpression 10)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag11_checked :
    (IntervalExpr.neg (normalizedLagExpression 11)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_lag12_checked :
    (IntervalExpr.neg (normalizedLagExpression 12)).strictNegative thirteenBox=true := by kernel_decide

theorem thirteen_finite_signs : ThirteenFiniteSigns := by
  refine ⟨thirteen_min_nonneg_of_check thirteen_min_checked,?_⟩
  intro n
  fin_cases n
  · exact thirteen_lag_nonneg_of_check 1 thirteen_lag01_checked
  · exact thirteen_lag_nonneg_of_check 2 thirteen_lag02_checked
  · exact thirteen_lag_nonneg_of_check 3 thirteen_lag03_checked
  · exact thirteen_lag_nonneg_of_check 4 thirteen_lag04_checked
  · exact thirteen_lag_nonneg_of_check 5 thirteen_lag05_checked
  · exact thirteen_lag_nonneg_of_check 6 thirteen_lag06_checked
  · exact thirteen_lag_nonneg_of_check 7 thirteen_lag07_checked
  · exact thirteen_lag_nonneg_of_check 8 thirteen_lag08_checked
  · exact thirteen_lag_nonneg_of_check 9 thirteen_lag09_checked
  · exact thirteen_lag_nonneg_of_check 10 thirteen_lag10_checked
  · exact thirteen_lag_nonneg_of_check 11 thirteen_lag11_checked
  · exact thirteen_lag_nonneg_of_check 12 thirteen_lag12_checked

end polyak.Certificates.PartII.Rational
