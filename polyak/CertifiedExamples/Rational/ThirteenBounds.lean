import polyak.CertifiedExamples.Rational.ThirteenSource
import polyak.Certificates.PartII.Trigonometry.Bounds

/-! The arithmetic box contains actual root-of-unity coordinates; certificate
acceptance is therefore a statement about the original probability slacks. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels chebyshev2.Numerics LeanCert.Core
open polyak.Certificates.PartII.Trigonometry

def thirteenBox (i:Fin 26) : IntervalRat :=
  if h:i.val<13 then cos13Interval ⟨i.val,h⟩
  else sin13Interval ⟨i.val-13,by omega⟩

theorem thirteenCoordinates_mem : ∀i,thirteenCoordinates i∈thirteenBox i := by
  intro i
  by_cases h:i.val<13
  · simpa [thirteenCoordinates,thirteenBox,h,gridCos]
      using cos13_mem ⟨i.val,h⟩
  · simpa [thirteenCoordinates,thirteenBox,h,gridSin]
      using sin13_mem ⟨i.val-13,by omega⟩

theorem thirteen_min_nonneg_of_check
    (hc:(IntervalExpr.neg normalizedMinExpression).strictNegative thirteenBox=true) :
    0≤thirteenRawMin := by
  have h:=(IntervalExpr.neg normalizedMinExpression).strictNegative_sound thirteenBox hc thirteenCoordinates_mem
  have hp : 0<normalizedMinExpression.value thirteenCoordinates := by
    change -normalizedMinExpression.value thirteenCoordinates<0 at h
    linarith
  rw [thirteen_min_source]
  exact (mul_pos normalizationFactor_pos hp).le

theorem thirteen_lag_nonneg_of_check (n:ℕ)
    (hc:(IntervalExpr.neg (normalizedLagExpression n)).strictNegative thirteenBox=true) :
    0≤thirteenRawLag n := by
  have h:=(IntervalExpr.neg (normalizedLagExpression n)).strictNegative_sound thirteenBox hc thirteenCoordinates_mem
  have hp : 0<(normalizedLagExpression n).value thirteenCoordinates := by
    change -(normalizedLagExpression n).value thirteenCoordinates<0 at h
    linarith
  rw [thirteen_lag_source]
  exact (mul_pos normalizationFactor_pos hp).le

end polyak.CertifiedExamples.Rational
