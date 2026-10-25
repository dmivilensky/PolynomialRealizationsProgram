import LeanCert.Core.IntervalRat.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact algebraic square-root enclosures verified by rational square comparisons. -/
namespace polyak.Numerics
open LeanCert.Core

def sqrtIntervalCheck (A B : IntervalRat) : Bool :=
  decide (0≤B.lo ∧ B.lo^2≤A.lo ∧ A.hi≤B.hi^2)

noncomputable section

theorem sqrtIntervalCheck_sound {A B : IntervalRat} (hc : sqrtIntervalCheck A B=true)
    {x : ℝ} (hx : x∈A) : Real.sqrt x∈B := by
  simp only [sqrtIntervalCheck,decide_eq_true_eq] at hc
  have hlo : (0 : ℝ)≤B.lo := by exact_mod_cast hc.1
  have hll : (B.lo : ℝ)^2≤A.lo := by exact_mod_cast hc.2.1
  have hhh : (A.hi : ℝ)≤(B.hi : ℝ)^2 := by exact_mod_cast hc.2.2
  have hbb : (B.lo : ℝ)≤B.hi := by exact_mod_cast B.le
  have hx0 : 0≤x := by nlinarith [hx.1,sq_nonneg (B.lo : ℝ)]
  have hs := Real.sq_sqrt hx0
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1,hx.2]

end
end polyak.Numerics
