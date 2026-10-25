import polyak.Certificates.P2SlacksData01
import polyak.Boundary.P2.Bounds

/-! Article: exact three active primal constraints of P₂, in the actual spectral measure. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: the three active raw constraints of P₂ vanish exactly. -/
theorem active_constraints {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) :
    meanA (spectrum z hz h1) (u z) t 1-meanB (spectrum z hz h1) (u z) 1+
      (d z/Real.sinh t)*Real.sinh (1*t)=0 ∧
    meanA (spectrum z hz h1) (u z) t 2+meanB (spectrum z hz h1) (u z) 2-
      (d z/Real.sinh t)*Real.sinh (2*t)=0 ∧
    meanA (spectrum z hz h1) (u z) t 3+meanB (spectrum z hz h1) (u z) 3-
      (d z/Real.sinh t)*Real.sinh (3*t)=0 := by
  have hs := Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht)
  have hL:=actual_reducedSlack hz h1 ht hs 1 (by omega) (-1)
  have hU2:=actual_reducedSlack hz h1 ht hs 2 (by omega) 1
  have hU3:=actual_reducedSlack hz h1 ht hs 3 (by omega) 1
  rw [lower1_zero hz] at hL
  rw [upper2_zero hz] at hU2
  rw [upper3_zero hz] at hU3
  norm_num only [neg_one_mul,one_mul,Nat.cast_ofNat] at hL hU2 hU3
  exact ⟨by simpa only [one_mul,neg_mul,sub_neg_eq_add,sub_eq_add_neg,neg_neg] using hL,hU2,hU3⟩


end
end polyak.Boundary.P2
