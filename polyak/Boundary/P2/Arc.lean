import polyak.Certificates.P2Slacks
import polyak.Boundary.P2.Active

/-!
Article: Theorem p2arc, feasibility and exact primal–dual optimality on the full closed arc.
Use: finite checked source slacks and one proved analytic tail cover every lag.
Both signs of the exponent are included through C=d/sinh t.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: every parameter of the closed P₂ arc lies in the common certificate interval. -/
theorem arc_mem_interval {z : ℝ} (hz : z∈Set.Icc zeta1 zetaA) : z∈parameterInterval := by
  constructor <;> linarith [hz.1,hz.2,zeta1_bounds.1,zetaA_bounds.2]

/-- Article: exact nonnegative upper lag-five source up to its endpoint. -/
theorem upper5_nonneg {z : ℝ} (hz : z∈parameterInterval) (ha : z ≤ zetaA) :
    0 ≤ reducedSlack z 5 1 := by
  rw [upper5_factor hz]
  exact mul_nonneg (N12_nonneg hz ha) (upper_five_factor_positive z hz).le

/-- Article: all eighteen finite raw source constraints of orders one through nine. -/
theorem prefix_source_nonneg {z : ℝ} (hz : z∈parameterInterval) (ha : z ≤ zetaA)
    (n : ℕ) (hn : 1 ≤ n) (hn9 : n ≤ 9) :
    0 ≤ reducedSlack z n (-1) ∧ 0 ≤ reducedSlack z n 1 := by
  interval_cases n
  · exact ⟨(lower1_zero hz).ge,(upper1_positive z hz).le⟩
  · exact ⟨(lower2_positive z hz).le,(upper2_zero hz).ge⟩
  · exact ⟨(lower3_positive z hz).le,(upper3_zero hz).ge⟩
  · exact ⟨(lower4_positive z hz).le,(upper4_positive z hz).le⟩
  · exact ⟨(lower5_positive z hz).le,upper5_nonneg hz ha⟩
  · exact ⟨(lower6_positive z hz).le,(upper6_positive z hz).le⟩
  · exact ⟨(lower7_positive z hz).le,(upper7_positive z hz).le⟩
  · exact ⟨(lower8_positive z hz).le,(upper8_positive z hz).le⟩
  · exact ⟨(lower9_positive z hz).le,(upper9_positive z hz).le⟩

/-- Article: the full source P₂ probability measure is feasible for all positive lags. -/
theorem feasibleU {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) (ha : z ≤ zetaA)
    (ht : Real.cosh t=G z) : FeasibleU (u z) t (spectrum z hz h1) (d z/Real.sinh t) := by
  have hgap := minimizer_gap hz h1 ht
  refine ⟨by linarith,fun n hn => ?_⟩
  by_cases h9 : n ≤ 9
  · have hsource := prefix_source_nonneg hz ha n hn h9
    have hs := Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht)
    have hl := actual_reducedSlack hz h1 ht hs n hn (-1)
    have hu := actual_reducedSlack hz h1 ht hs n hn 1
    constructor <;> nlinarith [hsource.1,hsource.2,hl,hu]
  · have htail := infinite_tail_positive hz h1 ht n (by omega)
    constructor <;> linarith [htail.1,htail.2]

/-- Article: the exact spectral boundary on the complete rational P₂ arc. -/
theorem optimal {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) (ha : z ≤ zetaA)
    (ht : Real.cosh t=G z) : V t=Real.arsinh (u z) := by
  apply primal_dual_optimal (dualWeights z hz)
  · have hu := u_lower_positive z hz
    linarith
  · exact feasibleU hz h1 ha ht
  · intro c
    rw [ht]
    exact dualPolynomial_nonneg hz c

/-- Article: upper lag five is strictly inactive before the P₅ endpoint. -/
theorem upper5_strict_before {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ha : z < zetaA) (ht : Real.cosh t=G z) :
    0 < meanA (spectrum z hz h1) (u z) t 5+meanB (spectrum z hz h1) (u z) 5-
      (d z/Real.sinh t)*Real.sinh (5*t) := by
  have hs := Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht)
  have he := actual_reducedSlack hz h1 ht hs 5 (by omega) 1
  have hpos : 0 < reducedSlack z 5 1 := by
    rw [upper5_factor hz]
    exact mul_pos (N12_positive hz ha) (upper_five_factor_positive z hz)
  norm_num only [one_mul,Nat.cast_ofNat] at he
  linarith

/-- Article: upper lag five becomes exactly active at the endpoint ζₐ. -/
theorem upper5_endpoint {t : ℝ} (ht : Real.cosh t=G zetaA) :
    meanA (spectrum zetaA zetaA_mem zeta1_lt_zetaA.le) (u zetaA) t 5+
      meanB (spectrum zetaA zetaA_mem zeta1_lt_zetaA.le) (u zetaA) 5-
      (d zetaA/Real.sinh t)*Real.sinh (5*t)=0 := by
  have hs := Real.sinh_ne_zero.mpr (exponent_ne_zero zetaA_mem ht)
  have he := actual_reducedSlack zetaA_mem zeta1_lt_zetaA.le ht hs 5 (by omega) 1
  rw [upper5_factor zetaA_mem,N12_zetaA,zero_mul] at he
  simpa only [one_mul,Nat.cast_ofNat] using he

/-- Article: every lower raw slack other than the active lag one is strictly positive. -/
theorem lower_strict {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) (n : ℕ) (hn : 2 ≤ n) :
    0<meanA (spectrum z hz h1) (u z) t n-meanB (spectrum z hz h1) (u z) n+
      (d z/Real.sinh t)*Real.sinh (n*t) := by
  by_cases hn9 : n ≤ 9
  · have hpos : 0<reducedSlack z n (-1) := by
      interval_cases n
      · exact lower2_positive z hz
      · exact lower3_positive z hz
      · exact lower4_positive z hz
      · exact lower5_positive z hz
      · exact lower6_positive z hz
      · exact lower7_positive z hz
      · exact lower8_positive z hz
      · exact lower9_positive z hz
    have h:=actual_reducedSlack hz h1 ht
      (Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht)) n (by omega) (-1)
    norm_num only [neg_one_mul] at h
    linarith
  · have h:=infinite_tail_positive hz h1 ht n (by omega)
    linarith [h.1]

/-- Article: every upper raw slack other than lags two, three and five is strictly positive. -/
theorem upper_strict {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) (n : ℕ) (hn : 1 ≤ n) (h2 : n≠2) (h3 : n≠3) (h5 : n≠5) :
    0<meanA (spectrum z hz h1) (u z) t n+meanB (spectrum z hz h1) (u z) n-
      (d z/Real.sinh t)*Real.sinh (n*t) := by
  by_cases hn9 : n ≤ 9
  · have hpos : 0<reducedSlack z n 1 := by
      interval_cases n
      · exact upper1_positive z hz
      · exact (h2 rfl).elim
      · exact (h3 rfl).elim
      · exact upper4_positive z hz
      · exact (h5 rfl).elim
      · exact upper6_positive z hz
      · exact upper7_positive z hz
      · exact upper8_positive z hz
      · exact upper9_positive z hz
    have h:=actual_reducedSlack hz h1 ht
      (Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht)) n hn 1
    norm_num only [one_mul] at h
    linarith
  · have h:=infinite_tail_positive hz h1 ht n (by omega)
    linarith [h.2]

end
end polyak.Boundary.P2
