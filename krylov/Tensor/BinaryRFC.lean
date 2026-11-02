import krylov.Tensor.BinaryMixed

/-!
Article: main_krylov, apD:lem-binary(d) and thm:Fplanar.
Use: take the genuine supremum over the entire original binary cubic ball,
including an actual harmonic lower attainer, and obtain the printed C_Y
bounds. Source: the proved sharp coefficient disks and Banach identity.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- All true normalized RFC-F objective values over the full binary cubic ball.
Article: main_krylov, apD:lem-binary(d). -/
def rfcValues (r : ℝ) : Set ℝ :=
  {v | ∃ t : BinaryCubic, t.InBall ∧ v=rfcObjective r t}

/-- The real worst-case coefficient, with the full original tensor ball.
Article: main_krylov, apD:lem-binary(d). -/
def rfcWorst (r : ℝ) : ℝ := sSup (rfcValues r)

/-- The actual harmonic tensor gives the printed value two in the original
supremum domain. Article: main_krylov, apD:lem-binary(d). -/
theorem two_mem_rfcValues (r : ℝ) : 2∈rfcValues r :=
  ⟨harmonicSine,harmonicSine_inBall,(harmonicSine_rfcObjective r).symm⟩

/-- The full objective-value set is bounded by the printed sharp upper envelope.
Article: main_krylov, apD:lem-binary(d). -/
theorem rfcValues_bddAbove (r : ℝ) : BddAbove (rfcValues r) := by
  refine ⟨2*Real.sqrt (1+r^2),?_⟩
  rintro v ⟨t,ht,rfl⟩
  exact rfcObjective_le ht r

/-- The true supremum obeys both printed bounds and has an actual tensor
attaining the lower comparison value, for every real parameter.
Article: main_krylov, apD:lem-binary(d). -/
theorem rfcWorst_bounds (r : ℝ) : 2≤rfcWorst r ∧ rfcWorst r≤2*Real.sqrt (1+r^2) := by
  constructor
  · exact le_csSup (rfcValues_bddAbove r) (two_mem_rfcValues r)
  · apply csSup_le ⟨2,two_mem_rfcValues r⟩
    rintro v ⟨t,ht,rfl⟩
    exact rfcObjective_le ht r

/-- The genuine function-value RFC planar leading coefficient C_Y.
Article: main_krylov, thm:Fplanar, the model-metric split. -/
def modelMetricCoefficient (r : ℝ) : ℝ := r*rfcWorst r

/-- The actual RFC-F coefficient has precisely the printed two-sided bounds.
Article: main_krylov, thm:Fplanar, 2r≤C_Y(r)≤2r sqrt(1+r²). -/
theorem modelMetricCoefficient_bounds {r : ℝ} (hr : 0≤r) :
    2*r≤modelMetricCoefficient r ∧ modelMetricCoefficient r≤2*r*Real.sqrt (1+r^2) := by
  obtain ⟨hlo,hhi⟩ := rfcWorst_bounds r
  constructor
  · simpa only [modelMetricCoefficient,mul_comm r 2] using mul_le_mul_of_nonneg_left hlo hr
  · have h := mul_le_mul_of_nonneg_left hhi hr
    unfold modelMetricCoefficient
    nlinarith

/-- The harmonic lower comparison is attained by the actual sine tensor.
Article: main_krylov, thm:Fplanar and apD:lem-binary(d). -/
theorem harmonicSine_modelMetric_value (r : ℝ) : r*rfcObjective r harmonicSine=2*r := by
  rw [harmonicSine_rfcObjective,mul_comm]

end
end krylov.Tensor.BinaryCubic
