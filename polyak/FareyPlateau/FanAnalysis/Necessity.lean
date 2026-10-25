import polyak.FareyPlateau.FanAnalysis.NecessityCore
import polyak.FareyPlateau.FanAnalysis.CarriedPair
import polyak.FareyPlateau.FanAnalysis.Cutoff

/-! The necessary half of the fan theorem for arbitrary nonzero finite
measures carried by the two actual fan frequencies. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Filter MeasureTheory Set
open scoped Topology
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem fan_no_measure_small {e : ℝ} (he : critical A < e) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀P : Fan.Data, P.j=j → P.k=k → P.delta=δ →
      ∀a c : Frequency, (a : ℝ)=P.near → (c : ℝ)=P.far →
      ¬∃μ : Measure Frequency,
        ProgramSolution (Geometry.shiftedCurve q (A.edgeShift-e*δ^2)) nonzeroLags μ ∧
          (∀ᵐ x ∂μ, x=a ∨ x=c) := by
  have ha := anglePath_actual q A.edgeShift A.frequency 1 e (frequency_interior A)
  have hc := anglePath_actual q A.edgeShift A.frequency (-((k : ℝ)-1)) e (frequency_interior A)
  filter_upwards [fan_infeasible_small A he, ha.filter_mono nhdsWithin_le_nhds,
    hc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with δ hsep hanglea hanglec hz P hj hk hδ a c haP hcP hμ
  have hcenter : P.center=(A.frequency : ℝ) := by
    change 2*Real.pi*P.j/P.k=2*Real.pi*j/k
    rw [hj,hk]
    push_cast
    rfl
  have hnear : P.near=(A.frequency : ℝ)+δ := by
    have hh := P.near_displacement
    rw [hcenter,hδ] at hh
    linarith
  have hfar : P.far=(A.frequency : ℝ)-((k : ℝ)-1)*δ := by
    have hh := P.far_displacement
    rw [hcenter,hδ,hk] at hh
    push_cast at hh
    exact hh
  have hneq : a ≠ c := by
    intro heq
    have hh := congrArg (fun x : Frequency => (x : ℝ)) heq
    rw [haP,hcP,hnear,hfar] at hh
    have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
    have hprod : (k : ℝ)*δ=0 := by nlinarith
    exact hz ((mul_eq_zero.mp hprod).resolve_left hkpos.ne')
  have hca : Geometry.shiftedCurve q (A.edgeShift-e*δ^2) a=nearAngle A e δ := by
    change Geometry.shiftedAngle q _ (a : ℝ)=_
    rw [haP,hnear]
    simpa only [one_mul, nearAngle] using hanglea.symm
  have hcc : Geometry.shiftedCurve q (A.edgeShift-e*δ^2) c=farAngle A e δ := by
    change Geometry.shiftedAngle q _ (c : ℝ)=_
    rw [hcP,hfar]
    change Geometry.shiftedAngle q _ ((A.frequency : ℝ)-((k : ℝ)-1)*δ)=
      anglePath q A.edgeShift A.frequency (-((k : ℝ)-1)) e δ
    convert hanglec.symm using 1; congr 1; ring
  obtain ⟨μ,hprog,hcar⟩ := hμ
  have hm := pair_solution_inequalities hneq hcar hprog
  let wa : ℝ := pairWeight μ a c 0
  let wc : ℝ := pairWeight μ a c 1
  have hsum : 0<wa+wc := by
    have hh := hm.1
    simp only [Fin.sum_univ_two] at hh
    exact_mod_cast hh
  apply hsep P hj hk hδ wa wc (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hsum
  intro n
  have hh := hm.2.2 n
  simpa only [Curve.lag,hca,hcc,haP,hcP,pairLag] using hh

theorem fan_no_measure {e : ℝ} (he : critical A < e) :
    ∃L₀ : ℕ, ∀P : Fan.Data, P.j=j → P.k=k → (L₀ : ℤ)≤P.L →
      ∀a c : Frequency, (a : ℝ)=P.near → (c : ℝ)=P.far →
      ¬∃μ : Measure Frequency,
        ProgramSolution (Geometry.shiftedCurve q (A.edgeShift-e*P.delta^2)) nonzeroLags μ ∧
          (∀ᵐ x ∂μ, x=a ∨ x=c) := by
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta A.period_ge (fan_no_measure_small A he)
  exact ⟨L₀,fun P hj hk hPL => hL₀ P hk hPL P hj hk rfl⟩

end polyak.FareyPlateau.FanAnalysis.Actual
