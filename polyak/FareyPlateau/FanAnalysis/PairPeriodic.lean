import polyak.FareyPlateau.FanAnalysis.PairAsymptotic

/-! The attained restricted pair threshold supplies an actual periodic
program of the fan order. No feasibility or grid hypotheses are assumed
in the final large-fan wrapper. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels MeasureTheory Set

theorem pairThreshold_ge_periodic (q : Tuning) (a c : Frequency) {L : ℕ} (hL : 3≤L)
    (ha : a∈periodicGrid L) (hc : c∈periodicGrid L)
    (hn : (pairFeasibleShifts q a c).Nonempty) : Threshold.sigmaPeriodic q L≤pairThreshold q a c := by
  apply (Threshold.shifted_periodic_iff q hL _).mp
  obtain ⟨μ,hμ,hcar⟩ := pairThreshold_attained q a c hn
  refine ⟨μ,hμ,hcar.mono ?_⟩
  intro x hx
  rcases hx with rfl|rfl
  · exact ha
  · exact hc

namespace FanData
variable (P : Fan.Data)

theorem L_pos : 0<P.L := by have := P.period_ge; have := P.order_gt; omega

theorem numerators_pos (hj : 0<P.j) : 0<P.J ∧ 0<P.J+P.sign := by
  have hkj : 0<P.k := by have := P.period_ge; omega
  have hjL : P.L≤P.j*P.L := by nlinarith [(L_pos P)]
  have hsign : -1≤P.sign ∧ P.sign≤1 := by rcases P.sign_unit with h|h <;> omega
  have hterm : -(P.k-1)≤P.sign*(P.k-1) := by
    have hh := mul_le_mul_of_nonneg_right hsign.1 (show 0≤P.k-1 by have := P.period_ge; omega)
    nlinarith only [hh]
  constructor
  · nlinarith [P.incidence,P.order_gt,P.period_ge]
  · nlinarith [P.incidence,P.order_gt]

theorem L_nat_ge : 3≤P.L.toNat := by
  have hh : ((P.L.toNat:ℕ):ℤ)=P.L := Int.toNat_of_nonneg (L_pos P).le
  have hn : (3:ℤ)≤(P.L.toNat:ℕ) := by rw [hh]; have := P.period_ge; have := P.order_gt; omega
  exact_mod_cast hn

theorem near_grid (hj : 0<P.j) (a : Frequency) (ha : (a:ℝ)=P.near) : a∈periodicGrid P.L.toNat := by
  have hLn : ((P.L.toNat:ℕ):ℤ)=P.L := Int.toNat_of_nonneg (L_pos P).le
  have hLr : (P.L.toNat:ℝ)=(P.L:ℝ) := by exact_mod_cast hLn
  have hJ : (0:ℝ)<P.J := by exact_mod_cast (numerators_pos P hj).1
  have hL : (0:ℝ)<P.L := by exact_mod_cast (L_pos P)
  refine ⟨?_,P.J,?_⟩
  · rw [ha]
    unfold Fan.Data.near
    positivity
  · rw [ha,hLr]
    unfold Fan.Data.near
    field_simp

theorem far_grid (hj : 0<P.j) (c : Frequency) (hc : (c:ℝ)=P.far) : c∈periodicGrid P.L.toNat := by
  have hLn : ((P.L.toNat:ℕ):ℤ)=P.L := Int.toNat_of_nonneg (L_pos P).le
  have hLr : (P.L.toNat:ℝ)=(P.L:ℝ) := by exact_mod_cast hLn
  have hJ : (0:ℝ)<(P.J+P.sign:ℤ) := by exact_mod_cast (numerators_pos P hj).2
  have hL : (0:ℝ)<P.L := by exact_mod_cast (L_pos P)
  refine ⟨?_,P.J+P.sign,?_⟩
  · rw [hc]
    unfold Fan.Data.far
    push_cast at hJ
    positivity
  · rw [hc,hLr]
    unfold Fan.Data.far
    push_cast
    field_simp

end FanData

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

include A

theorem fan_pair_threshold_ge_periodic :
    ∃L₀ : ℕ, ∀P : Fan.Data,P.j=j → P.k=k → (L₀:ℤ)≤P.L →
      ∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
        Threshold.sigmaPeriodic q P.L.toNat≤pairThreshold q a c := by
  obtain ⟨L₀,hL₀⟩ := fan_feasible A (show critical A-1<critical A by linarith)
  refine ⟨L₀,fun P hj hk hPL a c ha hc=>?_⟩
  obtain ⟨a',c',ha',hc',hsol⟩ := hL₀ P hj hk hPL
  have hae : a'=a := Subtype.ext (ha'.trans ha.symm)
  have hce : c'=c := Subtype.ext (hc'.trans hc.symm)
  subst a'
  subst c'
  have hFP : pairFP (Geometry.shiftedCurve q (A.edgeShift-(critical A-1)*P.delta^2)) a c := by
    refine ⟨_,hsol,?_⟩
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    fin_cases i <;> simp [pairCarrier]
  have hjpos : 0<P.j := by rw [hj]; exact_mod_cast (show 0<j by have := A.numerator_pos; omega)
  exact pairThreshold_ge_periodic q a c (FanData.L_nat_ge P)
    (FanData.near_grid P hjpos a ha) (FanData.far_grid P hjpos c hc) ⟨_,hFP⟩

end Actual
end polyak.FareyPlateau.FanAnalysis
