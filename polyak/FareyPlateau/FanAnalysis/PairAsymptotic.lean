import polyak.FareyPlateau.FanAnalysis.PairThreshold
import polyak.FareyPlateau.FanAnalysis.Necessity

/-! Literal epsilon form of the little-o(delta^2) pair-threshold expansion.
Both sufficiency and nonexistence concern arbitrary actual finite measures. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking MeasureTheory Set

theorem pairThreshold_error_bound (q : Tuning) (a c : Frequency) {s e η δ : ℝ}
    (hδ : δ≠0)
    (hupper : pairFP (Geometry.shiftedCurve q (s-(e-η)*δ^2)) a c)
    (hlower : ¬pairFP (Geometry.shiftedCurve q (s-(e+η)*δ^2)) a c) :
    |pairThreshold q a c-s+e*δ^2|≤η*δ^2 := by
  have hh := pairThreshold_squeeze q a c hδ hupper hlower
  have hp := mul_le_mul_of_nonneg_right hh (sq_nonneg δ)
  have he : |(pairThreshold q a c-s )/δ^2+e| * δ^2=
      |pairThreshold q a c-s+e*δ^2| := by
    calc
      _ = |((pairThreshold q a c-s)/δ^2+e)*δ^2| := by
        rw [abs_mul,abs_of_pos (sq_pos_of_ne_zero hδ)]
      _ = _ := by congr 1; field_simp
  rwa [he] at hp

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem fan_pair_threshold_asymptotic {η : ℝ} (hη : 0<η) :
    ∃L₀ : ℕ, ∀P : Fan.Data, P.j=j → P.k=k → (L₀:ℤ)≤P.L →
      ∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
        |pairThreshold q a c-A.edgeShift+critical A*P.delta^2|≤η*P.delta^2 := by
  obtain ⟨La,ha⟩ := fan_feasible A (show critical A-η<critical A by linarith)
  obtain ⟨Lb,hb⟩ := fan_no_measure A (show critical A<critical A+η by linarith)
  refine ⟨max La Lb,fun P hj hk hPL a c haP hcP=>?_⟩
  have hLa0 : (La:ℤ)≤(max La Lb:ℕ) := by exact_mod_cast le_max_left La Lb
  have hLa : (La:ℤ)≤P.L := hLa0.trans hPL
  have hLb0 : (Lb:ℤ)≤(max La Lb:ℕ) := by exact_mod_cast le_max_right La Lb
  have hLb : (Lb:ℤ)≤P.L := hLb0.trans hPL
  obtain ⟨a',c',ha',hc',hsol⟩ := ha P hj hk hLa
  have hae : a'=a := Subtype.ext (ha'.trans haP.symm)
  have hce : c'=c := Subtype.ext (hc'.trans hcP.symm)
  subst a'
  subst c'
  have hupper : pairFP (Geometry.shiftedCurve q (A.edgeShift-(critical A-η)*P.delta^2)) a c := by
    refine ⟨_,hsol,?_⟩
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    fin_cases i <;> simp [pairCarrier]
  have hlower : ¬pairFP (Geometry.shiftedCurve q (A.edgeShift-(critical A+η)*P.delta^2)) a c :=
    hb P hj hk hLb a c haP hcP
  have hδ : P.delta≠0 := by
    unfold Fan.Data.delta
    apply div_ne_zero
    · have hs : (P.sign:ℝ)≠0 := by rcases P.sign_unit with h|h <;> simp [h]
      exact mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℝ)≠0) Real.pi_ne_zero) hs
    · have hkp : (P.k:ℝ)≠0 := by exact_mod_cast (show P.k≠0 by have := P.period_ge; omega)
      have hLp : (P.L:ℝ)≠0 := by exact_mod_cast (show P.L≠0 by have := P.period_ge; have := P.order_gt; omega)
      exact mul_ne_zero hkp hLp
  exact pairThreshold_error_bound q a c hδ hupper hlower

end Actual
end polyak.FareyPlateau.FanAnalysis
