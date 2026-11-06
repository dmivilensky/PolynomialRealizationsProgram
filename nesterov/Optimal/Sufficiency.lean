import nesterov.Optimal.NearCorner
import nesterov.Optimal.Minimum
import nesterov.Layer.ResultsRates

/-! Sufficiency of the minimum-ratio condition for the actual full and rest
rates, with no boundedness assumptions on the corner coordinates. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem optimal_lagOne_upper {c : ℝ} (hc0 : 0<c) (hc1 : c<1)
    (hmin : Tendsto F.cornerLagAt l (𝓝 1)) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hQ : Flow.cQ 3 2=1 := by norm_num [Flow.cQ]
  have hcompact : IsCompact ({c}×ˢIcc (0:ℝ) 2) := isCompact_singleton.prod isCompact_Icc
  have herr := Metric.tendstoUniformlyOn_iff.mp (F.near_tail_error_uniform hcompact)
    (1-c) (sub_pos.mpr hc1)
  have hl := hmin.eventually (eventually_gt_nhds (show (1+c)/2<1 by linarith))
  have htail : ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ := by
    filter_upwards [F.near_tail_exact c,F.epsilon_pos,herr,hl] with a hex he herr hl ξ hξ
    have hr : (1+c)/2<F.cornerRatioAt a ξ := hl.trans_le (F.cornerLagAt_le a hξ)
    have hd : 0<4*(3-ξ) := by linarith [hξ.2]
    have hn : 2*(1-c)<F.cornerNAt a ξ-4*c*(3-ξ) := by
      have hh := (lt_div_iff₀ hd).mp hr
      have hden : 4≤4*(3-ξ) := by linarith [hξ.2]
      have hprod := mul_le_mul_of_nonneg_right hden (sub_pos.mpr hc1).le
      unfold cornerRatioAt at hr
      nlinarith
    have he' : |F.nearTailError c ξ a|<1-c := by
      have hh := herr (c,ξ) ⟨by simp,hξ⟩
      simpa only [Real.dist_eq,zero_sub,abs_neg] using hh
    rw [hex ξ]
    apply mul_pos he
    linarith [(abs_lt.mp he').1]
  exact (F.lag_scaled hc0 (by rwa [hQ]) htail).mono fun _ h=>h.2.2

 theorem optimal_coefficients_tendsto [l.IsCountablyGenerated]
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hmin : Tendsto F.cornerLagAt l (𝓝 1)) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ∧ Tendsto F.restCoefficientAt l (𝓝 1) := by
  have hlo (c : ℝ) (hc : c<1) :
      ∀ᶠ a in l,c<F.fullCoefficientAt a ∧ c<F.restCoefficientAt a := by
    obtain ⟨d,hdc,hd⟩ := exists_between (max_lt (show c<1 from hc) (by norm_num : (0:ℝ)<1))
    have hd0 : 0<d := (le_max_right c 0).trans_lt hdc
    have hcd : c<d := (le_max_left c 0).trans_lt hdc
    filter_upwards [F.optimal_lagOne_upper hd0 hd hmin,F.epsilon_pos,F.layer_coefficients_order]
      with a ha he hord
    have hf : d<F.fullCoefficientAt a := (lt_div_iff₀ he).mpr (by
      change d*F.epsilon a<1-Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1
      linarith)
    exact ⟨hcd.trans hf,hcd.trans (hf.trans_le hord)⟩
  have hhi (b : ℝ) (hb : 1<b) :
      ∀ᶠ a in l,F.fullCoefficientAt a<b ∧ F.restCoefficientAt a<b := by
    obtain ⟨d,hd,hdb⟩ := exists_between hb
    have hF : Flow.cF 3 2=1 := by norm_num [Flow.cF,Flow.cQ]
    filter_upwards [F.rest_coefficient_eventually_le_filter hstable (by rwa [hF]),
      F.layer_coefficients_order] with a ha hord
    exact ⟨(hord.trans ha).trans_lt hdb,ha.trans_lt hdb⟩
  exact ⟨tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.1,
      fun b hb=>(hhi b hb).mono fun _ h=>h.1⟩,
    tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.2,
      fun b hb=>(hhi b hb).mono fun _ h=>h.2⟩⟩

end
end nesterov.TwoStep.Scaling
