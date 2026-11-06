import nesterov.Corner.Lower
import nesterov.Corner.Upper
import nesterov.Layer.ResultsRates

/-! Both bounds in the source corner theorem concern the actual full and
from-rest rates. Equality is asserted only when the two proved bounds agree. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology

private theorem le_liminf_of_real_bounds {A : Type*} {l : Filter A}
    {f : A→ℝ} {b : ℝ} (h : ∀ c : ℝ,c<b → ∀ᶠ a in l,c≤f a) :
    (b:EReal)≤liminf (fun a=>(f a:EReal)) l := by
  by_contra hn
  obtain ⟨c,hlim,hcb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have he : ∀ᶠ a in l,(c:EReal)≤(f a:EReal) := by
    filter_upwards [h c (EReal.coe_lt_coe_iff.mp hcb)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha
  exact (not_lt_of_ge (Filter.le_liminf_of_le (by isBoundedDefault) he)) hlim

private theorem limsup_le_of_real_bounds {A : Type*} {l : Filter A}
    {f : A→ℝ} {b : ℝ} (h : ∀ c : ℝ,b<c → ∀ᶠ a in l,f a≤c) :
    limsup (fun a=>(f a:EReal)) l≤(b:EReal) := by
  by_contra hn
  obtain ⟨c,hbc,hlim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have he : ∀ᶠ a in l,(f a:EReal)≤(c:EReal) := by
    filter_upwards [h c (EReal.coe_lt_coe_iff.mp hbc)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) he)) hlim

variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

/-- The lower witnesses bound both upper limiting coefficients throughout the
stable corner regime, including a nonpositive lag-one minimum. -/
theorem corner_coefficient_limsup_upper [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) :
    limsup (fun p=>(F.fullCoefficientAt p:EReal)) l≤
        (max 0 (min (Flow.cQ θ 2) (Corner.cDisc θ a b)):EReal) ∧
      limsup (fun p=>(F.restCoefficientAt p:EReal)) l≤
        (max 0 (min (Flow.cQ θ 2) (Corner.cDisc θ a b)):EReal) := by
  have hupper (c : ℝ) (hc : max 0 (min (Flow.cQ θ 2) (Corner.cDisc θ a b))<c) :
      ∀ᶠ p in l,F.fullCoefficientAt p≤c ∧ F.restCoefficientAt p≤c := by
    filter_upwards [F.corner_rest_lower ha hb hmargin hc,F.epsilon_pos,
      F.layer_coefficients_order] with p hp he hord
    have hr : F.restCoefficientAt p<c := (div_lt_iff₀ he).mpr (by
      change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
        (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<c*F.epsilon p
      linarith)
    exact ⟨(hord.trans_lt hr).le,hr.le⟩
  exact ⟨limsup_le_of_real_bounds (fun c hc=>(hupper c hc).mono fun _ h=>h.1),
    limsup_le_of_real_bounds (fun c hc=>(hupper c hc).mono fun _ h=>h.2)⟩

theorem corner_coefficients_lower {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hLag : 0<Corner.cLag θ a b) (hc : c<min (Flow.cQ θ 2) (Corner.cLag θ a b)) :
    ∀ᶠ p in l,c<F.fullCoefficientAt p ∧ c<F.restCoefficientAt p := by
  have hm : 0<min (Flow.cQ θ 2) (Corner.cLag θ a b) :=
    lt_min (Flow.cQ_pos F.theta_pos (by norm_num)) hLag
  obtain ⟨d,hcd,hd⟩ := exists_between (max_lt hc hm)
  have hd0 : 0<d := (le_max_right c 0).trans_lt hcd
  have hdc : c<d := (le_max_left c 0).trans_lt hcd
  filter_upwards [F.corner_lagOne_upper ha hb hd0 hd,F.epsilon_pos,F.layer_coefficients_order]
    with p hp he hord
  have hf : d<F.fullCoefficientAt p := (lt_div_iff₀ he).mpr (by
    change d*F.epsilon p<1-Momentum.momentumRate (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1
    linarith)
  exact ⟨hdc.trans hf,(hdc.trans hf).trans_le hord⟩

theorem corner_coefficients_upper [l.IsCountablyGenerated] {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b)
    (hc : min (Flow.cQ θ 2) (Corner.cDisc θ a b)<c) :
    ∀ᶠ p in l,F.fullCoefficientAt p<c ∧ F.restCoefficientAt p<c := by
  have hm : 0<min (Flow.cQ θ 2) (Corner.cDisc θ a b) :=
    lt_min (Flow.cQ_pos F.theta_pos (by norm_num))
      (hLag.trans_le (Corner.cLag_le_cDisc θ a b))
  have hbound := F.corner_rest_lower ha hb hmargin
    (by rwa [max_eq_right hm.le])
  filter_upwards [hbound,F.epsilon_pos,F.layer_coefficients_order] with p hp he hord
  have hr : F.restCoefficientAt p<c := (div_lt_iff₀ he).mpr (by
    change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<c*F.epsilon p
    linarith)
  exact ⟨hord.trans_lt hr,hr⟩

theorem corner_coefficient_bounds [l.IsCountablyGenerated] [NeBot l] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b) :
    (min (Flow.cQ θ 2) (Corner.cLag θ a b):EReal)≤
      liminf (fun p=>(F.fullCoefficientAt p:EReal)) l ∧
    liminf (fun p=>(F.fullCoefficientAt p:EReal)) l≤
      limsup (fun p=>(F.restCoefficientAt p:EReal)) l ∧
    limsup (fun p=>(F.restCoefficientAt p:EReal)) l≤
      (min (Flow.cQ θ 2) (Corner.cDisc θ a b):EReal) := by
  refine ⟨le_liminf_of_real_bounds (fun c hc=>?_),?_,
    limsup_le_of_real_bounds (fun c hc=>?_)⟩
  · exact (F.corner_coefficients_lower ha hb hLag hc).mono fun _ h=>h.1.le
  · have hord : ∀ᶠ p in l,(F.fullCoefficientAt p:EReal)≤(F.restCoefficientAt p:EReal) :=
      F.layer_coefficients_order.mono fun _ h=>EReal.coe_le_coe_iff.mpr h
    exact (Filter.liminf_le_liminf hord).trans (Filter.liminf_le_limsup)
  · exact (F.corner_coefficients_upper ha hb hmargin hLag hc).mono fun _ h=>h.2.le

theorem corner_coefficients_tendsto [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b)
    (heq : min (Flow.cQ θ 2) (Corner.cLag θ a b)=
      min (Flow.cQ θ 2) (Corner.cDisc θ a b)) :
    Tendsto F.fullCoefficientAt l (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) ∧
      Tendsto F.restCoefficientAt l (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) := by
  have hlo (c : ℝ) (hc : c<min (Flow.cQ θ 2) (Corner.cLag θ a b)) :=
    F.corner_coefficients_lower ha hb hLag hc
  have hhi (c : ℝ) (hc : min (Flow.cQ θ 2) (Corner.cLag θ a b)<c) :=
    F.corner_coefficients_upper ha hb hmargin hLag (by rwa [←heq])
  exact ⟨tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.1,
      fun c hc=>(hhi c hc).mono fun _ h=>h.1⟩,
    tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.2,
      fun c hc=>(hhi c hc).mono fun _ h=>h.2⟩⟩

end
end nesterov.TwoStep.Scaling
