import nesterov.Corner.Expansion
import nesterov.Corner.Algebra
import nesterov.Corner.FixedBand
import nesterov.Corner.ProductBound
import nesterov.Layer.NegativeBandGeometry

/-! A strict dip at any fixed rational frequency produces a genuine
finite-dimensional from-rest witness through the all-lag spread theorem. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Phase
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_frequency_rest_witness {a b c : ℝ} {K : ℕ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hc0 : 0<c) (hc : c<θ/3) (hK : 3≤K)
    (hq : Corner.ratio θ a b (Corner.rationalXi K)<c) :
    ∀ᶠ p in l,∃ d : ℕ,
      RestLowerWitness (F.tuning p) (F.epsilon p^2) 1 (1-c*F.epsilon p) d ∧
      1-c*F.epsilon p≤Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
        (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1 := by
  let ω₀ : ℝ := nesterov.Spread.centerAngle K
  let P : ℝ→ℝ := fun ω=>(1-Real.cos ω)*
    (Corner.N θ a b (1-Real.cos ω)-4*c*(3-(1-Real.cos ω)))
  have hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3) :=
    ⟨nesterov.Spread.centerAngle_pos hK,nesterov.Spread.centerAngle_le hK⟩
  have hξp : 0<1-Real.cos ω₀ := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0)
      (show ω₀≤Real.pi by linarith [hω₀.2,Real.pi_pos]) hω₀.1
    simpa only [Real.cos_zero] using sub_pos.mpr hcos
  have hneg : P ω₀<0 := by
    have hN := (Corner.ratio_lt_iff (Corner.rationalXi_mem K).2).mp hq
    have hN' : Corner.N θ a b (1-Real.cos ω₀)-4*c*(3-(1-Real.cos ω₀))<0 := by
      change Corner.N θ a b (1-Real.cos ω₀)<4*c*(3-(1-Real.cos ω₀)) at hN
      linarith
    exact mul_neg_of_pos_of_neg hξp hN'
  obtain ⟨s,u,v,m,hs,hu,huv,hm,hlo,hhi,hP⟩ := Layer.negative_interval
    (by dsimp [P,Corner.N];fun_prop) hω₀.1 hneg nesterov.Spread.canonicalKernel.s1_pos
  have hs6 : s∈Ioc (0:ℝ) (1/6) := ⟨hs.1,hs.2.trans (min_le_right _ _)⟩
  have hband (ω : ℝ) (hω : ω∈Spread.band s ω₀) : P ω≤ -m := by
    have hlo' : (1-s)^2*ω₀≤(1-s)*ω₀ := by
      have hs01 : 0≤s ∧ s≤1 := ⟨hs.1.le,by linarith [hs6.2]⟩
      have hh : (1-s)^2≤1-s := by nlinarith
      exact mul_le_mul_of_nonneg_right hh hω₀.1.le
    have hhi' : (1+s)*ω₀≤(1+s)^2*ω₀ := by
      have hh : 1+s≤(1+s)^2 := by nlinarith [hs.1]
      exact mul_le_mul_of_nonneg_right hh hω₀.1.le
    exact hP ω ⟨hlo.le.trans (hlo'.trans hω.1),hω.2.trans (hhi'.trans hhi.le)⟩
  obtain ⟨X,hX,hprod⟩ := F.characteristic_product_bounded_on_compact c
    (isCompact_Icc (a:=(0:ℝ)) (b:=Real.pi))
  obtain ⟨M,hM,hmixed⟩ := Slow.uniformly_eventually_norm_bounded
    (isCompact_Icc (a:=(0:ℝ)) (b:=2)) (by unfold Corner.N;fun_prop)
    (F.corner_mixed_uniform c ha hb isCompact_Icc)
  have hcubic := Metric.tendstoUniformlyOn_iff.mp (F.corner_cubic_uniform c ha hb
    (isCompact_Icc (a:=(0:ℝ)) (b:=2))) (m/2) (by positivity)
  apply F.fixed_band_rest_witness (M:=M) (X:=X) (lam:=m/(2*X)) (K:=K) (s:=s)
    hc0 (by linarith [F.theta_pos] : c<θ/2)
    (by norm_num : (0:ℝ)<1/2) hs.1 (hs.2.trans (min_le_left _ _))
    (div_pos hm (by positivity : 0<2*X)) (F.corner_eventually_stable ha hb hmargin) hK
  · filter_upwards [hmixed,F.epsilon_pos,F.layerMixed_actual c] with p hp he hactual ω hω
    have hξ : 1-Real.cos ω∈Icc (0:ℝ) 2 :=
      ⟨sub_nonneg.mpr (Real.cos_le_one ω),by linarith [Real.neg_one_le_cos ω]⟩
    have hh := hp (1-Real.cos ω) hξ
    rw [Real.norm_eq_abs,abs_div,abs_of_pos he] at hh
    rw [hactual (1-Real.cos ω)]
    exact (div_le_iff₀ he).mp hh
  · filter_upwards [hprod] with p hp ω hω
    exact hp ω (let h := Spread.band_mem_Ioo hs6 hω₀ hω;⟨h.1.le,h.2.le⟩)
  · filter_upwards [hcubic,F.epsilon_pos,F.layerCubic_actual c] with p hp he hactual ω hω
    have hξ : 1-Real.cos ω∈Icc (0:ℝ) 2 :=
      ⟨sub_nonneg.mpr (Real.cos_le_one ω),by linarith [Real.neg_one_le_cos ω]⟩
    have hh := hp (1-Real.cos ω) hξ
    rw [Real.dist_eq] at hh
    have hPω := hband ω hω
    have hdiv : F.layerCubic c p (1-Real.cos ω)/F.epsilon p≤ -m/2 := by
      dsimp [P] at hPω
      linarith [(abs_lt.mp hh).1]
    rw [hactual ω]
    have hmε := (div_le_iff₀ he).mp hdiv
    have heq : -(m/(2*X))*F.epsilon p*X=(-m/2)*F.epsilon p := by
      field_simp [hX.ne']
    rw [heq]
    exact hmε

end
end nesterov.TwoStep.Scaling
