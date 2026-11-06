import nesterov.TwoStep.ScaledCoefficientsLimits
import nesterov.TwoStep.QuadraticAsymptotics
import nesterov.Phase.Separate

/-! Article: Lemma `lem:lagscaled`. Every rate bound concerns the actual
stationary method, with the slow root and positivity hypotheses derived exactly. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def scaledTail (ε c θ y τ ξ : ℝ) : ℝ :=
  scaledP1 ε c θ y τ+scaledP2 ε c θ y τ*ξ+scaledP3 ε c θ y τ*ξ^2

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem slow_test_tendsto (c : ℝ) :
    Tendsto (fun a=>Flow.delta (F.thetaAt a) (F.tuning a).stepSize c-
      (F.tuning a).stepSize*(1+(F.tuning a).tau)*c*F.epsilon a) l (𝓝 (Flow.delta θ y c)) := by
  have hc : Continuous (fun x : ℝ×ScaledParameters=>
      Flow.delta (x.2 1) (x.2 2) c-(x.2 2)*(1+x.2 3)*c*x.1) := by
    unfold Flow.delta
    fun_prop
  simpa [Function.comp_def,parametersAt,parametersLimit] using (hc.tendsto (0,parametersLimit c θ y τ)).comp
    (F.epsilon_zero.prodMk_nhds (F.parameters_tendsto c))

theorem determinant_test_tendsto (c : ℝ) :
    Tendsto (fun a=>F.thetaAt a-2*c+F.epsilon a*(c^2+(F.tuning a).stepSize*(F.tuning a).tau))
      l (𝓝 (θ-2*c)) := by
  have hc : Continuous (fun x : ℝ×ScaledParameters=>x.2 1-2*c+x.1*(c^2+x.2 2*x.2 3)) := by fun_prop
  simpa [Function.comp_def,parametersAt,parametersLimit] using (hc.tendsto (0,parametersLimit c θ y τ)).comp
    (F.epsilon_zero.prodMk_nhds (F.parameters_tendsto c))

theorem characteristic_at_radius_tendsto (c lam : ℝ) :
    Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize lam (1-c*F.epsilon a)) l (𝓝 (y*lam)) := by
  have hc : Continuous (fun x : ℝ×ScaledParameters=>
      realCharacteristic (1-x.2 1*x.1) (x.2 3) (x.2 2) lam (1-c*x.1)) := by
    unfold realCharacteristic Quadratic.S Quadratic.Q
    fun_prop
  have hh := (hc.tendsto (0,parametersLimit c θ y τ)).comp
    (F.epsilon_zero.prodMk_nhds (F.parameters_tendsto c))
  have he : realCharacteristic (1-(parametersLimit c θ y τ) 1*0) ((parametersLimit c θ y τ) 3)
      ((parametersLimit c θ y τ) 2) lam (1-c*0)=y*lam := by
    dsimp [parametersLimit,realCharacteristic,Quadratic.S,Quadratic.Q]
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [F.beta_eq] with a ha
  change realCharacteristic (1-F.thetaAt a*F.epsilon a) (F.tuning a).tau
    (F.tuning a).stepSize lam (1-c*F.epsilon a)=_
  rw [ha]

theorem slow_negative_radius_tendsto (c : ℝ) :
    Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) (-(1-c*F.epsilon a))) l (𝓝 4) := by
  have hc : Continuous (fun x : ℝ×ScaledParameters=>
      realCharacteristic (1-x.2 1*x.1) (x.2 3) (x.2 2) (x.1^2) (-(1-c*x.1))) := by
    unfold realCharacteristic Quadratic.S Quadratic.Q
    fun_prop
  have hh := (hc.tendsto (0,parametersLimit c θ y τ)).comp
    (F.epsilon_zero.prodMk_nhds (F.parameters_tendsto c))
  have he : realCharacteristic (1-(parametersLimit c θ y τ) 1*0) ((parametersLimit c θ y τ) 3)
      ((parametersLimit c θ y τ) 2) (0^2) (-(1-c*0))=4 := by
    norm_num [realCharacteristic,Quadratic.S,Quadratic.Q]
  rw [he] at hh
  exact hh.congr' (by
    filter_upwards [F.beta_eq] with a ha
    dsimp [parametersAt]
    rw [ha])

/-- The independent slow-root part of the source lemma. -/
theorem slow_endpoint_roots_lt {c : ℝ} (hc : c<Flow.cQ θ y) :
    ∀ᶠ a in l,∀ z : ℂ,Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) z=0 → ‖z‖<1-c*F.epsilon a := by
  obtain ⟨hhalf,hdelta⟩ := (Flow.lt_cQ_iff θ y c).mp hc
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [F.beta_eq,F.epsilon_pos,
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    (F.slow_test_tendsto c).eventually (eventually_gt_nhds hdelta),
    (F.determinant_test_tendsto c).eventually (eventually_gt_nhds (by linarith : 0<θ-2*c)),
    (F.slow_negative_radius_tendsto c).eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<4))]
      with a hβ he hrad hpos hdet hminus
  intro z hz
  apply (Quadratic.roots_lt_radius_iff hrad).mpr ?_ z (by rwa [←Quadratic.characteristic_eq])
  · refine ⟨?_,?_,?_⟩
    · rw [hβ]
      unfold Quadratic.Q
      nlinarith [mul_pos he hdet]
    · change 0<realCharacteristic (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.epsilon a^2) (1-c*F.epsilon a)
      rw [hβ,realCharacteristic_slow]
      exact mul_pos (sq_pos_of_pos he) hpos
    · simpa only [realCharacteristic,neg_sq,mul_neg,sub_neg_eq_add] using hminus

/-- P₀ is positive independently of every fast-frequency coefficient. -/
theorem P0_eventually_pos {c : ℝ} (hc0 : 0<c) (hc : c<Flow.cQ θ y) :
    ∀ᶠ a in l,0<scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau := by
  have hdelta := (Flow.lt_cQ_iff θ y c).mp hc |>.2
  have hy : Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (1-c*F.epsilon a)) l (𝓝 y) := by
    simpa only [mul_one] using F.characteristic_at_radius_tendsto c 1
  filter_upwards [F.epsilon_pos,F.beta_eq,(F.slow_test_tendsto c).eventually (eventually_gt_nhds hdelta),
    hy.eventually (eventually_gt_nhds F.step_pos)] with a he hβ hp hL
  rw [scaledP0_exact,realCharacteristic_slow]
  rw [hβ] at hL
  exact mul_pos (mul_pos (mul_pos hc0 he) (mul_pos (sq_pos_of_pos he) hp)) hL

theorem lag_scaled {c : ℝ} (hc0 : 0<c) (hc : c<Flow.cQ θ y)
    (hcoef : ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ) :
    ∀ᶠ a in l,Quadratic.quadraticRate (F.epsilon a^2) 1 (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize<1-c*F.epsilon a ∧
      IQC.middleRadius (Momentum.method (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne') (F.epsilon a^2) 1<1-c*F.epsilon a ∧
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [hcoef,F.P0_eventually_pos hc0 hc,F.slow_endpoint_roots_lt hc,F.beta_eq,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with a hcoef hp0 hslow hβ he he1 hr0
  have hp : ∀ z : ℂ,‖z‖=1-c*F.epsilon a →
      0<((1-z)*Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.epsilon a^2) z*star (Quadratic.characteristic (F.tuning a).beta
          (F.tuning a).tau (F.tuning a).stepSize 1 z)).re := by
    intro z hz
    have hez : circle (1-c*F.epsilon a) z.arg=z := by
      simpa [circle,polyak.Waves.z,hz] using Complex.norm_mul_exp_arg_mul_I z
    rw [←hez,Quadratic.characteristic_eq,Quadratic.characteristic_eq]
    change 0<((1-circle _ _)*quad _ _ (circle _ _)*star (quad _ _ (circle _ _))).re
    rw [lagOne_cubic,hβ]
    have hξ : 1-Real.cos z.arg∈Icc (0:ℝ) 2 :=
      ⟨by linarith [Real.cos_le_one z.arg],by linarith [Real.neg_one_le_cos z.arg]⟩
    have hh := mul_nonneg hξ.1 (hcoef _ hξ).le
    change 0<scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau+
      scaledP1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*(1-Real.cos z.arg)+
      scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*(1-Real.cos z.arg)^2+
      scaledP3 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*(1-Real.cos z.arg)^3
    unfold scaledTail at hh
    nlinarith only [hh,hp0]
  have hh := Phase.separate (F.tuning a) (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)
    ⟨hr0,by nlinarith [mul_pos hc0 he]⟩ hp hslow
  exact ⟨hh.1,hh.2.2.1,hh.2.2.2⟩

theorem P0_div_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/F.epsilon a) l (𝓝 0) := by
  have hslow := (F.epsilon_zero.pow 2).mul (F.slow_test_tendsto c)
  have hhigh := F.characteristic_at_radius_tendsto c 1
  have hh := (hslow.const_mul c).mul hhigh
  simp only [zero_pow (by omega : 2≠0),zero_mul,mul_zero] at hh
  apply hh.congr'
  filter_upwards [F.epsilon_pos,F.beta_eq] with a he hb
  rw [scaledP0_exact,realCharacteristic_slow]
  rw [hb]
  field_simp


theorem bulk_scaledTail_positive {c : ℝ} (hc : c<Flow.cF θ y)
    (hτ : 1/2<τ) (hmargin : y*(1+2*τ)<4) :
    ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ := by
  have hct : c<θ/3 := lt_of_lt_of_le hc (min_le_left _ _)
  have hp1 : 0<2*y*(θ-3*c) := mul_pos (mul_pos (by norm_num) F.step_pos) (by linarith)
  have hp2 : 0<2*y*(2*τ-1) := mul_pos (mul_pos (by norm_num) F.step_pos) (by linarith)
  have hend : Tendsto (fun a=>scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau+2*scaledP3 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau)
      l (𝓝 (2*(4-y*(1+2*τ)))) := by
    have hh := (F.P2_tendsto c).add ((tendsto_const_nhds (x:=(2:ℝ))).mul (F.P3_tendsto c))
    have he : 2*y*(2*τ-1)+2*(4*(1-τ*y))=2*(4-y*(1+2*τ)) := by ring
    rw [he] at hh
    exact hh
  filter_upwards [(F.P1_div_tendsto c).eventually (eventually_gt_nhds hp1),
    (F.P2_tendsto c).eventually (eventually_gt_nhds hp2),
    hend.eventually (eventually_gt_nhds (by linarith : 0<2*(4-y*(1+2*τ)))),F.epsilon_pos]
      with a h1 h2 hEnd he ξ hξ
  have h1p := (div_pos_iff_of_pos_right he).mp h1
  let p1 := scaledP1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau
  let p2 := scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau
  let p3 := scaledP3 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau
  have haff : 0≤p2+p3*ξ := by
    have hh : p2+p3*ξ=(1-ξ/2)*p2+(ξ/2)*(p2+2*p3) := by ring
    rw [hh]
    exact add_nonneg (mul_nonneg (by linarith [hξ.2]) h2.le)
      (mul_nonneg (by positivity [hξ.1]) hEnd.le)
  change 0<p1+p2*ξ+p3*ξ^2
  have hh := mul_nonneg hξ.1 haff
  change 0<p1 at h1p
  nlinarith only [hh,h1p]

/-- The bulk upper certificate in Theorem B, under its original strict hypotheses. -/
theorem bulk_lagOne_upper {c : ℝ} (hc0 : 0<c) (hc : c<Flow.cF θ y)
    (hτ : 1/2<τ) (hmargin : y*(1+2*τ)<4) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a :=
  (F.lag_scaled hc0 (lt_of_lt_of_le hc (min_le_right _ _))
    (F.bulk_scaledTail_positive hc hτ hmargin)).mono fun _ ha=>ha.2.2

end Scaling
end
end nesterov.TwoStep
