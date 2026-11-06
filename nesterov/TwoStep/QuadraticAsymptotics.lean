import nesterov.TwoStep.AsymptoticsModel
import nesterov.Quadratic.ScaledJury
import nesterov.Slow.RootSelection
import nesterov.Flow.QuadraticRates

/-! Lemma cq: actual quadratic asymptotics in the accelerated scaling.
The upper root bound uses affine dependence on curvature and the exact Jury test. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Polynomial
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem roots_eventually_lt_of_upper_endpoint {c : ℝ} (hc : c<Flow.cQ θ y)
    (hminus : ∀ᶠ a in l,0<realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))) :
    ∀ᶠ a in l,∀ lam ∈ Icc (F.epsilon a^2) 1,∀ z : ℂ,
      Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam z=0 →
        ‖z‖<1-c*F.epsilon a := by
  obtain ⟨hchalf,hdelta⟩ := (Flow.lt_cQ_iff θ y c).mp hc
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  have hq : Tendsto (fun a=>F.thetaAt a-2*c+F.epsilon a*(c^2+(F.tuning a).stepSize*(F.tuning a).tau))
      l (𝓝 (θ-2*c)) := by
    convert (F.theta_tendsto.sub_const (2*c)).add
      (F.epsilon_zero.mul ((tendsto_const_nhds (x:=c^2)).add (F.step_tendsto.mul F.tau_tendsto))) using 1
    all_goals first | (funext a;rfl) | simp only [zero_mul,add_zero]
  have hp : Tendsto (fun a=>Flow.delta (F.thetaAt a) (F.tuning a).stepSize c-
      (F.tuning a).stepSize*(1+(F.tuning a).tau)*c*F.epsilon a) l (𝓝 (Flow.delta θ y c)) := by
    have hd : Tendsto (fun a=>Flow.delta (F.thetaAt a) (F.tuning a).stepSize c) l (𝓝 (Flow.delta θ y c)) := by
      exact ((tendsto_const_nhds (x:=c^2)).sub (F.theta_tendsto.mul_const c)).add F.step_tendsto
    convert hd.sub (((F.step_tendsto.mul ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).mul_const c).mul
      F.epsilon_zero) using 1
    simp only [mul_zero,sub_zero]
  have hn : Tendsto (fun a=>(1+(F.tuning a).tau)*(1-c*F.epsilon a)-(F.tuning a).tau) l (𝓝 1) := by
    convert (((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto).mul hr).sub F.tau_tendsto using 1
    congr 1
    ring
  filter_upwards [F.epsilon_pos,F.beta_eq,hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hq.eventually (eventually_gt_nhds (by linarith : 0<θ-2*c)),
    hp.eventually (eventually_gt_nhds hdelta),hn.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hminus] with a he hβ hrad hdet hpos hquery hminus
  intro lam hlam z hz
  apply (Quadratic.roots_lt_radius_iff hrad).mpr ?_ z (by rwa [←Quadratic.characteristic_eq])
  have hqbound : Quadratic.Q (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam≤
      Quadratic.Q (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize (F.epsilon a^2) := by
    unfold Quadratic.Q
    nlinarith [mul_nonneg (F.tuning a).step_pos.le (F.tuning a).tau_nonneg,
      mul_le_mul_of_nonneg_right hlam.1
        (mul_nonneg (F.tuning a).step_pos.le (F.tuning a).tau_nonneg)]
  have hdet' : Quadratic.Q (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.epsilon a^2)<(1-c*F.epsilon a)^2 := by
    rw [hβ]
    unfold Quadratic.Q
    nlinarith [mul_pos he hdet]
  have hpos' : 0<realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) (1-c*F.epsilon a) := by
    rw [hβ,realCharacteristic_slow]
    exact mul_pos (sq_pos_of_pos he) hpos
  have hinc : realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) (1-c*F.epsilon a)≤
      realCharacteristic (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize lam (1-c*F.epsilon a) := by
    simp only [realCharacteristic_affine]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlam.1 (F.tuning a).step_pos.le) hquery.le
    linarith
  have hnegquery : (1+(F.tuning a).tau)*(-(1-c*F.epsilon a))-(F.tuning a).tau<0 := by
    nlinarith [(F.tuning a).tau_nonneg,
      mul_pos (show 0<1+(F.tuning a).tau by linarith [(F.tuning a).tau_nonneg]) hrad]
  have hdec : realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))≤
      realCharacteristic (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize lam (-(1-c*F.epsilon a)) := by
    simp only [realCharacteristic_affine]
    nlinarith [mul_le_mul_of_nonpos_right
      (mul_le_mul_of_nonneg_left hlam.2 (F.tuning a).step_pos.le) hnegquery.le]
  refine ⟨hqbound.trans_lt hdet',?_,?_⟩
  · exact hpos'.trans_le hinc
  · simpa only [realCharacteristic,neg_sq,mul_neg,sub_neg_eq_add] using hminus.trans_le hdec

theorem bulk_roots_eventually_lt {c : ℝ} (hc : c<Flow.cQ θ y)
    (hmargin : y*(1+2*τ)<4) :
    ∀ᶠ a in l,∀ lam ∈ Icc (F.epsilon a^2) 1,∀ z : ℂ,
      Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam z=0 →
        ‖z‖<1-c*F.epsilon a := by
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  have hm : Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))) l (𝓝 (4-y*(1+2*τ))) := by
    unfold realCharacteristic Quadratic.S Quadratic.Q
    convert (hr.neg.pow 2).sub
      ((((tendsto_const_nhds (x:=(1:ℝ))).add F.beta_tendsto).sub
        ((F.step_tendsto.mul_const 1).mul ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto))).mul hr.neg) |>.add
      (F.beta_tendsto.sub ((F.step_tendsto.mul_const 1).mul F.tau_tendsto)) using 1
    congr 1
    ring
  exact F.roots_eventually_lt_of_upper_endpoint hc
    (hm.eventually (eventually_gt_nhds (by linarith : 0<4-y*(1+2*τ))))

theorem bulk_rate_eventually_lt {c : ℝ} (hc : c<Flow.cQ θ y)
    (hmargin : y*(1+2*τ)<4) :
    ∀ᶠ a in l,F.rate a<1-c*F.epsilon a := by
  filter_upwards [F.bulk_roots_eventually_lt hc hmargin,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),F.epsilon_pos]
    with a ha he hp
  have hμL : F.epsilon a^2≤1 := by nlinarith
  obtain ⟨lam,hlam,z,hz,heq⟩ := (Quadratic.quadraticRate_isGreatest_general hμL
    (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau) (h:=(F.tuning a).stepSize)).1
  change Quadratic.quadraticRate (F.epsilon a^2) 1
    (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize<1-c*F.epsilon a
  rw [heq]
  exact ha lam hlam z hz

private def slowQuadratic (a : A) : Polynomial ℂ := X^2-
  C ((F.thetaAt a+(F.tuning a).stepSize*(1+(F.tuning a).tau)*F.epsilon a:ℝ):ℂ)*X+
  C ((F.tuning a).stepSize:ℂ)

private theorem slowQuadratic_degree (a : A) : (F.slowQuadratic a).natDegree≤2 := by
  unfold slowQuadratic
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le (by simp only [natDegree_pow,natDegree_X];omega)
      (natDegree_mul_le.trans (by simp only [natDegree_C,natDegree_X];omega))))
    (by simp only [natDegree_C];omega))

private theorem slowQuadratic_tendsto (z : ℂ) :
    Tendsto (fun a=>(F.slowQuadratic a).eval z) l (𝓝 (z^2-(θ:ℂ)*z+(y:ℂ))) := by
  have ht : Tendsto (fun a=>F.thetaAt a+(F.tuning a).stepSize*(1+(F.tuning a).tau)*F.epsilon a)
      l (𝓝 θ) := by
    convert F.theta_tendsto.add ((F.step_tendsto.mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).mul F.epsilon_zero) using 1
    all_goals first | (funext a;rfl) | simp only [mul_zero,add_zero]
  have hc := (Complex.continuous_ofReal.tendsto θ).comp ht
  have hy := (Complex.continuous_ofReal.tendsto y).comp F.step_tendsto
  have hh := ((tendsto_const_nhds (x:=z^2)).sub (hc.mul_const z)).add hy
  convert hh using 1
  funext a
  simp only [slowQuadratic,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C]
  rfl

private theorem slowQuadratic_actual : ∀ᶠ a in l,∀ w : ℂ,
    Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.epsilon a^2) (1-(F.epsilon a:ℂ)*w)=(F.epsilon a:ℂ)^2*(F.slowQuadratic a).eval w := by
  filter_upwards [F.beta_eq] with a ha w
  simp only [Quadratic.characteristic_eq,Quadratic.S,Quadratic.Q,slowQuadratic,
    eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C]
  rw [ha]
  push_cast
  ring

/-- The quadratic ceiling, without a strict limiting stability margin. -/
theorem quadratic_coefficient_eventually_lt {b : ℝ} (hb : Flow.cQ θ y<b) :
    ∀ᶠ a in l,(1-F.rate a)/F.epsilon a<b := by
  obtain ⟨γ,_,hγ⟩ := Flow.exists_quadratic_frequency F.theta_pos F.step_pos
  let w₀ : ℂ := -Flow.spiralExponent (Flow.cQ θ y) γ
  let p₀ : Polynomial ℂ := X^2-C (θ:ℂ)*X+C (y:ℂ)
  have hw : p₀.eval w₀=0 := by
    simp only [p₀,w₀,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C]
    linear_combination hγ
  have hre : w₀.re=Flow.cQ θ y := by simp [w₀,Flow.spiralExponent]
  have hp₀ : p₀≠0 := by
    intro hh
    have he := congrArg (Polynomial.eval (0:ℂ)) hh
    simp only [p₀,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_zero,
      zero_pow (by omega : 2≠0),mul_zero,sub_self,zero_add] at he
    exact (Complex.ofReal_ne_zero.mpr F.step_pos.ne') he
  have hδ : 0<b-w₀.re := by rw [hre];linarith
  have hnear := nesterov.Slow.eventually_exists_root_near F.slowQuadratic_degree
    (p₀:=p₀) (by intro z;simpa only [p₀,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C]
      using F.slowQuadratic_tendsto z) hp₀ hw hδ
  filter_upwards [hnear,F.slowQuadratic_actual,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a ha hactual he he1
  obtain ⟨w,hw,hd⟩ := ha
  have hz : Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.epsilon a^2) (1-(F.epsilon a:ℂ)*w)=0 := by rw [hactual w,hw,mul_zero]
  have hμL : F.epsilon a^2≤1 := by nlinarith
  have hrate := Quadratic.root_norm_le_rate_general hμL ⟨le_rfl,hμL⟩ hz
  have hwre : w.re<b := by
    have hh := Complex.re_le_norm (w-w₀)
    rw [Complex.sub_re] at hh
    linarith
  have hnorm : 1-F.epsilon a*w.re≤‖1-(F.epsilon a:ℂ)*w‖ := by
    simpa only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using Complex.re_le_norm (1-(F.epsilon a:ℂ)*w)
  apply (div_lt_iff₀ he).mpr
  change 1-Quadratic.quadraticRate (F.epsilon a^2) 1
    (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize<b*F.epsilon a
  nlinarith [mul_lt_mul_of_pos_left hwre he]

/-- Lemma cq: the exact first-order constant of the actual quadratic maximum. -/
theorem quadratic_coefficient_tendsto (hmargin : y*(1+2*τ)<4) :
    Tendsto (fun a=>(1-F.rate a)/F.epsilon a) l (𝓝 (Flow.cQ θ y)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    filter_upwards [F.bulk_rate_eventually_lt hc hmargin,F.epsilon_pos] with a ha he
    apply (lt_div_iff₀ he).mpr
    linarith
  · intro b hb
    exact F.quadratic_coefficient_eventually_lt hb

/-- The literal limsup statement of Lemma cq for stable accelerated families. -/
theorem quadratic_coefficient_limsup_le [NeBot l]
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    limsup (fun a=>(1-F.rate a)/F.epsilon a) l≤Flow.cQ θ y := by
  have hb : IsBoundedUnder (·≤·) l (fun a=>(1-F.rate a)/F.epsilon a) :=
    ⟨Flow.cQ θ y+1,(F.quadratic_coefficient_eventually_lt (by linarith : Flow.cQ θ y<Flow.cQ θ y+1)).mono
      fun _ ha=>ha.le⟩
  have hlo : ∀ᶠ a in l,0≤(1-F.rate a)/F.epsilon a := by
    filter_upwards [hstable,F.epsilon_pos,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a hs he he1
    have hμL : F.epsilon a^2≤1 := by nlinarith
    have hr := (Quadratic.stable_iff_quadraticRate_lt_one hμL).mp hs
    change F.rate a<1 at hr
    exact div_nonneg (by linarith) he.le
  exact (limsup_le_iff (isCoboundedUnder_le_of_eventually_le l hlo) hb).mpr
    (fun b hb=>F.quadratic_coefficient_eventually_lt hb)

end
end nesterov.TwoStep.Scaling
