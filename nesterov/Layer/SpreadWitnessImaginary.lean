import nesterov.TwoStep.ScaledCoefficients

/-! Positivity of the actual cross-characteristic imaginary part below θ/2. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem spread_cross_im_eventually_pos {c : ℝ} (hc : c<θ/2) :
    ∀ᶠ a in l, ∀ ω∈Ioo (0:ℝ) Real.pi,
      0<(Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.epsilon a^2) (circle (1-c*F.epsilon a) ω)*
        star (Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau
          (F.tuning a).stepSize 1 (circle (1-c*F.epsilon a) ω))).im := by
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [F.epsilon_pos,F.beta_eq,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    F.theta_tendsto.eventually (eventually_gt_nhds (show 2*c<θ by linarith)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with a he hb he1 hθ hr ω hω
  have hstep := (F.tuning a).step_pos
  have htau := (F.tuning a).tau_nonneg
  have hchi (lam : ℝ) : Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize lam (circle (1-c*F.epsilon a) ω)=
      Quadratic.characteristic (1-F.thetaAt a*F.epsilon a) (F.tuning a).tau 1
        ((F.tuning a).stepSize*lam) (circle (1-c*F.epsilon a) ω) := by
    rw [hb]
    simp only [Quadratic.characteristic]
    push_cast
    ring
  rw [hchi,hchi,mul_one,scaled_cross_im]
  have hd : 0<(F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2 := by
    nlinarith [mul_pos hstep (show 0<1-F.epsilon a^2 by nlinarith)]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hξ : 0≤1-Real.cos ω := sub_nonneg.mpr (Real.cos_le_one ω)
  have hbpos : 0<F.epsilon a*(F.thetaAt a-2*c)+
      (1+(F.tuning a).tau)*c^2*F.epsilon a^2+
        2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω) := by
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (mul_pos he (by exact sub_pos.mpr hθ)) (by positivity))
      (by positivity)
  exact mul_pos (mul_pos (mul_pos hd hr) hsin) hbpos

end
end nesterov.TwoStep.Scaling
