import nesterov.Layer.Coefficients
import nesterov.TwoStep.StabilityMargin

/-! Exact moving corner coordinates; no boundedness of either coordinate
is included in this model. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def cornerAlpha (a : A) : ℝ :=
  (1/2-(F.tuning a).tau)*(F.tuning a).stepSize/(2*F.epsilon a)

def cornerNAt (a : A) (ξ : ℝ) : ℝ :=
  4*F.thetaAt a+2*(F.thetaAt a-4*F.cornerAlpha a)*ξ+
    (F.stabilityMargin a+4*F.cornerAlpha a-4*F.thetaAt a)*ξ^2

def cornerRatioAt (a : A) (ξ : ℝ) : ℝ := F.cornerNAt a ξ/(4*(3-ξ))

def cornerLagAt (a : A) : ℝ := sInf (F.cornerRatioAt a '' Icc 0 2)

def cornerDefect (a : A) : ℝ := max (4*F.cornerAlpha a-5) 0

theorem corner_alpha_exact : ∀ᶠ a in l,
    2*(F.tuning a).stepSize*(2*(F.tuning a).tau-1)=
      -8*F.cornerAlpha a*F.epsilon a := by
  filter_upwards [F.epsilon_pos] with a he
  unfold cornerAlpha
  field_simp
  ring

theorem corner_tail_exact : ∀ᶠ a in l,
    4*(1-(F.tuning a).tau*(F.tuning a).stepSize)=
      (F.stabilityMargin a+4*F.cornerAlpha a)*F.epsilon a := by
  filter_upwards [F.epsilon_pos] with a he
  unfold cornerAlpha stabilityMargin
  field_simp
  ring

theorem corner_margin_numerator_tendsto :
    Tendsto (fun a=>F.epsilon a*F.stabilityMargin a) l (𝓝 (4-y*(1+2*τ))) := by
  have h : Tendsto (fun a=>4-(F.tuning a).stepSize*(1+2*(F.tuning a).tau)) l
      (𝓝 (4-y*(1+2*τ))) := tendsto_const_nhds.sub (F.step_tendsto.mul
    (tendsto_const_nhds.add (F.tau_tendsto.const_mul 2)))
  apply h.congr'
  filter_upwards [F.epsilon_pos] with a he
  unfold stabilityMargin
  field_simp

theorem corner_defect_nonneg (a : A) : 0≤F.cornerDefect a := le_max_right _ _

theorem corner_denominator_pos
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,0<F.stabilityMargin a+5+F.cornerDefect a := by
  filter_upwards [F.stable_iff_scaled_margin,hstable,F.epsilon_pos] with a hs hstab he
  have hθ : 0<F.thetaAt a := div_pos (sub_pos.mpr (F.tuning a).beta_lt_one) he
  have hm := hs.mp hstab
  linarith [F.corner_defect_nonneg a]

end
end nesterov.TwoStep.Scaling
