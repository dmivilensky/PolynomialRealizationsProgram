import nesterov.Momentum.Parameters
import nesterov.Flow.Constants

/-! The article's accelerated scaling, over an arbitrary parameter filter.
Physical tuning restrictions are retained on every family member. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

structure Scaling (A : Type*) (l : Filter A) (θ y τ : ℝ) where
  epsilon : A→ℝ
  tuning : A→Momentum.Tuning
  epsilon_tendsto : Tendsto epsilon l (𝓝[>] (0:ℝ))
  theta_tendsto : Tendsto (fun a=>(1-(tuning a).beta)/epsilon a) l (𝓝 θ)
  step_tendsto : Tendsto (fun a=>(tuning a).stepSize) l (𝓝 y)
  tau_tendsto : Tendsto (fun a=>(tuning a).tau) l (𝓝 τ)
  theta_pos : 0<θ
  step_pos : 0<y
  tau_nonneg : 0≤τ

def realCharacteristic (β τ h lam z : ℝ) : ℝ :=
  z^2-Quadratic.S β τ h lam*z+Quadratic.Q β τ h lam

theorem realCharacteristic_slow (ε θ y τ c : ℝ) :
    realCharacteristic (1-θ*ε) τ y (ε^2) (1-c*ε)=
      ε^2*(Flow.delta θ y c-y*(1+τ)*c*ε) := by
  unfold realCharacteristic Quadratic.S Quadratic.Q Flow.delta
  ring

theorem realCharacteristic_affine (β τ h lam z : ℝ) :
    realCharacteristic β τ h lam z=
      (z-1)*(z-β)+h*lam*((1+τ)*z-τ) := by
  unfold realCharacteristic Quadratic.S Quadratic.Q
  ring

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def thetaAt (a : A) : ℝ := (1-(F.tuning a).beta)/F.epsilon a
def rate (a : A) : ℝ := Quadratic.quadraticRate (F.epsilon a^2) 1
  (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize

theorem epsilon_zero : Tendsto F.epsilon l (𝓝 0) :=
  F.epsilon_tendsto.mono_right nhdsWithin_le_nhds

theorem epsilon_pos : ∀ᶠ a in l,0<F.epsilon a :=
  F.epsilon_tendsto.eventually self_mem_nhdsWithin

theorem beta_eq : ∀ᶠ a in l,(F.tuning a).beta=1-F.thetaAt a*F.epsilon a := by
  filter_upwards [F.epsilon_pos] with a ha
  unfold thetaAt
  field_simp
  ring

theorem beta_tendsto : Tendsto (fun a=>(F.tuning a).beta) l (𝓝 1) := by
  have ht := (tendsto_const_nhds (x:=(1:ℝ)) (f:=l)).sub (F.theta_tendsto.mul F.epsilon_zero)
  have hh := ht.congr' (by
    filter_upwards [F.beta_eq] with a ha
    exact ha.symm)
  simpa only [mul_zero,sub_zero] using hh

/-- Change the family parameter without changing any physical tuning. -/
def reindex {B : Type*} {m : Filter B} (f : B→A) (hf : Tendsto f m l) : Scaling B m θ y τ where
  epsilon := F.epsilon ∘ f
  tuning := F.tuning ∘ f
  epsilon_tendsto := F.epsilon_tendsto.comp hf
  theta_tendsto := F.theta_tendsto.comp hf
  step_tendsto := F.step_tendsto.comp hf
  tau_tendsto := F.tau_tendsto.comp hf
  theta_pos := F.theta_pos
  step_pos := F.step_pos
  tau_nonneg := F.tau_nonneg

theorem limiting_stability_margin_le [NeBot l]
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) : y*(1+2*τ)≤4 := by
  have hl := F.step_tendsto.mul ((tendsto_const_nhds (x:=(1:ℝ))).add (F.tau_tendsto.const_mul 2))
  have hr := ((tendsto_const_nhds (x:=(1:ℝ))).add F.beta_tendsto).const_mul 2
  have hr' : Tendsto (fun a=>2*(1+(F.tuning a).beta)) l (𝓝 4) := by
    convert hr using 1
    norm_num
  apply le_of_tendsto_of_tendsto hl hr'
  filter_upwards [hstable,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a hs he he1
  have hh := ((F.tuning a).stable_iff (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)).mp hs
  simpa only [mul_one] using hh.le

end Scaling
end
end nesterov.TwoStep
