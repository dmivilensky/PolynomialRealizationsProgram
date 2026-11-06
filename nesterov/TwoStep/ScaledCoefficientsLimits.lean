import nesterov.TwoStep.ScaledCoefficientsUniform

/-! Moving-parameter limits of the exact compact-uniform coefficient expansions. -/
namespace nesterov.TwoStep
noncomputable section
open Filter
open scoped Topology
namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def parametersAt (c : ℝ) (a : A) : ScaledParameters :=
  ![c,F.thetaAt a,(F.tuning a).stepSize,(F.tuning a).tau]
def parametersLimit (c θ y τ : ℝ) : ScaledParameters := ![c,θ,y,τ]

theorem parameters_tendsto (c : ℝ) : Tendsto (F.parametersAt c) l (𝓝 (parametersLimit c θ y τ)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · exact tendsto_const_nhds
  · exact F.theta_tendsto
  · exact F.step_tendsto
  · exact F.tau_tendsto

theorem remainder_tendsto (c : ℝ) (k : Fin 6) :
    Tendsto (fun a=>coefficientRemainder (F.epsilon a) (F.parametersAt c a) k) l
      (𝓝 (coefficientRemainder 0 (parametersLimit c θ y τ) k)) := by
  have hh := ((continuous_coefficientRemainder k).tendsto (0,parametersLimit c θ y τ)).comp
    (F.epsilon_zero.prodMk_nhds (F.parameters_tendsto c))
  simpa only [Function.comp_def] using hh

theorem coefficient_tendsto (c : ℝ) (k : Fin 6) :
    Tendsto (fun a=>scaledCoefficient (F.epsilon a) (F.parametersAt c a) k) l
      (𝓝 (zeroCoefficient (parametersLimit c θ y τ) k)) := by
  have hz := ((continuous_zeroCoefficient k).tendsto _).comp (F.parameters_tendsto c)
  have hf := ((continuous_firstCoefficient k).tendsto _).comp (F.parameters_tendsto c)
  have hh := (hz.add (F.epsilon_zero.mul hf)).add ((F.epsilon_zero.pow 2).mul (F.remainder_tendsto c k))
  simp only [zero_pow (by omega : 2≠0),zero_mul,add_zero,Function.comp_def] at hh
  exact hh.congr' (Eventually.of_forall fun a=>(scaled_coefficient_exact _ _ _).symm)

theorem coefficient_first_order (c : ℝ) (k : Fin 6) :
    Tendsto (fun a=>(scaledCoefficient (F.epsilon a) (F.parametersAt c a) k-
      zeroCoefficient (F.parametersAt c a) k)/F.epsilon a) l
      (𝓝 (firstCoefficient (parametersLimit c θ y τ) k)) := by
  have hf := ((continuous_firstCoefficient k).tendsto _).comp (F.parameters_tendsto c)
  have hh := hf.add (F.epsilon_zero.mul (F.remainder_tendsto c k))
  simp only [zero_mul,add_zero] at hh
  apply hh.congr'
  filter_upwards [F.epsilon_pos] with a ha
  dsimp only [Function.comp_def]
  rw [scaled_coefficient_exact]
  field_simp
  ring

theorem P1_div_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledP1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/F.epsilon a) l (𝓝 (2*y*(θ-3*c))) := by
  have hh := F.coefficient_first_order c 0
  have he : firstCoefficient (parametersLimit c θ y τ) 0=2*y*(θ-3*c) := by
    dsimp [firstCoefficient,parametersLimit,dotP1]
    ring
  rw [he] at hh
  simpa [scaledCoefficient,zeroCoefficient,parametersAt] using hh

theorem P2_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau) l (𝓝 (2*y*(2*τ-1))) := by
  exact F.coefficient_tendsto c 1

theorem P3_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledP3 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau) l (𝓝 (4*(1-τ*y))) := by
  exact F.coefficient_tendsto c 2

end Scaling
end
end nesterov.TwoStep
