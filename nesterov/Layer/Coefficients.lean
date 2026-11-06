import nesterov.Layer.Model
import nesterov.TwoStep.LagScaled
import nesterov.Slow.Uniform

/-! Exact rescaling and compact-uniform limits of both layer quadratics. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology

private theorem middle_rescaling {ε s τ y p : ℝ} (hs : s^2=ε) (hsp : s≠0) :
    p/s= -4*y*((1/2-τ)/s)+s*((p-2*y*(2*τ-1))/ε) := by
  rw [←hs]
  field_simp
  ring

private theorem tail_rescaling {ε s p₁ p₂ p₃ φ : ℝ} (hs : s^2=ε) (hsp : s≠0) :
    (p₁+p₂*(s*φ)+p₃*(s*φ)^2)/ε=p₁/ε+(p₂/s)*φ+p₃*φ^2 := by
  rw [←hs]
  field_simp

variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def layerError (c : ℝ) (k : Fin 6) (a : A) : ℝ :=
  (scaledCoefficient (F.epsilon a) (F.parametersAt c a) k-
    zeroCoefficient (F.parametersAt c a) k)/F.epsilon a

theorem layerError_tendsto (c : ℝ) (k : Fin 6) :
    Tendsto (F.layerError c k) l (𝓝 (firstCoefficient (parametersLimit c θ y τ) k)) :=
  F.coefficient_first_order c k

theorem P2_layer_exact (c : ℝ) : ∀ᶠ a in l,
    scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau/
      Real.sqrt (F.epsilon a)= -4*(F.tuning a).stepSize*F.layerDeficit a+
        Real.sqrt (F.epsilon a)*F.layerError c 1 a := by
  filter_upwards [F.epsilon_pos] with a ha
  exact middle_rescaling (Real.sq_sqrt ha.le) (Real.sqrt_pos.mpr ha).ne'

theorem Q1_layer_exact (c : ℝ) : ∀ᶠ a in l,
    scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau/
      Real.sqrt (F.epsilon a)= -4*(F.tuning a).stepSize*F.layerDeficit a+
        Real.sqrt (F.epsilon a)*F.layerError c 4 a := by
  filter_upwards [F.epsilon_pos] with a ha
  exact middle_rescaling (Real.sq_sqrt ha.le) (Real.sqrt_pos.mpr ha).ne'

theorem P2_layer_tendsto {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B)) :
    Tendsto (fun a=>scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/Real.sqrt (F.epsilon a)) l (𝓝 (-4*y*B)) := by
  have ht := ((F.step_tendsto.const_mul (-4)).mul hB).add
    (F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto c 1))
  simp only [zero_mul,add_zero] at ht
  exact ht.congr' ((F.P2_layer_exact c).mono fun _ h=>h.symm)

theorem Q1_layer_tendsto {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B)) :
    Tendsto (fun a=>scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/Real.sqrt (F.epsilon a)) l (𝓝 (-4*y*B)) := by
  have ht := ((F.step_tendsto.const_mul (-4)).mul hB).add
    (F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto c 4))
  simp only [zero_mul,add_zero] at ht
  exact ht.congr' ((F.Q1_layer_exact c).mono fun _ h=>h.symm)

theorem Q0_div_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledQ0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/F.epsilon a) l (𝓝 (2*y*(θ-2*c))) := by
  have ht := F.coefficient_first_order c 3
  have he : firstCoefficient (parametersLimit c θ y τ) 3=2*y*(θ-2*c) := by
    dsimp [firstCoefficient,parametersLimit,dotQ0]
    ring
  rw [he] at ht
  simpa [scaledCoefficient,zeroCoefficient,parametersAt] using ht

theorem Q2_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledQ2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau) l (𝓝 (4*(1-τ*y))) := F.coefficient_tendsto c 5

theorem layer_tail_exact (c : ℝ) : ∀ᶠ a in l,∀ φ : ℝ,
    scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau
      (Real.sqrt (F.epsilon a)*φ)/F.epsilon a=
      scaledP1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau/F.epsilon a+
      (scaledP2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau/
        Real.sqrt (F.epsilon a))*φ+
      scaledP3 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*φ^2 := by
  filter_upwards [F.epsilon_pos] with a he φ
  exact tail_rescaling (Real.sq_sqrt he.le) (Real.sqrt_pos.mpr he).ne'

variable (F : Scaling A l θ y (1/2))

theorem layer_tail_tendsto {B φ₀ : ℝ} {φ : A→ℝ} (c : ℝ)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hφ : Tendsto φ l (𝓝 φ₀)) :
    Tendsto (fun a=>scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau (Real.sqrt (F.epsilon a)*φ a)/F.epsilon a)
      l (𝓝 (Layer.polynomial θ y c B φ₀)) := by
  have ht := ((F.P1_div_tendsto c).add ((F.P2_layer_tendsto c hB).mul hφ)).add
    ((F.P3_tendsto c).mul (hφ.pow 2))
  have he : 2*y*(θ-3*c)+(-4*y*B)*φ₀+4*(1-(1/2)*y)*φ₀^2=
      Layer.polynomial θ y c B φ₀ := by unfold Layer.polynomial;ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos] with a ha
  exact (tail_rescaling (Real.sq_sqrt ha.le) (Real.sqrt_pos.mpr ha).ne').symm

theorem layer_mixed_tendsto {B φ₀ : ℝ} {φ : A→ℝ} (c : ℝ)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hφ : Tendsto φ l (𝓝 φ₀)) :
    Tendsto (fun a=>(scaledQ0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau+scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau*(Real.sqrt (F.epsilon a)*φ a)+
      scaledQ2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau*(Real.sqrt (F.epsilon a)*φ a)^2)/F.epsilon a)
      l (𝓝 (Layer.mixedPolynomial θ y c B φ₀)) := by
  have ht := ((F.Q0_div_tendsto c).add ((F.Q1_layer_tendsto c hB).mul hφ)).add
    ((F.Q2_tendsto c).mul (hφ.pow 2))
  have he : 2*y*(θ-2*c)+(-4*y*B)*φ₀+4*(1-(1/2)*y)*φ₀^2=
      Layer.mixedPolynomial θ y c B φ₀ := by unfold Layer.mixedPolynomial;ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos] with a ha
  exact (tail_rescaling (Real.sq_sqrt ha.le) (Real.sqrt_pos.mpr ha).ne').symm

theorem layer_tail_uniform {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a φ=>scaledTail (F.epsilon a) c (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau (Real.sqrt (F.epsilon a)*φ)/F.epsilon a)
      (Layer.polynomial θ y c B) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Layer.polynomial;fun_prop) _ hK
  intro φ
  exact (F.reindex Prod.fst tendsto_fst).layer_tail_tendsto c (hB.comp tendsto_fst) tendsto_snd

theorem layer_mixed_uniform {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a φ=>(scaledQ0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau+scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau*(Real.sqrt (F.epsilon a)*φ)+
      scaledQ2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau*(Real.sqrt (F.epsilon a)*φ)^2)/F.epsilon a)
      (Layer.mixedPolynomial θ y c B) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Layer.mixedPolynomial;fun_prop) _ hK
  intro φ
  exact (F.reindex Prod.fst tendsto_fst).layer_mixed_tendsto c (hB.comp tendsto_fst) tendsto_snd

end
end nesterov.TwoStep.Scaling
