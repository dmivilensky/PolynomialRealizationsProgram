import nesterov.Layer.Coefficients
import nesterov.Layer.SpreadWitnessSymbols

/-! The exact cubic's layer limit, including the negligible constant term,
uniformly on every compact phi set. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def layerCubic (c : ℝ) (a : A) (ξ : ℝ) : ℝ :=
  scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau+
    ξ*scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ

def layerMixed (c : ℝ) (a : A) (ξ : ℝ) : ℝ :=
  scaledQ0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau+
    scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*ξ+
    scaledQ2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*ξ^2

theorem layerCubic_actual (c : ℝ) : ∀ᶠ a in l,∀ ω : ℝ,
    ((1-circle (1-c*F.epsilon a) ω)*
      Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re=
        F.layerCubic c a (1-Real.cos ω) := by
  filter_upwards [F.beta_eq] with a hb ω
  rw [Spread.product_normalized,←mul_assoc,Quadratic.characteristic_eq,Quadratic.characteristic_eq]
  change ((1-circle _ ω)*quad _ _ (circle _ ω)*star (quad _ _ (circle _ ω))).re=_
  rw [lagOne_cubic,hb]
  simp only [mul_one]
  unfold layerCubic scaledTail scaledP0 scaledP1 scaledP2 scaledP3
  simp only [Quadratic.S,Quadratic.Q,one_mul,mul_one]
  ring

theorem layerMixed_actual (c : ℝ) : ∀ᶠ a in l,∀ ξ : ℝ,
    mixedPolynomial (F.tuning a).beta (F.tuning a).tau
      ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize (1-c*F.epsilon a) ξ=
        F.layerMixed c a ξ := by
  filter_upwards [F.beta_eq] with a hb ξ
  rw [mixedPolynomial_coefficients,hb]
  rfl

private theorem P0_rescaling {ε s c p q : ℝ} (hs : s^2=ε) (hsp : s≠0) :
    (c*ε*(ε^2*p)*q)/(ε*s)=c*(ε*s)*p*q := by
  rw [←hs]
  field_simp

theorem P0_layer_tendsto (c : ℝ) :
    Tendsto (fun a=>scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/(F.epsilon a*Real.sqrt (F.epsilon a))) l (𝓝 0) := by
  have ht := (((F.epsilon_zero.mul F.sqrt_epsilon_tendsto).const_mul c).mul
    (F.slow_test_tendsto c)).mul (F.characteristic_at_radius_tendsto c 1)
  simp only [zero_mul,mul_zero] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos,F.beta_eq] with a he hb
  rw [hb,scaledP0_exact,realCharacteristic_slow]
  exact (P0_rescaling (Real.sq_sqrt he.le) (Real.sqrt_pos.mpr he).ne').symm

variable (F : Scaling A l θ y (1/2))

private theorem cubic_rescaling {ε s p t φ : ℝ} (he : ε≠0) (hs : s≠0) :
    (p+(s*φ)*t)/(ε*s)=p/(ε*s)+φ*(t/ε) := by
  field_simp

theorem layer_cubic_tendsto {B φ₀ : ℝ} {φ : A→ℝ} (c : ℝ)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hφ : Tendsto φ l (𝓝 φ₀)) :
    Tendsto (fun a=>F.layerCubic c a (Real.sqrt (F.epsilon a)*φ a)/
      (F.epsilon a*Real.sqrt (F.epsilon a))) l (𝓝 (φ₀*Layer.polynomial θ y c B φ₀)) := by
  have ht := (F.P0_layer_tendsto c).add (hφ.mul (F.layer_tail_tendsto c hB hφ))
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos] with a he
  exact (cubic_rescaling he.ne' (Real.sqrt_pos.mpr he).ne').symm

theorem layer_cubic_uniform {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a φ=>F.layerCubic c a (Real.sqrt (F.epsilon a)*φ)/
      (F.epsilon a*Real.sqrt (F.epsilon a)))
      (fun φ=>φ*Layer.polynomial θ y c B φ) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Layer.polynomial;fun_prop) _ hK
  intro φ
  exact (F.reindex Prod.fst tendsto_fst).layer_cubic_tendsto c (hB.comp tendsto_fst) tendsto_snd

theorem layer_mixed_bounded {B : ℝ} (c : ℝ) (hB : Tendsto F.layerDeficit l (𝓝 B))
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ a in l,∀ φ∈K,
      |F.layerMixed c a (Real.sqrt (F.epsilon a)*φ)|≤M*F.epsilon a := by
  obtain ⟨M,hM,hbound⟩ := Slow.uniformly_eventually_norm_bounded hK
    (show Continuous (Layer.mixedPolynomial θ y c B) by unfold Layer.mixedPolynomial;fun_prop)
      (F.layer_mixed_uniform c hB hK)
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound,F.epsilon_pos] with a ha he φ hφ
  have hh : |F.layerMixed c a (Real.sqrt (F.epsilon a)*φ)/F.epsilon a|≤M := ha φ hφ
  rwa [abs_div,abs_of_pos he,div_le_iff₀ he] at hh

end
end nesterov.TwoStep.Scaling
