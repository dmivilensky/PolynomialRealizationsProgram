import nesterov.Optimal.Model

/-! The literal unbounded-coordinate near-corner expansions. The error is
uniform on compact sets of the test constant and frequency coordinate. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

def nearCoefficientError (c : ℝ) (k : Fin 6) (a : A) : ℝ :=
  F.layerError c k a-firstCoefficient (parametersLimit c (F.thetaAt a) 2 (1/2)) k

def nearTailError (c ξ : ℝ) (a : A) : ℝ :=
  F.nearCoefficientError c 0 a+F.nearCoefficientError c 1 a*ξ+
    F.nearCoefficientError c 2 a*ξ^2

def nearMixedError (c ξ : ℝ) (a : A) : ℝ :=
  F.nearCoefficientError c 3 a+F.nearCoefficientError c 4 a*ξ+
    F.nearCoefficientError c 5 a*ξ^2

theorem near_coefficient_exact (c : ℝ) (k : Fin 6) : ∀ᶠ a in l,
    F.layerError c k a=firstCoefficient (F.parametersAt c a) k+
      F.epsilon a*coefficientRemainder (F.epsilon a) (F.parametersAt c a) k := by
  filter_upwards [F.epsilon_pos] with a he
  unfold layerError
  rw [scaled_coefficient_exact]
  field_simp
  ring

theorem near_coefficient_error_tendsto {c₀ : ℝ} {c : A→ℝ}
    (hc : Tendsto c l (𝓝 c₀)) (k : Fin 6) :
    Tendsto (fun a=>F.nearCoefficientError (c a) k a) l (𝓝 0) := by
  have hp : Tendsto (fun a=>F.parametersAt (c a) a) l
      (𝓝 (parametersLimit c₀ θ 2 (1/2))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases j
    · exact hc
    · exact F.theta_tendsto
    · exact F.step_tendsto
    · exact F.tau_tendsto
  have hq : Tendsto (fun a=>parametersLimit (c a) (F.thetaAt a) 2 (1/2)) l
      (𝓝 (parametersLimit c₀ θ 2 (1/2))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases j
    · exact hc
    · exact F.theta_tendsto
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have hfirst := ((continuous_firstCoefficient k).tendsto _).comp hp
  have hcorner := ((continuous_firstCoefficient k).tendsto _).comp hq
  have hrem := ((continuous_coefficientRemainder k).tendsto _).comp
    (F.epsilon_zero.prodMk_nhds hp)
  have h := (hfirst.add (F.epsilon_zero.mul hrem)).sub hcorner
  simp only [zero_mul,add_zero,sub_self,Function.comp_def] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos] with a he
  unfold nearCoefficientError layerError
  rw [scaled_coefficient_exact]
  field_simp
  ring

theorem near_tail_error_tendsto {c₀ ξ₀ : ℝ} {c ξ : A→ℝ}
    (hc : Tendsto c l (𝓝 c₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun a=>F.nearTailError (c a) (ξ a) a) l (𝓝 0) := by
  have h := ((F.near_coefficient_error_tendsto hc 0).add
    ((F.near_coefficient_error_tendsto hc 1).mul hξ)).add
      ((F.near_coefficient_error_tendsto hc 2).mul (hξ.pow 2))
  simpa only [nearTailError,zero_mul,add_zero] using h

theorem near_mixed_error_tendsto {c₀ ξ₀ : ℝ} {c ξ : A→ℝ}
    (hc : Tendsto c l (𝓝 c₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun a=>F.nearMixedError (c a) (ξ a) a) l (𝓝 0) := by
  have h := ((F.near_coefficient_error_tendsto hc 3).add
    ((F.near_coefficient_error_tendsto hc 4).mul hξ)).add
      ((F.near_coefficient_error_tendsto hc 5).mul (hξ.pow 2))
  simpa only [nearMixedError,zero_mul,add_zero] using h

theorem near_tail_exact (c : ℝ) : ∀ᶠ a in l,∀ ξ : ℝ,
    scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ=
      F.epsilon a*(F.cornerNAt a ξ-4*c*(3-ξ)+F.nearTailError c ξ a) := by
  filter_upwards [F.epsilon_pos] with a he ξ
  unfold nearTailError nearCoefficientError layerError scaledTail cornerNAt cornerAlpha stabilityMargin
  dsimp [scaledCoefficient,zeroCoefficient,firstCoefficient,parametersAt,parametersLimit,
    dotP1,dotP2,dotP3]
  field_simp
  ring

theorem near_mixed_exact (c : ℝ) : ∀ᶠ a in l,∀ ξ : ℝ,
    (scaledQ0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau+
      scaledQ1 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*ξ+
      scaledQ2 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau*ξ^2)=
      F.epsilon a*(F.cornerNAt a ξ-2*c*(4-ξ)+F.nearMixedError c ξ a) := by
  filter_upwards [F.epsilon_pos] with a he ξ
  unfold nearMixedError nearCoefficientError layerError cornerNAt cornerAlpha stabilityMargin
  dsimp [scaledCoefficient,zeroCoefficient,firstCoefficient,parametersAt,parametersLimit,
    dotQ0,dotQ1,dotQ2]
  field_simp
  ring

theorem near_tail_error_uniform {K : Set (ℝ×ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a p=>F.nearTailError p.1 p.2 a) (fun _=>0) l K := by
  apply Slow.uniform_on_compact_of_joint_limit continuous_const _ hK
  intro p
  have hc : Tendsto (fun x : A×(ℝ×ℝ)=>x.2.1) (l×ˢ𝓝 p) (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp tendsto_snd
  have hξ : Tendsto (fun x : A×(ℝ×ℝ)=>x.2.2) (l×ˢ𝓝 p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp tendsto_snd
  exact (F.reindex Prod.fst tendsto_fst).near_tail_error_tendsto hc hξ

theorem near_mixed_error_uniform {K : Set (ℝ×ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a p=>F.nearMixedError p.1 p.2 a) (fun _=>0) l K := by
  apply Slow.uniform_on_compact_of_joint_limit continuous_const _ hK
  intro p
  have hc : Tendsto (fun x : A×(ℝ×ℝ)=>x.2.1) (l×ˢ𝓝 p) (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp tendsto_snd
  have hξ : Tendsto (fun x : A×(ℝ×ℝ)=>x.2.2) (l×ˢ𝓝 p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp tendsto_snd
  exact (F.reindex Prod.fst tendsto_fst).near_mixed_error_tendsto hc hξ

end
end nesterov.TwoStep.Scaling
