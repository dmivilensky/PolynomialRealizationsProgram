import nesterov.Layer.SpreadWitnessSymbols
import nesterov.TwoStep.AsymptoticsModel
import nesterov.Slow.Uniform

/-! Uniform bounds for the actual characteristic product on fixed compact
frequency sets. No bounds on the scaled corner coordinates are assumed. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Phase
open scoped Topology

variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem characteristic_product_bounded_on_compact (c : ℝ) {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ X : ℝ,0<X ∧ ∀ᶠ a in l,∀ ω∈K,
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤X := by
  let P : (ℝ×ℝ×ℝ×ℝ×ℝ×ℝ)→ℂ := fun p=>
    Quadratic.characteristic p.1 p.2.1 p.2.2.1 (p.2.2.2.1^2)
      (circle p.2.2.2.2.1 p.2.2.2.2.2)*
    star (Quadratic.characteristic p.1 p.2.1 p.2.2.1 1
      (circle p.2.2.2.2.1 p.2.2.2.2.2))
  have hP : Continuous P := by
    unfold P Quadratic.characteristic Quadratic.queryPolynomial circle polyak.Waves.z
    fun_prop
  have hlim : Continuous (fun ω=>P (1,τ,y,0,1,ω)) := by fun_prop
  have hj (ω : ℝ) : Tendsto (fun p : A×ℝ=>Spread.product (F.tuning p.1)
      (F.epsilon p.1^2) 1 (1-c*F.epsilon p.1) p.2) (l ×ˢ 𝓝 ω)
      (𝓝 (P (1,τ,y,0,1,ω))) := by
    have hβ := F.beta_tendsto.comp (tendsto_fst (f:=l) (g:=𝓝 ω))
    have hτ := F.tau_tendsto.comp (tendsto_fst (f:=l) (g:=𝓝 ω))
    have hh := F.step_tendsto.comp (tendsto_fst (f:=l) (g:=𝓝 ω))
    have hε := F.epsilon_zero.comp (tendsto_fst (f:=l) (g:=𝓝 ω))
    have hr : Tendsto (fun p : A×ℝ=>1-c*F.epsilon p.1) (l ×ˢ 𝓝 ω) (𝓝 1) := by
      simpa only [mul_zero,sub_zero,Function.comp_def] using
        (tendsto_const_nhds (x:=(1:ℝ))).sub (hε.const_mul c)
    have hp : Tendsto (fun p : A×ℝ=>((F.tuning p.1).beta,(F.tuning p.1).tau,
        (F.tuning p.1).stepSize,F.epsilon p.1,1-c*F.epsilon p.1,p.2))
        (l ×ˢ 𝓝 ω) (𝓝 (1,τ,y,0,1,ω)) :=
      hβ.prodMk_nhds (hτ.prodMk_nhds (hh.prodMk_nhds
        (hε.prodMk_nhds (hr.prodMk_nhds (tendsto_snd (f:=l) (g:=𝓝 ω))))))
    change Tendsto (fun p : A×ℝ=>P ((F.tuning p.1).beta,(F.tuning p.1).tau,
      (F.tuning p.1).stepSize,F.epsilon p.1,1-c*F.epsilon p.1,p.2))
      (l ×ˢ 𝓝 ω) (𝓝 (P (1,τ,y,0,1,ω)))
    exact (hP.tendsto (1,τ,y,0,1,ω)).comp hp
  have hu : TendstoUniformlyOn (fun a ω=>Spread.product (F.tuning a)
      (F.epsilon a^2) 1 (1-c*F.epsilon a) ω) (fun ω=>P (1,τ,y,0,1,ω)) l K :=
    Slow.uniform_on_compact_of_joint_limit hlim hj hK
  exact Slow.uniformly_eventually_norm_bounded hK hlim hu

end
end nesterov.TwoStep.Scaling
