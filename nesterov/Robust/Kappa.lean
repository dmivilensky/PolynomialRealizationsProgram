import nesterov.Robust.Asymptotics
import nesterov.Robust.Scaling

/-! Literal condition-number parameterization of the TMM physical limits. -/
namespace nesterov.Robust
noncomputable section
open Filter
open scoped Topology

theorem tmm_kappa_parameters {A : Type*} {l : Filter A} {κ : A→ℝ}
    (hκ : ∀ a,1<κ a) (hκtop : Tendsto κ l atTop) :
    Tendsto (fun a=>(1-(tmmDesign (κ a) (hκ a)).beta)/Slow.epsilon (κ a)) l (𝓝 3) ∧
    Tendsto (fun a=>(tmmDesign (κ a) (hκ a)).step) l (𝓝 2) ∧
    Tendsto (fun a=>(tmmDesign (κ a) (hκ a)).tau) l (𝓝 (1/2)) ∧
    Tendsto (fun a=>(1/2-(tmmDesign (κ a) (hκ a)).tau)/Slow.epsilon (κ a)) l (𝓝 (5/4)) ∧
    Tendsto (fun a=>(2-(tmmDesign (κ a) (hκ a)).step)/Slow.epsilon (κ a)) l (𝓝 1) := by
  let D : A→Design := fun a=>tmmDesign (κ a) (hκ a)
  have hT : ∀ a,(D a).kappa*(1-(D a).rho)^2=1 := fun a=>tmm_design_equality (κ a) (hκ a)
  have he : Tendsto (fun a=>Slow.epsilon (κ a)) l (𝓝 0) :=
    (Slow.epsilon_tendsto.mono_right nhdsWithin_le_nhds).comp hκtop
  have hr : Tendsto (fun a=>(D a).rho) l (𝓝 1) := by
    simpa only [D,tmmDesign,ofInterval,Slow.epsilon,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub he
  have hg (a : A) : 1-(D a).rho=Slow.epsilon (κ a) := by
    change 1-(1-1/Real.sqrt (κ a))=1/Real.sqrt (κ a)
    ring
  refine ⟨?_,Design.tmm_step_tendsto D hT hr,Design.tmm_tau_tendsto D hT hr,?_,?_⟩
  · simpa only [hg] using Design.tmm_theta_tendsto D hT hr
  · simpa only [hg] using Design.tmm_a_tendsto D hT hr
  · simpa only [hg] using Design.tmm_b_tendsto D hT

theorem tmm_kappa_deficit_isBigO {A : Type*} {l : Filter A} {κ : A→ℝ}
    (hκ : ∀ a,1<κ a) (hκtop : Tendsto κ l atTop) :
    (fun a=>(1/2-(tmmDesign (κ a) (hκ a)).tau)-5/4*Slow.epsilon (κ a)) =O[l]
      (fun a=>Slow.epsilon (κ a)^2) := by
  let D : A→Design := fun a=>tmmDesign (κ a) (hκ a)
  have hT : ∀ a,(D a).kappa*(1-(D a).rho)^2=1 := fun a=>tmm_design_equality (κ a) (hκ a)
  have he : Tendsto (fun a=>Slow.epsilon (κ a)) l (𝓝 0) :=
    (Slow.epsilon_tendsto.mono_right nhdsWithin_le_nhds).comp hκtop
  have hr : Tendsto (fun a=>(D a).rho) l (𝓝 1) := by
    simpa only [D,tmmDesign,ofInterval,Slow.epsilon,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub he
  have hg (a : A) : 1-(D a).rho=Slow.epsilon (κ a) := by
    change 1-(1-1/Real.sqrt (κ a))=1/Real.sqrt (κ a)
    ring
  simpa only [hg] using Design.tmm_deficit_isBigO D hT hr

end
end nesterov.Robust
