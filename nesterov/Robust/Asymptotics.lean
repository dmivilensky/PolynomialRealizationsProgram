import nesterov.Robust.TMM
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Exact TMM deficit identities and limits of the actual physical
coefficients. The identities retain the original member parameters. -/
namespace nesterov.Robust.Design
noncomputable section
open Filter
open scoped Topology

theorem tmm_theta_identity (D : Robust.Design) (hT : D.kappa*(1-D.rho)^2=1) :
    (1-D.beta)/(1-D.rho)=(3-(1-D.rho))/(1+(1-D.rho)) := by
  rw [D.tmm_beta hT]
  have hg := D.gap_pos.ne'
  have hd : 2-D.rho≠0 := by linarith [D.rho_lt_one]
  rw [show 1+(1-D.rho)=2-D.rho by ring]
  field_simp [hg,hd]
  ring

theorem tmm_a_identity (D : Robust.Design) (hT : D.kappa*(1-D.rho)^2=1) :
    (1/2-D.tau)/(1-D.rho)=(2+3*D.rho)/(2*(2+D.rho-D.rho^2)) := by
  rw [D.tmm_deficit hT]
  field_simp [D.gap_pos.ne']

theorem tmm_b_identity (D : Robust.Design) (hT : D.kappa*(1-D.rho)^2=1) :
    (2-D.step)/(1-D.rho)=1 := by
  rw [D.tmm_step hT]
  have hh : 2-(1+D.rho)=1-D.rho := by ring
  rw [hh,div_self D.gap_pos.ne']

theorem tmm_a_remainder (D : Robust.Design) (hT : D.kappa*(1-D.rho)^2=1) :
    (1/2-D.tau)/(1-D.rho)=5/4+
      (1-D.rho)*(5*(1-D.rho)-11)/(4*(2+D.rho-D.rho^2)) := by
  rw [D.tmm_a_identity hT]
  have hd : 2+D.rho-D.rho^2≠0 := by
    have hp := mul_pos (show 0<1+D.rho by linarith [D.rho_pos])
      (show 0<2-D.rho by linarith [D.rho_lt_one])
    nlinarith
  field_simp [hd]
  ring

variable {A : Type*} {l : Filter A} (D : A→Robust.Design)
    (hT : ∀ a,(D a).kappa*(1-(D a).rho)^2=1)
    (hρ : Tendsto (fun a=>(D a).rho) l (𝓝 1))
include hT hρ

theorem tmm_theta_tendsto :
    Tendsto (fun a=>(1-(D a).beta)/(1-(D a).rho)) l (𝓝 3) := by
  have hc : ContinuousAt (fun x : ℝ=>(3-(1-x))/(1+(1-x))) 1 := by fun_prop (disch := norm_num)
  convert hc.tendsto.comp hρ using 1
  · funext a
    exact (D a).tmm_theta_identity (hT a)
  · norm_num

theorem tmm_step_tendsto : Tendsto (fun a=>(D a).step) l (𝓝 2) := by
  convert (tendsto_const_nhds (x:=(1:ℝ))).add hρ using 1
  · funext a
    exact (D a).tmm_step (hT a)
  · norm_num

theorem tmm_tau_tendsto : Tendsto (fun a=>(D a).tau) l (𝓝 (1/2)) := by
  have hc : ContinuousAt (fun x : ℝ=>x^2/((1+x)*(2-x))) 1 := by fun_prop (disch := norm_num)
  convert hc.tendsto.comp hρ using 1
  · funext a
    exact (D a).tmm_tau (hT a)
  · norm_num

theorem tmm_a_tendsto :
    Tendsto (fun a=>(1/2-(D a).tau)/(1-(D a).rho)) l (𝓝 (5/4)) := by
  have hc : ContinuousAt (fun x : ℝ=>(2+3*x)/(2*(2+x-x^2))) 1 := by fun_prop (disch := norm_num)
  convert hc.tendsto.comp hρ using 1
  · funext a
    exact (D a).tmm_a_identity (hT a)
  · norm_num

omit hρ in
 theorem tmm_b_tendsto :
    Tendsto (fun a=>(2-(D a).step)/(1-(D a).rho)) l (𝓝 1) := by
  convert tendsto_const_nhds using 1
  funext a
  exact (D a).tmm_b_identity (hT a)

theorem tmm_deficit_isBigO :
    (fun a=>(1/2-(D a).tau)-5/4*(1-(D a).rho)) =O[l]
      (fun a=>(1-(D a).rho)^2) := by
  let C : ℝ→ℝ := fun x=>(5*(1-x)-11)/(4*(2+x-x^2))
  have hc : ContinuousAt C 1 := by dsimp [C];fun_prop (disch := norm_num)
  have hb := (hc.tendsto.comp hρ).isBigO_one ℝ
  have hm := (Asymptotics.isBigO_refl (fun a=>(1-(D a).rho)^2) l).mul hb
  have he (a : A) : (1/2-(D a).tau)-5/4*(1-(D a).rho)=
      (1-(D a).rho)^2*C ((D a).rho) := by
    calc
      _=(1-(D a).rho)*((1/2-(D a).tau)/(1-(D a).rho)-5/4) := by
        field_simp [(D a).gap_pos.ne']
      _=_ := by rw [(D a).tmm_a_remainder (hT a)];dsimp [C];ring
  simpa only [Function.comp_def,mul_one,←he] using hm

end
end nesterov.Robust.Design
