import nesterov.Slow.Ceiling
import nesterov.Flow.Damping
import nesterov.Flow.LevelSets
import nesterov.Flow.Supporting

/-! Article: Corollary 5.3, actual-rate ceilings and necessary slow data. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Filter Flow
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

def quadraticCoefficient (ε : ℝ) : ℝ := (1-Rates.quadraticRate (F.method ε) (ε^2) 1)/ε

theorem quadratic_limsup_coefficient_le :
    limsup (fun ε=>(F.quadraticCoefficient ε:EReal)) (𝓝[>] (0:ℝ))≤(cQ θ y:EReal) := by
  by_contra h
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hr : cQ θ y<a := EReal.coe_lt_coe_iff.mp ha
  have he : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.quadraticCoefficient ε:EReal)≤(a:EReal) := by
    filter_upwards [F.quadratic_coefficient_eventually_le hr] with ε hε
    exact EReal.coe_le_coe_iff.mpr hε
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) he)) halim

theorem nonlinear_optimal_ceiling :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤(Real.sqrt (y/2):EReal) :=
  F.limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr (cF_le_optimal F.step_pos))

theorem pareto_ceiling :
    ∃ θ' : ℝ,2*Real.sqrt y≤θ' ∧ θ'≤3*Real.sqrt (y/2) ∧
      limsup (fun ε=>(F.quadraticCoefficient ε:EReal)) (𝓝[>] (0:ℝ))≤(cQ θ' y:EReal) ∧
      limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤((θ'/3:ℝ):EReal) ∧
      cF θ' y=θ'/3 := by
  obtain ⟨θ',hl,hu,hq,hf,he⟩ := pareto_domination F.theta_pos F.step_pos
  exact ⟨θ',hl,hu,F.quadratic_limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr hq),
    F.limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr hf),he⟩

theorem third_ceiling :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤((θ/3:ℝ):EReal) :=
  F.limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr (cF_le_third θ y))

theorem critical_ceiling (hθ : θ=2*Real.sqrt y) :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤((2*Real.sqrt y/3:ℝ):EReal) := by
  simpa only [hθ] using F.third_ceiling

theorem necessary_slow_data
    (h : (1:EReal)≤liminf (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))) :
    3≤θ ∧ θ-1≤y ∧ 2≤θ-1 ∧ 2≤y := by
  have hi : liminf (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤
      limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ)) := Filter.liminf_le_limsup
  have hr : 1≤cF θ y := EReal.coe_le_coe_iff.mp ((h.trans hi).trans F.limsup_coefficient_le)
  have hh := (le_cF_iff (show (0:ℝ)≤1 by norm_num) θ y).mp hr
  norm_num at hh
  exact ⟨hh.1,by linarith [hh.2],by linarith,by linarith [hh.1,hh.2]⟩

theorem standard_nesterov_data_ceiling (F : nesterov.Slow.SecondOrderFamily 2 1) :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤((2/3:ℝ):EReal) := F.third_ceiling

theorem quadratic_nesterov_data_ceiling (F : nesterov.Slow.SecondOrderFamily (4/Real.sqrt 3) (4/3)) :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤((4/(3*Real.sqrt 3):ℝ):EReal) := by
  convert F.third_ceiling using 1
  congr 1
  ring

end
end nesterov.Slow.SecondOrderFamily
