import polyak.Boundary.P5.CriticalDual
import polyak.Boundary.P5.Contacts
import polyak.Boundary.P5.LocalImplicit

/-!
Article: Theorem p5local, persistence of dual nonnegativity along the actual analytic branch.
Use: exact double contacts, true continuous residual coefficients and the proved
critical reserve give all-frequency dual positivity near h=0.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Polynomial Filter
open scoped Topology

/-- Article: the moving main atom in the original regularization. -/
def branchMain (h : ℝ) : ℝ := -1/2+h*localBranch h 1
/-- Article: the moving auxiliary atom in the original regularization. -/
def branchAux (h : ℝ) : ℝ := localBranch h 2
/-- Article: the actual unscaled dual coefficient along the analytic branch. -/
def branchCoefficient (n : ℕ) (h : ℝ) : ℝ := (dualReal h (localBranch h)).coeff n
/-- Article: the exact quadratic residual's leading coefficient. -/
def branchResidual₂ (h : ℝ) : ℝ := branchCoefficient 6 h
/-- Article: the exact quadratic residual's linear coefficient. -/
def branchResidual₁ (h : ℝ) : ℝ :=
  branchCoefficient 5 h+2*(branchMain h+branchAux h)*branchCoefficient 6 h
/-- Article: the exact quadratic residual's constant coefficient. -/
def branchResidual₀ (h : ℝ) : ℝ :=
  branchCoefficient 4 h+2*(branchMain h+branchAux h)*branchCoefficient 5 h+
    (3*branchMain h^2+4*branchMain h*branchAux h+3*branchAux h^2)*branchCoefficient 6 h

/-- Article: the actual source coefficients are continuous along the true implicit branch. -/
theorem branchCoefficient_continuousAt (n : ℕ) : ContinuousAt (branchCoefficient n) 0 := by
  exact ContinuousAt.comp (f := fun h : ℝ => (h,localBranch h))
    (dualReal_coeff_analyticAt n (0,localBranch 0)).continuousAt
    (continuousAt_id.prodMk localBranch_analyticAt.continuousAt)

/-- Article: the exact residual has the certified critical values, including the common scale 15. -/
theorem branchResidual_zero :
    branchResidual₂ 0=15*q2₀ ∧ branchResidual₁ 0=15*q1₀ ∧ branchResidual₀ 0=15*q0₀ := by
  obtain ⟨h6,h5,h4⟩ := dualReal_critical_coefficients
  obtain ⟨hq2,hq1,hq0⟩ := critical_residual_coefficients
  simp only [branchResidual₂,branchResidual₁,branchResidual₀,branchCoefficient,branchMain,
    branchAux,localBranch_zero,zero_mul,add_zero,criticalPoint_2,h6,h5,h4]
  refine ⟨hq2,?_,?_⟩
  · convert hq1 using 1
    ring
  · convert hq0 using 1
    ring

/-- Article: a strict coefficient reserve persists on an actual neighborhood of the critical parameter. -/
theorem eventually_branchResidual_reserve :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0<branchResidual₀ h-|branchResidual₁ h|-|branchResidual₂ h| := by
  have hm : ContinuousAt branchMain 0 := by
    have hz := (continuous_apply (1 : Fin 7)).continuousAt.comp localBranch_analyticAt.continuousAt
    unfold branchMain
    fun_prop
  have hy : ContinuousAt branchAux 0 :=
    (continuous_apply (2 : Fin 7)).continuousAt.comp localBranch_analyticAt.continuousAt
  have h4 := branchCoefficient_continuousAt 4
  have h5 := branchCoefficient_continuousAt 5
  have h6 := branchCoefficient_continuousAt 6
  have hr : ContinuousAt (fun h => branchResidual₀ h-|branchResidual₁ h|-|branchResidual₂ h|) 0 := by
    unfold branchResidual₀ branchResidual₁ branchResidual₂
    fun_prop
  have hp : 0<branchResidual₀ 0-|branchResidual₁ 0|-|branchResidual₂ 0| := by
    obtain ⟨h2,h1,h0⟩ := branchResidual_zero
    rw [h0,h1,h2,abs_mul,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<15)]
    nlinarith [critical_dual_residual_gap]
  exact continuousAt_const.eventually_lt hr hp

/-- Article: the actual local simplex weights, main mass and distinct atoms remain admissible. -/
theorem eventually_branch_dual_parameters :
    ∀ᶠ h in 𝓝 (0 : ℝ),
      0<localBranch h 5 ∧ 0<localBranch h 6 ∧ 0<1-localBranch h 5-localBranch h 6 ∧
      h*localBranch h 3<1 ∧ branchMain h<1 ∧ branchMain h<branchAux h := by
  have hz (i : Fin 7) : ContinuousAt (fun h => localBranch h i) 0 :=
    (continuous_apply i).continuousAt.comp localBranch_analyticAt.continuousAt
  have hzero : localBranch 0=criticalPoint := localBranch_zero
  have hw5 : 0<1-localBranch 0 5-localBranch 0 6 := by
    rw [hzero]
    norm_num only [criticalPoint_5,criticalPoint_6]
    linarith [critical_weights_sum,w5₀_bounds.1]
  have hm : ContinuousAt branchMain 0 := by unfold branchMain; fun_prop
  have hy : ContinuousAt branchAux 0 := hz 2
  have hw2 := continuousAt_const.eventually_lt (hz 5)
    (by simpa only [hzero,criticalPoint_5] using w2₀_bounds.1)
  have hw3 := continuousAt_const.eventually_lt (hz 6)
    (by simpa only [hzero,criticalPoint_6] using w3₀_bounds.1)
  have hw₅ := continuousAt_const.eventually_lt
    ((continuousAt_const.sub (hz 5)).sub (hz 6)) hw5
  have hp := (continuousAt_id.mul (hz 3)).eventually_lt continuousAt_const
    (by norm_num : (0 : ℝ)*localBranch 0 3<1)
  have hx : ∀ᶠ h in 𝓝 (0 : ℝ), branchMain h<1 :=
    hm.eventually_lt continuousAt_const (by norm_num [branchMain])
  have hxy := hm.eventually_lt hy
    (by simpa only [branchMain,branchAux,hzero,zero_mul,add_zero,criticalPoint_2]
      using (show (-1/2 : ℝ)<y₀ by linarith [y₀_bounds.1]))
  filter_upwards [hw2,hw3,hw₅,hp,hx,hxy] with h h2 h3 h5 hp hx hxy
  exact ⟨h2,h3,h5,hp,hx,hxy⟩

/-- Article: every nearby nonnegative parameter has a nonnegative actual source dual on all frequencies. -/
theorem localBranch_dual_nonneg :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0≤h → ∀ c : Frequency, 0≤(dualReal h (localBranch h)).eval (c : ℝ) := by
  filter_upwards [localBranch_equations,eventually_branch_dual_parameters,
    eventually_branchResidual_reserve] with h hz hp hr hh c
  obtain ⟨h2,h3,h5,hp,hx,hxy⟩ := hp
  obtain ⟨hy,hdx,hdy⟩ := regularSystem_dual_exact h (localBranch h)
  rw [hz] at hy hdx hdy
  have hf := hermite_sextic_eval (dualReal_natDegree h (localBranch h)) (ne_of_lt hxy)
    (dualReal_main_root hh hz hp hx) hdx.symm hy.symm hdy.symm (c : ℝ)
  have hf' : (dualReal h (localBranch h)).eval (c : ℝ)=
    ((c : ℝ)-branchMain h)^2*((c : ℝ)-branchAux h)^2*
      (branchResidual₂ h*(c : ℝ)^2+branchResidual₁ h*c+branchResidual₀ h) := by
    simpa only [branchResidual₂,branchResidual₁,branchResidual₀,branchCoefficient,add_assoc] using hf
  rw [hf']
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (quadratic_pos_on_frequency hr c).le

end polyak.Boundary.P5
