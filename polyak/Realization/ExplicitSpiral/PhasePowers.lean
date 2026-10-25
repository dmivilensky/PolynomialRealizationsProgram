import polyak.Realization.ExplicitSpiral.Phase

/-!
Article: the phase estimate for all three residue classes, uniformly in time.
Use: turn the finite near-critical quadratic signs into infinitely many
initialized interpolation inequalities.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the unit complex phase at a real angle. -/
def unitPhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)

/-- Article: the phase's real coordinate is the ordinary cosine. -/
theorem unitPhase_re (t : ℝ) : (unitPhase t).re=Real.cos t := by
  simp [unitPhase,Complex.exp_re]

/-- Article: the phase's imaginary coordinate is the ordinary sine. -/
theorem unitPhase_im (t : ℝ) : (unitPhase t).im=Real.sin t := by
  simp [unitPhase,Complex.exp_im]

/-- Article: phases have unit norm. -/
theorem norm_unitPhase (t : ℝ) : ‖unitPhase t‖=1 := by
  simp [unitPhase,Complex.norm_exp]

/-- Article: addition of real angles is multiplication of phases. -/
theorem unitPhase_add (t u : ℝ) : unitPhase (t+u)=unitPhase t*unitPhase u := by
  simp only [unitPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

/-- Article: the phase is one-Lipschitz in its real angle. -/
theorem unitPhase_lipschitz (t u : ℝ) : ‖unitPhase t-unitPhase u‖≤|t-u| := by
  have he : unitPhase t-unitPhase u=(unitPhase (t-u)-1)*unitPhase u := by
    rw [sub_mul,one_mul,← unitPhase_add,sub_add_cancel]
  rw [he,norm_mul,norm_unitPhase,mul_one]
  simpa only [unitPhase,mul_comm,Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=t-u))

/-- Article: every multiple of the critical three-step phase is exact. -/
theorem unitPhase_critical (j : ℕ) : unitPhase ((3*(j : ℝ))*(2*Real.pi/3))=1 := by
  have he : (((3*(j : ℝ))*(2*Real.pi/3) : ℝ) : ℂ)*Complex.I=
      (j : ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
  rw [unitPhase,he,Complex.exp_nat_mul_two_pi_mul_I]

/-- Article: phase error in the j-th complete cycle is bounded without truncating time. -/
theorem unitPhase_cycles {r : ℝ} (hr : 1≤r) (j : ℕ) :
    ‖unitPhase ((3*(j : ℝ))*Real.arccos (radialCosine r))-1‖≤
      (3*(j : ℝ))*phaseBudget r*Real.log r := by
  have hh := unitPhase_lipschitz ((3*(j : ℝ))*Real.arccos (radialCosine r))
    ((3*(j : ℝ))*(2*Real.pi/3))
  rw [unitPhase_critical] at hh
  have hn : 0≤3*(j : ℝ) := by positivity
  calc
    _ ≤ |(3*(j : ℝ))*Real.arccos (radialCosine r)-(3*(j : ℝ))*(2*Real.pi/3)| := hh
    _ = (3*(j : ℝ))*|Real.arccos (radialCosine r)-2*Real.pi/3| := by
      rw [← mul_sub,abs_mul,abs_of_nonneg hn]
    _ ≤ (3*(j : ℝ))*(phaseBudget r*Real.log r) :=
      mul_le_mul_of_nonneg_left (phase_error_le hr) hn
    _ = _ := by ring

/-- Article: uniform perturbation from a residue's phase, for every index 3j+a. -/
theorem unitPhase_residue {r : ℝ} (hr : 1≤r) (j a : ℕ) :
    ‖unitPhase (((3*j+a : ℕ) : ℝ)*Real.arccos (radialCosine r))-
      unitPhase ((a : ℝ)*Real.arccos (radialCosine r))‖≤
      phaseBudget r*Real.log (r^(3*j+a)) := by
  have he : (((3*j+a : ℕ) : ℝ)*Real.arccos (radialCosine r))=
      (3*(j : ℝ))*Real.arccos (radialCosine r)+(a : ℝ)*Real.arccos (radialCosine r) := by
    push_cast; ring
  rw [he,unitPhase_add]
  have hf (x y : ℂ) : x*y-y=(x-1)*y := by ring
  rw [hf,norm_mul,norm_unitPhase,mul_one]
  have hp : 0≤phaseBudget r*Real.log r := by
    apply mul_nonneg
    · unfold phaseBudget
      have hsq : 0≤r^2-1 := by nlinarith
      positivity
    · exact Real.log_nonneg hr
  calc
    _ ≤ (3*(j : ℝ))*phaseBudget r*Real.log r := unitPhase_cycles hr j
    _ ≤ ((3*j+a : ℕ) : ℝ)*(phaseBudget r*Real.log r) := by
      push_cast; nlinarith [show (0 : ℝ)≤a by positivity]
    _ = _ := by rw [Real.log_pow]; ring

end
end polyak.Realization.ExplicitSpiral
