import krylov.Completion.PhysicalTrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), exact attained physical damping minimax.
Use: optimize the original positive DC estimate over genuine matrix
completions, retaining both attained physical endpoint scenarios.
Source: the proved scalar arithmetic equioscillation and the true positive
reciprocal curvature/step interval; singleton intervals are included.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.OneGradient
variable {n : ℕ}

/-- The true worst residual multiplier over a physical completion family is
exactly the maximum at its two actual attained curvature endpoints.
Use: the DC damping problem quantifies over original matrices rather than
merely a scalar interval that could contain unrealizable scenarios.
Article: main_krylov, thm:dcs(c).
Proof: positive reciprocal order bounds every real searched length; the two
genuine endpoint completions attain the scalar endpoint maximum. -/
theorem physical_damping_worst
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi : ℝ)
    (hq : 0<q) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi)
    (t : ℝ) (ht : 0<t) :
    IsGreatest ((fun A => |1-physicalTrialLength d q A/t|) '' C)
      (dampingEndpointError (q/hi) (q/lo) t) := by
  have hhi : 0<hi := hlo.trans_le horder
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  constructor
  · obtain ⟨Alo,hAlo,hclo⟩ := (hrange lo).mpr ⟨le_rfl,horder⟩
    obtain ⟨Ahi,hAhi,hchi⟩ := (hrange hi).mpr ⟨horder,le_rfl⟩
    rcases le_total |q/hi/t-1| |q/lo/t-1| with h|h
    · refine ⟨Alo,hAlo,?_⟩
      change |1-physicalTrialLength d q Alo/t|=_
      rw [physicalTrialLength,hclo,abs_sub_comm,dampingEndpointError,max_eq_right h]
    · refine ⟨Ahi,hAhi,?_⟩
      change |1-physicalTrialLength d q Ahi/t|=_
      rw [physicalTrialLength,hchi,abs_sub_comm,dampingEndpointError,max_eq_left h]
  · rintro z ⟨A,hA,rfl⟩
    have hcurv := (hrange _).mp ⟨A,hA,rfl⟩
    have hcpos : 0<d ⬝ᵥ (A*ᵥ d) := hlo.trans_le hcurv.1
    change |1-physicalTrialLength d q A/t|≤_
    rw [abs_sub_comm]
    exact damping_error_le_endpoints
      (div_le_div_of_nonneg_left hq.le hcpos hcurv.2)
      (div_le_div_of_nonneg_left hq.le hlo hcurv.1) ht

/-- The original positive DC estimate problem on a genuine physical completion
family has the exact attained arithmetic-step minimax, with a unique estimate.
Use: the source curvature completion theorems supply the actual range, even
when endpoints coincide or shifted old forms are singular.
Article: main_krylov, thm:dcs(c), unique minimax damping estimate.
Proof: every positive real estimate has the proved actual attained endpoint
maximum. Genuine scalar arithmetic equioscillation supplies the attained
minimum and uniqueness; positive reciprocal algebra gives the printed
curvature arithmetic-mean estimate and condition-ratio value. -/
theorem physical_damping_minimax
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi : ℝ)
    (hq : 0<q) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi) :
    IsLeast {v : ℝ | ∃ t : ℝ,0<t ∧ IsGreatest ((fun A => |1-physicalTrialLength d q A/t|) '' C) v}
      ((hi-lo)/(hi+lo)) ∧
      (∀ t : ℝ,0<t → ((∀ A∈C,|1-physicalTrialLength d q A/t|≤(hi-lo)/(hi+lo)) ↔
        t=q*(lo⁻¹+hi⁻¹)/2)) := by
  have hhi : 0<hi := hlo.trans_le horder
  have ha : 0<q/hi := div_pos hq hhi
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  have hv := (harmonic_physical_curvature hlo hhi hq).2
  have he : arithmeticEstimate (q/hi) (q/lo)=q*(lo⁻¹+hi⁻¹)/2 := by
    unfold arithmeticEstimate
    ring
  have hw := physical_damping_worst C d q lo hi hq hlo horder hrange
  constructor
  · constructor
    · refine ⟨arithmeticEstimate (q/hi) (q/lo),(arithmetic_estimate_attains ha hab).1,?_⟩
      simpa only [(arithmetic_estimate_attains ha hab).2,hv] using
        hw _ (arithmetic_estimate_attains ha hab).1
    · rintro v ⟨t,ht,hvmax⟩
      have heq := hvmax.unique (hw t ht)
      rw [heq,← hv]
      exact arithmetic_estimate_lower_bound ha hab ht
  · intro t ht
    have hiff : (∀ A∈C,|1-physicalTrialLength d q A/t|≤(hi-lo)/(hi+lo)) ↔
        dampingEndpointError (q/hi) (q/lo) t≤ intervalMinimaxValue (q/hi) (q/lo) := by
      constructor
      · intro hb
        obtain ⟨A,hA,hval⟩ := (hw t ht).1
        rw [hv,← hval]
        exact hb A hA
      · intro hb A hA
        exact ((hw t ht).2 ⟨A,hA,rfl⟩).trans (hv ▸ hb)
    rw [hiff,arithmetic_estimate_unique ha hab ht,he]

end
end krylov.Completion
