import krylov.OneGradient.TrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, exact physical curvature-trial minimax.
Use: transfer a proved attained physical curvature interval to the original
minimax over real admissible matrix completions, including collapsed intervals.
Source: the already proved unique harmonic interval minimax, with the true
physical searched step derived from positive curvature and descent pairing.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.OneGradient
variable {n : ℕ}

/-- The original exact-search length of a genuine matrix along an actual
physical direction with the supplied positive negative gradient pairing.
Use: formulate the minimax over actual completion matrices rather than scalar surrogates.
Article: main_krylov, thm:radau, alpha(A')=-g^T d/(d^T A' d). -/
def physicalTrialLength (d : Fin n → ℝ) (q : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  q/(d ⬝ᵥ (A*ᵥ d))

/-- The exact attained worst trial error on a genuine physical matrix
completion family depends only on its proved attained positive curvature interval.
Use: both endpoints and every interior physical scenario remain in the source uncertainty class.
Article: main_krylov, thm:radau.
Proof: positive reciprocal order bounds every actual searched step; the actual
endpoint completions attain the two endpoint errors. The existing true interval
trial-error theorem supplies the upper bound for every original real trial. -/
theorem physical_trial_worst
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi : ℝ)
    (hq : 0<q) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi) (t : ℝ) :
    IsGreatest ((fun A => |1-t/physicalTrialLength d q A|) '' C)
      (trialEndpointError (q/hi) (q/lo) t) := by
  have hhi : 0<hi := hlo.trans_le horder
  have ha : 0<q/hi := div_pos hq hhi
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  constructor
  · obtain ⟨Alo,hAlo,hclo⟩ := (hrange lo).mpr ⟨le_rfl,horder⟩
    obtain ⟨Ahi,hAhi,hchi⟩ := (hrange hi).mpr ⟨horder,le_rfl⟩
    rcases le_total |1-t/(q/hi)| |1-t/(q/lo)| with h|h
    · refine ⟨Alo,hAlo,?_⟩
      change |1-t/physicalTrialLength d q Alo|=_
      rw [physicalTrialLength,hclo,trialEndpointError,max_eq_right h]
    · refine ⟨Ahi,hAhi,?_⟩
      change |1-t/physicalTrialLength d q Ahi|=_
      rw [physicalTrialLength,hchi,trialEndpointError,max_eq_left h]
  · rintro z ⟨A,hA,rfl⟩
    have hcurv := (hrange _).mp ⟨A,hA,rfl⟩
    have hcpos : 0<d ⬝ᵥ (A*ᵥ d) := hlo.trans_le hcurv.1
    exact trial_error_le_endpoints ha
      (div_le_div_of_nonneg_left hq.le hcpos hcurv.2)
      (div_le_div_of_nonneg_left hq.le hlo hcurv.1) t

/-- The original harmonic step interval trial is exactly the midpoint-curvature
rule along the actual physical descent direction.
Use: identify the article's two equivalent descriptions of the unique radau trial.
Article: main_krylov, thm:radau.
Proof: clear the strictly positive original curvature endpoints and their sum. -/
theorem harmonic_physical_curvature {q lo hi : ℝ} (hlo : 0<lo) (hhi : 0<hi) (hq : 0<q) :
    harmonicTrial (q/hi) (q/lo)=2*q/(lo+hi) ∧
      intervalMinimaxValue (q/hi) (q/lo)=(hi-lo)/(hi+lo) := by
  constructor
  · unfold harmonicTrial
    field_simp
  · unfold intervalMinimaxValue
    field_simp

/-- The original physical completion trial problem has the exact attained
midpoint-curvature minimax value over all real trials, with a unique minimizer.
Use: the theorem covers genuine physical window and full-action completion sets,
including coincident endpoints; its hypotheses are supplied by their proved range theorems.
Article: main_krylov, thm:radau, unique midpoint-curvature minimax.
Proof: every physical trial has the proved exact attained worst error. The
existing unique harmonic minimax and true positive reciprocal interval give
the real minimum; actual algebra identifies its midpoint-curvature formula. -/
theorem physical_trial_minimax
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi : ℝ)
    (hq : 0<q) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi) :
    IsLeast {v : ℝ | ∃ t : ℝ,IsGreatest ((fun A => |1-t/physicalTrialLength d q A|) '' C) v}
      ((hi-lo)/(hi+lo)) ∧
      (∀ t : ℝ,(∀ A∈C,|1-t/physicalTrialLength d q A|≤(hi-lo)/(hi+lo)) ↔ t=2*q/(lo+hi)) := by
  have hhi : 0<hi := hlo.trans_le horder
  have ha : 0<q/hi := div_pos hq hhi
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  obtain ⟨htrial,hvalue⟩ := harmonic_physical_curvature hlo hhi hq
  have hw := physical_trial_worst C d q lo hi hq hlo horder hrange
  constructor
  · constructor
    · refine ⟨2*q/(lo+hi),?_⟩
      rw [← htrial,← hvalue]
      simpa only [(harmonic_trial_attains ha hab).2] using hw (harmonicTrial (q/hi) (q/lo))
    · rintro v ⟨t,ht⟩
      have he : v=trialEndpointError (q/hi) (q/lo) t := ht.unique (hw t)
      rw [he,← hvalue]
      exact harmonic_trial_lower_bound ha hab t
  · intro t
    have hb : (∀ A∈C,|1-t/physicalTrialLength d q A|≤(hi-lo)/(hi+lo)) ↔
        trialEndpointError (q/hi) (q/lo) t≤(hi-lo)/(hi+lo) := by
      constructor
      · intro h
        obtain ⟨A,hA,he⟩ := (hw t).1
        rw [← he]
        exact h A hA
      · intro h A hA
        exact ((hw t).2 ⟨A,hA,rfl⟩).trans h
    rw [hb,← hvalue,harmonic_trial_unique ha hab,htrial]

end
end krylov.Completion
