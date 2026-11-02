import krylov.Nonlinear.RFCSLocality
import krylov.Nonlinear.AveragedComparison

/-!
Article: main_krylov, thm:RFCS, actual nonlinear averaged-Hessian dictionary.
Use: Identify the genuine finite-probe nonlinear RFC-S transcript with the
original operator run using the actual averaged derivatives on its queried
probe and full-step segments, once those real queries have been localized.
Source: the reused exact averaged-derivative FTC, convex segment enclosure,
genuine measured nonlinear execution and Bochner integral norm bounds.
-/

namespace krylov.Nonlinear
noncomputable section
open Set krylov.Methods chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine averaged derivative on the actual nonlinear RFC-S total evaluated step.
Use: Retain the actual physical segment, including its real model correction.
Article: main_krylov, thm:RFCS, real averaged-Hessian source realization.
-/
def rfcSFunctionSegment (memory : ℕ → ℕ) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (h : ℕ → ℝ) (i : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (rfcSFunctionPoint memory G x₀ h i)
    (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step

/-- The genuine averaged derivative on the actual finite nonlinear RFC-S probe segment.
Use: Identify the measured finite difference with its true integral operator, including arbitrarily short positive probes.
Article: main_krylov, thm:RFCS, real averaged-Hessian source realization.
-/
def rfcSFunctionProbeOperator (memory : ℕ → ℕ) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (h : ℕ → ℝ) (i : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (rfcSFunctionPoint memory G x₀ h i)
    (h i • windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
      (rfcSFunctionRun memory G x₀ h i).gradient)

/-- Every genuinely localized finite nonlinear RFC-S history is exactly its original operator execution with the real averaged derivatives of its actual full steps and finite probes.
Use: Apply the original operator expansion to the genuine function trajectory after actual query localization.
Article: main_krylov, thm:RFCS, real averaged-Hessian source realization.
Proof: Convexity encloses every real query segment. The reused exact FTC identifies its measured full-step and nonzero finite-probe actions. The proved complete measured-transcript dictionary identifies the entire actual run.
-/
theorem rfcSFunctionRun_averaged (memory : ℕ → ℕ) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (h : ℕ → ℝ) (N : ℕ) (S : Set E) (hS : Convex ℝ S)
    (hH : ContinuousOn H S) (hG : ∀ x∈S, HasFDerivAt G (H x) x)
    (hh : ∀ i<N, h i≠0) (hpoint : ∀ i≤N, rfcSFunctionPoint memory G x₀ h i∈S)
    (hprobe : ∀ i<N, rfcSFunctionPoint memory G x₀ h i+h i •
      windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
        (rfcSFunctionRun memory G x₀ h i).gradient∈S) :
    rfcSFunctionRun memory G x₀ h N=
      rfcSRun memory (rfcSFunctionProbeOperator memory G H x₀ h)
        (rfcSFunctionSegment memory G H x₀ h) (rfcSFunctionSegment memory G H x₀ h) (G x₀) N := by
  apply rfcSFunctionRun_operator
  · intro i hi
    have hp t (ht : t∈Icc (0 : ℝ) 1) := hS.add_smul_mem (hpoint i hi.le) (hprobe i hi) ht
    have ha := hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    have he := averaged_probe_secant G H (rfcSFunctionPoint memory G x₀ h i)
      (windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
        (rfcSFunctionRun memory G x₀ h i).gradient) (hh i hi) ha (fun t ht => hG _ (hp t ht))
    rw [rfcSFunctionRecord_probe]
    simpa only [rfcSFunctionProbeOperator,rfcSFunctionRun_gradient,rfcSFunctionPoint] using he.symm
  · intro i hi
    have hs : rfcSFunctionPoint memory G x₀ h i+
        (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step∈S := by
      rw [← rfcSFunctionPoint_succ]
      exact hpoint (i+1) (by omega)
    have hp t (ht : t∈Icc (0 : ℝ) 1) := hS.add_smul_mem (hpoint i hi.le) hs ht
    have ha := hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    have he := averagedDerivative_apply G H (rfcSFunctionPoint memory G x₀ h i)
      (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step ha
      (fun t ht => hG _ (hp t ht))
    rw [rfcSFunctionRecord_gradient,rfcSFunctionRun_gradient]
    exact he

/-- A uniform genuine derivative perturbation bound on an actual enclosed segment gives the same bound for its true averaged operator.
Use: Bound the actual nonlinear source profile from the real local Hessian perturbations.
Article: main_krylov, thm:RFCS, real averaged-Hessian source realization.
Proof: Move the fixed operator inside the genuine Bochner segment integral and apply its proved integral norm bound over the unit interval.
-/
theorem averagedDerivative_sub_const_norm_le (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (x s : E) {η : ℝ} (hH : ContinuousOn (fun t : ℝ => H (x+t • s)) (Icc 0 1))
    (hb : ∀ t∈Icc (0 : ℝ) 1, ‖H (x+t • s)-Q‖≤η) :
    ‖averagedDerivative H x s-Q‖≤η := by
  have hint := hH.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ)≤1)
  have he : averagedDerivative H x s-Q=∫ t in (0 : ℝ)..1, (H (x+t • s)-Q) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,intervalIntegral.integral_const]
    simp [averagedDerivative]
  rw [he]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => H (x+t • s)-Q) (C := η) (by
      intro t ht
      have ht' : t∈Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ)≤1)] using ht
      exact hb t ⟨ht'.1.le,ht'.2⟩)
  simpa only [sub_zero,abs_one,mul_one] using hn

end
end krylov.Nonlinear
