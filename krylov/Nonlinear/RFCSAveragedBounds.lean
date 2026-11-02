import krylov.Nonlinear.RFCSAveraged
import krylov.Correction.RFCSOperatorCoordinates

/-!
Article: main_krylov, thm:RFCS, actual averaged-Hessian perturbation bounds.
Use: Transfer the original fixed-reference operator estimates to genuine nonlinear gradient requests with their actual local Hessian data.
Source: the proved actual query localization, exact averaged-derivative FTC, genuine compact source tubes and real field homogeneity.
-/

namespace krylov.Nonlinear
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Correction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every genuine localized nonlinear RFC-S probe and full-step averaged operator obeys the actual uniform local Hessian perturbation bound.
Use: Derive the true finite operator-source radius from the original function Hessian data.
Article: main_krylov, thm:RFCS, genuine nonlinear function remainder transfer.
Proof: Convexity encloses each actual probe and full-step segment; apply the proved genuine averaged-operator norm bound on those real paths.
-/
theorem rfcSFunction_averaged_operator_bounds (memory : ℕ → ℕ) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (h : ℕ → ℝ) (N : ℕ) (S : Set E) (hS : Convex ℝ S) (hH : ContinuousOn H S)
    (Q : E →L[ℝ] E) {η : ℝ} (hb : ∀ x∈S, ‖H x-Q‖≤η)
    (hpoint : ∀ i≤N, rfcSFunctionPoint memory G x₀ h i∈S)
    (hprobe : ∀ i<N, rfcSFunctionPoint memory G x₀ h i+h i •
      windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
        (rfcSFunctionRun memory G x₀ h i).gradient∈S) :
    ∀ i<N, ‖rfcSFunctionProbeOperator memory G H x₀ h i-Q‖≤η ∧
      ‖rfcSFunctionSegment memory G H x₀ h i-Q‖≤η := by
  intro i hi
  constructor
  · have hp t (ht : t∈Icc (0 : ℝ) 1) := hS.add_smul_mem (hpoint i hi.le) (hprobe i hi) ht
    have ha := hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    exact averagedDerivative_sub_const_norm_le H Q _ _ ha (fun t ht => hb _ (hp t ht))
  · have hs : rfcSFunctionPoint memory G x₀ h i+
        (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step∈S := by
      rw [← rfcSFunctionPoint_succ]
      exact hpoint (i+1) (by omega)
    have hp t (ht : t∈Icc (0 : ℝ) 1) := hS.add_smul_mem (hpoint i hi.le) hs ht
    have ha := hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    exact averagedDerivative_sub_const_norm_le H Q _ _ ha (fun t ht => hb _ (hp t ht))

end
end krylov.Nonlinear
