import krylov.Nonlinear.RFCSFunctionFields
import krylov.Nonlinear.RFCSAveraged
import krylov.Nonlinear.CoordinateLipschitz
import krylov.Nonlinear.LastProbeAlgebra

/-!
Article: main_krylov, thm:RFCS, genuine canonical nonlinear probe/full-step comparison.
Use: Preserve the original actual last-probe coefficient under genuine local function and measured-search estimates.
Source: exact actual averaged-Hessian congruence, convex query enclosure and proved scalar/norm inequalities.
-/

namespace krylov.Nonlinear
noncomputable section
open Set krylov.Methods chebyshev1.Nonlinear
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual canonical nonlinear RFC-S averaged-Hessian mismatch obeys the exact one-half local Lipschitz bound with its real relative probe error, genuine line displacement and actual physical correction.
Use: Apply self-concordant canonical Hessian control directly to the true function requests without a fictitious operator scenario.
Article: main_krylov, thm:RFCS, actual nonlinear last-probe leading coefficient.
Proof: Reconstruct actual physical Hessian continuity from the canonical bound. Convexity encloses the genuine full-step and finite-probe paths using their real endpoints. Exact averaged-operator congruence transfers both actual averages to canonical coordinates; the real relative-probe mismatch inequality retains the literal executed search error.
-/
theorem rfcSFunction_canonical_mismatch_bound (T : E ≃L[ℝ] E)
    (memory : ℕ → ℕ) (G : E → E) (H : E → E →L[ℝ] E) (x₀ : E) (h : ℕ → ℝ) (i : ℕ)
    {S : Set E} (hS : Convex ℝ S) {L : ℝ≥0} (hL : LipschitzOnWith L (coordinateDerivative T H) S)
    (hα : 0<rfcSFunctionAlpha memory G x₀ h i)
    (hx : T (rfcSFunctionPoint memory G x₀ h i)∈S)
    (hx' : T (rfcSFunctionPoint memory G x₀ h (i+1))∈S)
    (hp : T (rfcSFunctionPoint memory G x₀ h i+h i • windowDirection
      (selectedWindow memory (rfcSFunctionRun memory G x₀ h i)) (rfcSFunctionRun memory G x₀ h i).gradient)∈S) :
    ‖coordinateCongruence T (rfcSFunctionSegment memory G H x₀ h i-rfcSFunctionProbeOperator memory G H x₀ h i)‖≤
      (L : ℝ)/2*(|1-h i/rfcSFunctionAlpha memory G x₀ h i| *‖T (rfcSFunctionLineStep memory G x₀ h i)‖+
        ‖T (rfcSFunctionCorrection memory G x₀ h i)‖) := by
  let x := rfcSFunctionPoint memory G x₀ h i
  let d := windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i)) (rfcSFunctionRun memory G x₀ h i).gradient
  let s := (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step
  let α := rfcSFunctionAlpha memory G x₀ h i
  let c := rfcSFunctionCorrection memory G x₀ h i
  have hline : rfcSFunctionLineStep memory G x₀ h i=α • d := by
    rw [rfcSFunctionLineStep,rfcSFunctionRecord_direction]
  have hs : s=α • d+c := by
    change s=α • d+(s-rfcSFunctionLineStep memory G x₀ h i)
    rw [hline]
    abel
  have hend : T (x+s)∈S := by
    change T (rfcSFunctionPoint memory G x₀ h i+
      (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step)∈S
    rw [← rfcSFunctionPoint_succ]
    exact hx'
  have hphysical := coordinateDerivative_lipschitz_pullback T H hL
  have hpath t (ht : t∈Icc (0 : ℝ) 1) : x+t • s∈T ⁻¹' S := by
    simp only [Set.mem_preimage,map_add,map_smul]
    apply hS.add_smul_mem hx _ ht
    simpa only [map_add] using hend
  have hprobe t (ht : t∈Icc (0 : ℝ) 1) : x+t • (h i • d)∈T ⁻¹' S := by
    simp only [Set.mem_preimage,map_add,map_smul]
    apply hS.add_smul_mem hx _ ht
    simpa only [map_add,map_smul] using hp
  have hcfull := hphysical.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hpath
  have hcprobe := hphysical.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hprobe
  have hfullcan t (ht : t∈Icc (0 : ℝ) 1) : T x+t • (α • T d+T c)∈S := by
    have hh := hpath t ht
    change T (x+t • s)∈S at hh
    simpa only [hs,map_add,map_smul] using hh
  have hprobecan t (ht : t∈Icc (0 : ℝ) 1) : T x+t • (h i • T d)∈S := by
    have hh := hprobe t ht
    change T (x+t • (h i • d))∈S at hh
    simpa only [map_add,map_smul] using hh
  have hb := averaged_probe_relative_mismatch (coordinateDerivative T H) (T x) (T d) (T c) α (h i) hL hα hfullcan hprobecan
  have he : ‖coordinateCongruence T (rfcSFunctionSegment memory G H x₀ h i-rfcSFunctionProbeOperator memory G H x₀ h i)‖=
      ‖averagedDerivative (coordinateDerivative T H) (T x) (α • T d+T c)-
        averagedDerivative (coordinateDerivative T H) (T x) (h i • T d)‖ := by
    change ‖coordinateCongruence T (averagedDerivative H x s-averagedDerivative H x (h i • d))‖=_
    rw [map_sub,← averagedDerivative_coordinate_operator T H x s hcfull,
      ← averagedDerivative_coordinate_operator T H x (h i • d) hcprobe,hs,map_add,map_smul,map_smul]
  rw [he]
  simpa only [hline,map_smul] using hb

end
end krylov.Nonlinear
