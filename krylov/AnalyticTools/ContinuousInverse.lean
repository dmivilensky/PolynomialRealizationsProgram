import krylov.AnalyticTools.LocalInverse
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Compact

/-!
Article: main_krylov, apC:prop:LV, rational path fields near the saddle.
Use: evaluate the actual Banach-algebra inverse pointwise and expose its
analyticity at invertible paths. Nonvanishing is required on the whole compact
path; no pointwise inverse is declared continuous through zeros.
Source: mathlib's continuous-map units and analytic normed-algebra inversion.
-/

namespace krylov.AnalyticTools
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- The algebra inverse agrees pointwise with scalar reciprocal at unit paths. -/
theorem inverse_continuousMap_apply {f : C(X, ℝ)} (hf : IsUnit f) (x : X) :
    Ring.inverse f x = (f x)⁻¹ := by
  have hn : f x ≠ 0 := (ContinuousMap.isUnit_iff_forall_ne_zero f).mp hf x
  have he := congrArg (fun g : C(X, ℝ) ↦ g x) (Ring.inverse_mul_cancel f hf)
  have he' : Ring.inverse f x * f x = 1 := by simpa using he
  calc
    Ring.inverse f x = (Ring.inverse f x * f x) / f x := by field_simp
    _ = (f x)⁻¹ := by rw [he', one_div]

theorem analyticAt_continuousMap_inverse {f : C(X, ℝ)} (hf : IsUnit f) :
    AnalyticAt ℝ (Ring.inverse : C(X, ℝ) → C(X, ℝ)) f := by
  simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hf.unit)

omit [CompactSpace X] in
theorem isUnit_continuousMap_const {c : ℝ} (hc : c ≠ 0) :
    IsUnit (ContinuousMap.const X c) :=
  (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr fun _ ↦ hc

end
end krylov.AnalyticTools
