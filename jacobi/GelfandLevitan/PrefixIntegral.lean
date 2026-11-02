import jacobi.GelfandLevitan.CutoffFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib's subtype measure and indicator-integral identities.
Use: converts the literal GL transformation integral to real-variable integration in GelfandLevitan.NegativeComparison and later spatial derivative arguments.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Set MeasureTheory jacobi.Reference
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual subtype prefix integral is exactly the original real interval integral for every Banach-valued integrand.
Use: converts the literal GL transformation integral to real-variable integration in GelfandLevitan.NegativeComparison and later spatial derivative arguments.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: subtype Lebesgue measure and the indicator formula for Bochner integration.
Proof: the subtype prefix indicator is the pullback of the real [0,t]
indicator. The subtype integral is the real [0,1] integral, whose
intersection with [0,t] is [0,t]. Null endpoints identify it with
the actual interval integral. -/
theorem prefix_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : ℝ → E) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (∫ r : Interval in prefixSet t,G (r:ℝ))=∫ s in (0:ℝ)..t,G s := by
  -- The physical subtype has its original measure, and the two indicators agree at every point of that domain.
  rw [← integral_indicator (prefixSet_measurable t)]
  have he : (fun r : Interval => (prefixSet t).indicator (fun r : Interval => G (r:ℝ)) r)=
      (fun r : Interval => (Icc (0:ℝ) t).indicator G (r:ℝ)) := by
    funext r
    have hmem : r∈prefixSet t ↔ (r:ℝ)∈Icc (0:ℝ) t :=
      ⟨fun hr => ⟨r.property.1,hr⟩,fun hr => hr.2⟩
    by_cases hr : r∈prefixSet t
    · rw [indicator_of_mem hr,indicator_of_mem (hmem.mp hr)]
    · rw [indicator_of_notMem hr,indicator_of_notMem (fun h => hr (hmem.mpr h))]
  rw [he,integral_subtype measurableSet_Icc,setIntegral_indicator measurableSet_Icc,
    inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2),integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le ht.1]

end
end jacobi.GelfandLevitan
