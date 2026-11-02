import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Article: `main_krylov`, `apC:eq:state`, passage to the actual type variable.
A measurable full-measure physical set of valid derivative identities has
full measure in type after a strictly increasing integral clock. The proof
uses the actual one-dimensional Jacobian formula on the good set, and the
total primitive increment, so no unproved null-image or inverse-regularity
assumption is inserted into the change of variables.
Source: mathlib `lintegral_deriv_eq_volume_image_of_monotoneOn`.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory

/-- A full physical derivative set occupies the full type interval. This is
the measure-theoretic bridge needed to transfer inverse derivative identities
from almost every physical point to almost every type point. -/
theorem type_image_full_measure {a b : ℝ} {Y v : ℝ → ℝ} {good : Set ℝ}
    (hab : a < b) (hY : StrictMonoOn Y (Icc a b))
    (hv : IntervalIntegrable v volume a b)
    (hv₀ : ∀ x ∈ Ioo a b, 0 ≤ v x)
    (htotal : Y b - Y a = ∫ x in a..b, v x)
    (hg : MeasurableSet good) (hsub : good ⊆ Ioo a b)
    (hfull : volume (Ioo a b \ good) = 0)
    (hderiv : ∀ x ∈ good, HasDerivAt Y (v x) x) :
    MeasurableSet (Y '' good) ∧ volume (Ioo (Y a) (Y b) \ Y '' good) = 0 := by
  have hmono : MonotoneOn Y good := hY.monotoneOn.mono (hsub.trans Ioo_subset_Icc_self)
  have himage : MeasurableSet (Y '' good) := hg.image_of_monotoneOn hmono
  have hsubset : Y '' good ⊆ Ioo (Y a) (Y b) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hsub hx
    exact ⟨hY ⟨le_rfl, hab.le⟩ ⟨hx'.1.le, hx'.2.le⟩ hx'.1,
      hY ⟨hx'.1.le, hx'.2.le⟩ ⟨hab.le, le_rfl⟩ hx'.2⟩
  have hsets : good =ᵐ[volume] Ioo a b := by
    rw [ae_eq_set]
    exact ⟨by rw [sdiff_eq_empty.mpr hsub, measure_empty], hfull⟩
  have hioc : IntegrableOn v (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hv
  have hig : IntegrableOn v good := hioc.mono_set (hsub.trans Ioo_subset_Ioc_self)
  have heq : volume (Y '' good) = ENNReal.ofReal (Y b - Y a) := by
    rw [← lintegral_deriv_eq_volume_image_of_monotoneOn hg
      (fun x hx ↦ (hderiv x hx).hasDerivWithinAt) hmono]
    rw [← ofReal_integral_eq_lintegral_ofReal hig]
    · rw [setIntegral_congr_set hsets, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hab.le, ← htotal]
    · filter_upwards [ae_restrict_mem hg] with x hx
      exact hv₀ x (hsub hx)
  refine ⟨himage, ?_⟩
  rw [measure_sdiff hsubset himage.nullMeasurableSet (by rw [heq]; exact ENNReal.ofReal_ne_top),
    Real.volume_Ioo, heq, tsub_self]

end
end krylov.Strings
