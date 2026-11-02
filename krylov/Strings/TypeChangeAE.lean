import krylov.Strings.TypeClockInverse
import krylov.Strings.TypeImage

/-!
Article: main_krylov, apC:eq:reduced.
Use: transfer physical almost-everywhere identities to the actual type
variable. The proof constructs a measurable good set and proves its image
has full type measure using the Jacobian formula. No continuity or positive
lower bound of the clock density is assumed.
Source: `type_image_full_measure` and the actual compact-window inverse.
-/

namespace krylov.Strings.TypeChange
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Almost-everywhere identities pass through a strictly increasing integral
clock. Crucially, the conclusion is almost everywhere in type, not merely
at images of an unspecified full physical set. -/
theorem ae_transfer {a b : ℝ} {Y v : ℝ → ℝ} {P : ℝ → Prop}
    (hab : a < b) (hm : StrictMonoOn Y (Icc a b)) (hi : IntervalIntegrable v volume a b)
    (hn : ∀ x ∈ Ioo a b, 0 ≤ v x)
    (htotal : Y b - Y a = ∫ x in a..b, v x)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt Y (v x) x)
    (hP : ∀ᵐ x, x ∈ Ioo a b → P x) :
    ∀ᵐ y, y ∈ Ioo (Y a) (Y b) → P (inverse Y a b y) := by
  let bad := {x : ℝ | ¬ (x ∈ Ioo a b → HasDerivAt Y (v x) x ∧ P x)}
  have hbad : volume bad = 0 := by
    apply ae_iff.mp
    filter_upwards [hd, hP] with x hx hxP hxin
    exact ⟨hx hxin, hxP hxin⟩
  let good := Ioo a b \ toMeasurable volume bad
  have hgood : MeasurableSet good := measurableSet_Ioo.diff (measurableSet_toMeasurable _ _)
  have hsub : good ⊆ Ioo a b := fun _ hx ↦ hx.1
  have hfull : volume (Ioo a b \ good) = 0 := by
    apply measure_mono_null (t := toMeasurable volume bad)
    · intro x hx
      by_contra h
      exact hx.2 ⟨hx.1, h⟩
    · rw [measure_toMeasurable, hbad]
  have hvalid : ∀ x ∈ good, HasDerivAt Y (v x) x ∧ P x := by
    intro x hx
    have hb : x ∉ bad := fun h ↦ hx.2 (subset_toMeasurable volume bad h)
    exact (not_not.mp hb) hx.1
  obtain ⟨_, himage⟩ := type_image_full_measure hab hm hi hn htotal hgood hsub hfull
    (fun x hx ↦ (hvalid x hx).1)
  have hae : ∀ᵐ y : ℝ, y ∉ Ioo (Y a) (Y b) \ Y '' good := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using himage
  filter_upwards [hae] with y hy hyt
  have hym : y ∈ Y '' good := by
    by_contra h
    exact hy ⟨hyt, h⟩
  obtain ⟨x, hx, rfl⟩ := hym
  rw [inverse_clock hm (Ioo_subset_Icc_self (hsub hx))]
  exact (hvalid x hx).2

end
end krylov.Strings.TypeChange
