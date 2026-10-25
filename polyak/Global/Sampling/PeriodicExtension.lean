import polyak.Global.Sampling.Taylor
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Calculus.MeanValue

/-! Periodic extension preserves a matching value and first derivative.
The endpoint argument uses the actual two one-sided representatives. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Filter AddCommGroup
open scoped Topology

def periodicExtension {p : ℝ} (hp : 0<p) (f : ℝ→ℝ) (x : ℝ) : ℝ :=
  f (toIcoMod hp 0 x)

theorem periodicExtension_periodic {p : ℝ} (hp : 0<p) (f : ℝ→ℝ) :
    Function.Periodic (periodicExtension hp f) p :=
  (toIcoMod_periodic hp 0).comp f

theorem periodicExtension_eq_ioc {p : ℝ} (hp : 0<p) {f : ℝ→ℝ}
    (he : f 0=f p) (x : ℝ) : periodicExtension hp f x=f (toIocMod hp 0 x) := by
  by_cases hx : (0:ℝ) ≡ x [PMOD p]
  · have hc := (modEq_iff_toIcoMod_eq_left hp).mp hx
    have ho := (modEq_iff_toIcoMod_add_period_eq_toIocMod hp).mp hx
    dsimp [periodicExtension]
    rw [hc,zero_add] at ho
    rw [hc,←ho,he]
  · unfold periodicExtension
    rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp).mp hx]

theorem hasDerivAt_periodicExtension {p : ℝ} (hp : 0<p) {f df : ℝ→ℝ}
    (hf : ∀x∈Icc 0 p,HasDerivAt f (df x) x)
    (he : f 0=f p) (hde : df 0=df p) (x : ℝ) :
    HasDerivAt (periodicExtension hp f) (periodicExtension hp df x) x := by
  have hc : toIcoMod hp 0 x∈Icc 0 p := by
    simpa only [zero_add] using Ico_subset_Icc_self (toIcoMod_mem_Ico hp 0 x)
  have ho : toIocMod hp 0 x∈Icc 0 p := by
    simpa only [zero_add] using Ioc_subset_Icc_self (toIocMod_mem_Ioc hp 0 x)
  have hright : HasDerivWithinAt (periodicExtension hp f)
      (periodicExtension hp df x) (Ici x) x := by
    have ht := (hf _ hc).comp (h:=fun y=>y-toIcoDiv hp 0 x • p) x ((hasDerivAt_id x).sub_const (toIcoDiv hp 0 x • p))
    simp only [mul_one] at ht
    apply ht.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventuallyEq_toIcoDiv_nhdsGE hp 0 x] with y hy
      simp only [periodicExtension,toIcoMod,hy,Function.comp_apply]
    · rfl
  have hleft : HasDerivWithinAt (periodicExtension hp f)
      (periodicExtension hp df x) (Iio x) x := by
    have ht := (hf _ ho).comp (h:=fun y=>y-toIocDiv hp 0 x • p) x ((hasDerivAt_id x).sub_const (toIocDiv hp 0 x • p))
    simp only [mul_one] at ht
    rw [←periodicExtension_eq_ioc hp hde x] at ht
    apply ht.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventuallyEq_toIcoDiv_nhdsLT hp 0 x] with y hy
      simp only [periodicExtension,toIcoMod,hy,Function.comp_apply]
    · exact periodicExtension_eq_ioc hp he x
  have hu:=hright.union hleft
  simpa only [Ici_union_Iio,hasDerivWithinAt_univ] using hu

@[fun_prop] theorem continuous_periodicExtension {p : ℝ} (hp : 0<p) {f : ℝ→ℝ}
    (he : f 0=f p) (hc : ContinuousOn f (Icc 0 p)) :
    Continuous (periodicExtension hp f) := by
  let : Fact (0<p) := ⟨hp⟩
  exact (AddCircle.liftIco_zero_continuous he hc).comp (AddCircle.continuous_mk' p)

theorem hasDerivWithinAt_periodicExtension_right {p : ℝ} (hp : 0<p) {f df : ℝ→ℝ}
    (hf : ∀x∈Ico 0 p,HasDerivWithinAt f (df x) (Ici x) x) (x : ℝ) :
    HasDerivWithinAt (periodicExtension hp f) (periodicExtension hp df x) (Ici x) x := by
  have hc : toIcoMod hp 0 x∈Ico 0 p := by
    simpa only [zero_add] using toIcoMod_mem_Ico hp 0 x
  have ht := (hf _ hc).comp (h:=fun y=>y-toIcoDiv hp 0 x • p) x
    (show HasDerivWithinAt (fun y=>y-toIcoDiv hp 0 x • p) 1 (Ici x) x from
      ((hasDerivAt_id x).sub_const (toIcoDiv hp 0 x • p)).hasDerivWithinAt)
    (by intro y hy; change x-toIcoDiv hp 0 x • p≤y-toIcoDiv hp 0 x • p; exact sub_le_sub_right hy _)
  simp only [mul_one] at ht
  apply ht.congr_of_eventuallyEq
  · filter_upwards [eventuallyEq_toIcoDiv_nhdsGE hp 0 x] with y hy
    simp only [periodicExtension,toIcoMod,hy,Function.comp_apply]
  · rfl

theorem periodicExtension_lipschitz {p M : ℝ} (hp : 0<p) {f df : ℝ→ℝ}
    (he : f 0=f p) (hc : ContinuousOn f (Icc 0 p))
    (hf : ∀x∈Ico 0 p,HasDerivWithinAt f (df x) (Ici x) x)
    (hb : ∀x∈Ico 0 p,|df x|≤M) (x y : ℝ) :
    |periodicExtension hp f x-periodicExtension hp f y|≤M*|x-y| := by
  have hcont := continuous_periodicExtension hp he hc
  have hder:=hasDerivWithinAt_periodicExtension_right hp hf
  have hbound (z:ℝ) : ‖periodicExtension hp df z‖≤M := by
    exact hb _ (by simpa only [zero_add] using toIcoMod_mem_Ico hp 0 z)
  wlog hxy : y≤x generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hh := norm_image_sub_le_of_norm_deriv_right_le_segment
    (a:=y) (b:=x) hcont.continuousOn (fun z _=>hder z) (fun z _=>hbound z) x ⟨hxy,le_rfl⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] using hh

end polyak.Global.Sampling
