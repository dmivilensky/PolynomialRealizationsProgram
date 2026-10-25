import polyak.Global.Circle.PeriodizationBasic
import polyak.Global.Kernels.MeasureDensity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! The smooth periodized function is the actual Haar density of the
pushforward measure. Haar normalization contributes the literal factor 2pi. -/
noncomputable section
namespace polyak.Global.Circle
open Set Filter Function MeasureTheory Topology
open scoped Topology ContDiff ENNReal

def periodicDensity (f : ℝ→ℝ) : Circle→ℝ:=(periodize_periodic f).lift

def haarDensity (f : ℝ→ℝ) (z : Circle) : ℝ:=(2*Real.pi)*periodicDensity f z

@[simp] theorem periodicDensity_ofReal (f : ℝ→ℝ) (x : ℝ) :
    periodicDensity f (ofReal x)=periodize f x := (periodize_periodic f).lift_coe x

@[simp] theorem haarDensity_ofReal (f : ℝ→ℝ) (x : ℝ) :
    haarDensity f (ofReal x)=(2*Real.pi)*periodize f x := by rw [haarDensity,periodicDensity_ofReal]

theorem continuous_periodicDensity {f : ℝ→ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ f)
    (hf : ∀x,f x≠0→|x|≤R) : Continuous (periodicDensity f) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2*Real.pi))).continuous_iff.mpr
  simpa only [Function.comp_def,periodicDensity,Function.Periodic.lift_coe] using (smooth_periodize hs hf).continuous

theorem continuous_haarDensity {f : ℝ→ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ f)
    (hf : ∀x,f x≠0→|x|≤R) : Continuous (haarDensity f) :=
  continuous_const.mul (continuous_periodicDensity hs hf)

theorem smooth_haarDensity_lift {f : ℝ→ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ f)
    (hf : ∀x,f x≠0→|x|≤R) : ContDiff ℝ ∞ (fun x : ℝ=>haarDensity f (ofReal x)) := by
  simpa only [haarDensity_ofReal] using contDiff_const.mul (smooth_periodize hs hf)

theorem haarDensity_nonneg {f : ℝ→ℝ} (hf : ∀x,0≤f x) (z : Circle) : 0≤haarDensity f z := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    change 0≤haarDensity f (ofReal x)
    rw [haarDensity_ofReal]
    exact mul_nonneg Real.two_pi_pos.le (periodize_nonneg hf x)

theorem compact_of_support_bound {f : ℝ→ℝ} {R : ℝ} (hf : ∀x,f x≠0→|x|≤R) :
    HasCompactSupport f := by
  change IsCompact (closure (Function.support f))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx=>abs_le.mp (hf x hx)) isClosed_Icc)

theorem integral_haarDensity (f : ℝ→ℝ) {R : ℝ} (hR : R<Real.pi)
    (hf : ∀x,f x≠0→|x|≤R) (φ : C(Circle,ℝ)) :
    (∫z,haarDensity f z*φ z∂haar)=∫x : ℝ,f x*φ (ofReal x) := by
  have hnorm : (∫z,haarDensity f z*φ z∂haar)=∫z : Circle,periodicDensity f z*φ z := by
    have hid : (fun z : Circle=>haarDensity f z*φ z)=
        (fun z : Circle=>(2*Real.pi)*(periodicDensity f z*φ z)) := by
      funext z
      unfold haarDensity
      ring
    rw [hid,integral_const_mul,AddCircle.integral_haarAddCircle]
    simp only [smul_eq_mul]
    rw [←mul_assoc,mul_inv_cancel₀ Real.two_pi_pos.ne',one_mul]
  rw [hnorm,←AddCircle.intervalIntegral_preimage (2*Real.pi) (-Real.pi)]
  rw [show -Real.pi+(2*Real.pi)=Real.pi by ring]
  have he : (∫x in -Real.pi..Real.pi,periodicDensity f (x:Circle)*φ x)=
      ∫x in -Real.pi..Real.pi,f x*φ (ofReal x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hi : x∈Icc (-Real.pi) Real.pi:=by simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)] using hx
    change periodicDensity f (ofReal x)*φ (ofReal x)=_
    rw [periodicDensity_ofReal,periodize_eq_on_fundamental hR hf hi]
  rw [he,intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with x hx
  have hz : f x=0 := by
    by_contra hn
    have hh:=(hf x hn).trans_lt hR
    have hi:=abs_lt.mp hh
    exact hx ⟨hi.1,hi.2.le⟩
  simp only [hz,zero_mul]

theorem map_density_eq_haarDensity {f : ℝ→ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ f)
    (hR : R<Real.pi) (hf : ∀x,f x≠0→|x|≤R) (hn : ∀x,0≤f x) :
    (volume.withDensity (fun x=>ENNReal.ofReal (f x))).map ofReal=
      haar.withDensity (fun z=>ENNReal.ofReal (haarDensity f z)) := by
  have hfi:=hs.continuous.integrable_of_hasCompactSupport (μ:=volume) (compact_of_support_bound hf)
  have : IsFiniteMeasure (volume.withDensity (fun x=>ENNReal.ofReal (f x))):=
    isFiniteMeasure_withDensity_ofReal hfi.2
  have hcont:=continuous_haarDensity hs hf
  have hdi:=hcont.integrable_of_hasCompactSupport (μ:=haar) (HasCompactSupport.of_compactSpace _)
  have : IsFiniteMeasure (haar.withDensity (fun z=>ENNReal.ofReal (haarDensity f z))):=
    isFiniteMeasure_withDensity_ofReal hdi.2
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  change (∫x,φ.toContinuousMap x∂(volume.withDensity (fun x=>ENNReal.ofReal (f x))).map ofReal)=
    ∫x,φ.toContinuousMap x∂haar.withDensity (fun z=>ENNReal.ofReal (haarDensity f z))
  rw [integral_map continuous_ofReal.measurable.aemeasurable φ.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (μ:=volume) (f:=fun x=>ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hs.continuous.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  rw [integral_withDensity_eq_integral_toReal_smul (μ:=haar) (f:=fun z=>ENNReal.ofReal (haarDensity f z)) (ENNReal.measurable_ofReal.comp hcont.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _),ENNReal.toReal_ofReal (haarDensity_nonneg hn _),smul_eq_mul]
  exact (integral_haarDensity f hR hf φ.toContinuousMap).symm

end polyak.Global.Circle
