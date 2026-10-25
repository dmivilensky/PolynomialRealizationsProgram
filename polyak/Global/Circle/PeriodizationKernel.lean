import polyak.Global.Circle.PeriodizationDensity
import polyak.Global.Circle.Kernel
import polyak.Global.Kernels.Moments

/-! The actual scaled source kernel has the constructed smooth periodic
Haar density. This identifies the given pushforward probability measure. -/
noncomputable section
namespace polyak.Global.Circle
open Set Filter Function MeasureTheory
open scoped Topology ContDiff ENNReal

def scaledKernel (ε x : ℝ) : ℝ:=Kernels.kappa (x/ε)/ε

theorem scaledKernel_smooth (ε : ℝ) : ContDiff ℝ ∞ (scaledKernel ε) :=
  (Kernels.kappa_smooth.comp (contDiff_id.div_const ε)).div_const ε

theorem scaledKernel_nonneg {ε : ℝ} (hε : 0<ε) (x : ℝ) : 0≤scaledKernel ε x :=
  div_nonneg (Kernels.kappa_nonneg _) hε.le

theorem scaledKernel_even (ε x : ℝ) : scaledKernel ε (-x)=scaledKernel ε x := by
  unfold scaledKernel
  rw [neg_div,Kernels.kappa_even]

theorem scaledKernel_support {ε : ℝ} (hε : 0<ε) (x : ℝ) (hx : scaledKernel ε x≠0) :
    |x|≤ε := by
  have hn : Kernels.kappa (x/ε)≠0:=fun he=>hx (by simp only [scaledKernel,he,zero_div])
  have hh:=Kernels.kappa_support_bound hn
  rw [abs_div,abs_of_pos hε] at hh
  exact ((div_lt_one hε).mp hh).le

 theorem kernelMeasure_density {ε : ℝ} (hε : 0<ε) :
    Kernels.kernelMeasure ε=volume.withDensity (fun x=>ENNReal.ofReal (scaledKernel ε x)) := by
  have hs:=scaledKernel_smooth ε
  have hsupport:=scaledKernel_support hε
  have hfi:=hs.continuous.integrable_of_hasCompactSupport (μ:=volume) (compact_of_support_bound hsupport)
  have : IsFiniteMeasure (volume.withDensity (fun x=>ENNReal.ofReal (scaledKernel ε x))):=
    isFiniteMeasure_withDensity_ofReal hfi.2
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  change (∫x,φ.toContinuousMap x∂Kernels.kernelMeasure ε)=
    ∫x,φ.toContinuousMap x∂volume.withDensity (fun x=>ENNReal.ofReal (scaledKernel ε x))
  rw [Kernels.kernelMeasure,integral_map (show Measurable (fun x : ℝ=>ε*x) by fun_prop).aemeasurable
    φ.continuous.aestronglyMeasurable,Kernels.integral_kappaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul (μ:=volume) (f:=fun x=>ENNReal.ofReal (scaledKernel ε x)) (ENNReal.measurable_ofReal.comp hs.continuous.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scaledKernel_nonneg hε _),smul_eq_mul]
  have hchange:=Measure.integral_comp_mul_left (fun x : ℝ=>Kernels.kappa (x/ε)*φ.toContinuousMap x) ε
  simp only [abs_of_pos (inv_pos.mpr hε),smul_eq_mul] at hchange
  have he : (fun x : ℝ=>Kernels.kappa (ε*x/ε)*φ.toContinuousMap (ε*x))=
      (fun x : ℝ=>Kernels.kappa x*φ.toContinuousMap (ε*x)) := by
    funext x
    rw [mul_div_cancel_left₀ x hε.ne']
  rw [he] at hchange
  rw [hchange,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold scaledKernel
  ring

def kernelDensity (ε : ℝ) : Circle→ℝ:=haarDensity (scaledKernel ε)

@[simp] theorem kernelDensity_ofReal (ε x : ℝ) :
    kernelDensity ε (ofReal x)=(2*Real.pi)*periodize (scaledKernel ε) x :=
  haarDensity_ofReal _ _

theorem continuous_kernelDensity {ε : ℝ} (hε : 0<ε) : Continuous (kernelDensity ε) :=
  continuous_haarDensity (scaledKernel_smooth ε) (scaledKernel_support hε)

theorem smooth_kernelDensity_lift {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ∞ (fun x : ℝ=>kernelDensity ε (ofReal x)) :=
  smooth_haarDensity_lift (scaledKernel_smooth ε) (scaledKernel_support hε)

theorem kernelDensity_nonneg {ε : ℝ} (hε : 0<ε) (x : Circle) : 0≤kernelDensity ε x :=
  haarDensity_nonneg (scaledKernel_nonneg hε) x

theorem kernelDensity_even (ε : ℝ) (z : Circle) : kernelDensity ε (-z)=kernelDensity ε z := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    change kernelDensity ε (ofReal (-x))=kernelDensity ε (ofReal x)
    rw [kernelDensity_ofReal,kernelDensity_ofReal,periodize_even (scaledKernel_even ε)]

theorem kernelDensity_periodic (ε : ℝ) :
    Function.Periodic (fun x : ℝ=>kernelDensity ε (ofReal x)) (2*Real.pi) := by
  intro x
  simp only [kernelDensity_ofReal]
  rw [periodize_periodic (scaledKernel ε)]

theorem kernelCircle_density {ε : ℝ} (hε : 0<ε) (hεπ : ε<Real.pi) :
    kernel ε=haar.withDensity (fun z=>ENNReal.ofReal (kernelDensity ε z)) := by
  rw [kernel,kernelMeasure_density hε]
  exact map_density_eq_haarDensity (scaledKernel_smooth ε) hεπ (scaledKernel_support hε) (scaledKernel_nonneg hε)

end polyak.Global.Circle
