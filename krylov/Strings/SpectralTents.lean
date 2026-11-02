import krylov.Strings.SpectralPrimitive
import krylov.Strings.SpectralBoundary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: `main_krylov`, `thm:value`, exclusion of a spurious boundary spectral
atom at infinite energy. Actual shrinking piecewise affine tents have
physical L² gradients and converge in mass L² to the distinguished boundary
vector. Thus boundary density is proved for the concrete energy realization.
-/
namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The string measure is carried by the physical half-line. -/
theorem mass_ae_nonnegative (M : Mass) : ∀ᵐ x ∂M.measure, 0 ≤ x := by
  have hbot : Tendsto M.cumulative atBot (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact (M.negative x hx).symm
  have hneg : M.measure (Iio (0 : ℝ)) = 0 := by
    change M.cumulative.measure (Iio 0) = 0
    rw [M.cumulative.measure_Iio hbot 0, M.leftLim_origin]
    simp
  apply ae_iff.mpr
  rw [show {x : ℝ | ¬0 ≤ x} = Iio (0 : ℝ) by ext x; simp]
  exact hneg

def tentScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tentScale_pos (n : ℕ) : 0 < tentScale n := by unfold tentScale; positivity

theorem tentScale_tendsto : Tendsto tentScale atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def tentFunction (n : ℕ) : ℝ → ℂ :=
  (Icc (0 : ℝ) (tentScale n)).indicator (fun x ↦ ((1 - x / tentScale n : ℝ) : ℂ))

theorem tentFunction_origin (n : ℕ) : tentFunction n 0 = 1 := by
  simp [tentFunction, (tentScale_pos n).le]

theorem tentFunction_norm_le (n : ℕ) (x : ℝ) : ‖tentFunction n x‖ ≤ 1 := by
  by_cases hx : x ∈ Icc (0 : ℝ) (tentScale n)
  · rw [tentFunction, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]
    have hh : x / tentScale n ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx.1 (tentScale_pos n).le, (div_le_one (tentScale_pos n)).mpr hx.2⟩
    constructor <;> linarith [hh.1, hh.2]
  · simp [tentFunction, hx]

private theorem tentFunction_memLp (M : Mass) [IsFiniteMeasure M.measure] (n : ℕ) :
    MemLp (tentFunction n) 2 M.measure := by
  apply MemLp.of_bound _ 1 (Eventually.of_forall (tentFunction_norm_le n))
  exact (Complex.continuous_ofReal.comp
    (continuous_const.sub (continuous_id.div_const (tentScale n)))).aestronglyMeasurable.indicator
      measurableSet_Icc

/-- Genuine physical mass L² tent. -/
def boundaryTent (M : Mass) [IsFiniteMeasure M.measure] (n : ℕ) : MassHilbert M :=
  (tentFunction_memLp M n).toLp (tentFunction n)

theorem boundaryTent_ae (M : Mass) [IsFiniteMeasure M.measure] (n : ℕ) :
    boundaryTent M n =ᵐ[M.measure] tentFunction n := MemLp.coeFn_toLp _

private theorem tent_difference_bound (n : ℕ) (x : ℝ) :
    ‖tentFunction n x - ({0} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) x‖ ≤
      ‖(Ioc (0 : ℝ) (tentScale n)).indicator (fun _ ↦ (1 : ℂ)) x‖ := by
  by_cases hzero : x = 0
  · subst x
    simp [tentFunction_origin]
  · have hnotzero : x ∉ ({0} : Set ℝ) := by simpa using hzero
    rw [indicator_of_notMem hnotzero, sub_zero]
    by_cases hx : x ∈ Ioc (0 : ℝ) (tentScale n)
    · rw [indicator_of_mem hx, norm_one]
      exact tentFunction_norm_le n x
    · have hnot : x ∉ Icc (0 : ℝ) (tentScale n) := by
        intro hh
        exact hx ⟨lt_of_le_of_ne hh.1 (Ne.symm hzero), hh.2⟩
      simp [tentFunction, hnot, hx]

private def shrinkingIndicator (M : Mass) (n : ℕ) : MassHilbert M :=
  indicatorConstLp 2 measurableSet_Ioc (M.measure_Ioc_lt_top 0 (tentScale n)).ne (1 : ℂ)

private theorem shrinkingIndicator_norm (M : Mass) (n : ℕ) :
    ‖shrinkingIndicator M n‖ = Real.sqrt (M.cumulative (tentScale n) - 1) := by
  rw [shrinkingIndicator, norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)]
  simp [Real.sqrt_eq_rpow, Measure.real, M.measure_Ioc, M.origin,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (M.one_le (tentScale_pos n).le))]

/-- Shrinking physical tents converge to the actual unit-atom boundary
vector. This is a mass L² statement even for singular or atomic mass. -/
theorem boundaryTent_tendsto (M : Mass) [IsFiniteMeasure M.measure] :
    Tendsto (boundaryTent M) atTop (𝓝 (boundaryVector M)) := by
  have hscale : Tendsto tentScale atTop (𝓝[≥] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tentScale_tendsto,
      Eventually.of_forall fun n ↦ (tentScale_pos n).le⟩
  have hmass : Tendsto (fun n ↦ M.cumulative (tentScale n) - 1) atTop (𝓝 (0 : ℝ)) := by
    have hh := (M.cumulative.right_continuous 0).tendsto.comp hscale
    simpa only [Function.comp_def, M.origin, sub_self] using hh.sub_const 1
  have hlim : Tendsto (fun n ↦ ‖shrinkingIndicator M n‖) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [shrinkingIndicator_norm]
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hmass
  have hbound (n : ℕ) : ‖boundaryTent M n - boundaryVector M‖ ≤ ‖shrinkingIndicator M n‖ := by
    have hh : ‖boundaryTent M n - boundaryVector M‖ ≤ 1 * ‖shrinkingIndicator M n‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (boundaryTent M n) (boundaryVector M), boundaryTent_ae M n,
        indicatorConstLp_coeFn (μ := M.measure) (s := ({0} : Set ℝ)) (c := (1 : ℂ)),
        indicatorConstLp_coeFn (μ := M.measure) (s := Ioc (0 : ℝ) (tentScale n)) (c := (1 : ℂ))]
        with x hsub htent hboundary hind
      simp only [Pi.sub_apply] at hsub
      rw [hsub, htent]
      change ‖tentFunction n x - boundaryVector M x‖ ≤ 1 * ‖shrinkingIndicator M n x‖
      rw [show boundaryVector M x = ({0} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) x from hboundary,
        show shrinkingIndicator M n x = (Ioc (0 : ℝ) (tentScale n)).indicator (fun _ ↦ (1 : ℂ)) x from hind,
        one_mul]
      exact tent_difference_bound n x
    simpa only [one_mul] using hh
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ by simpa only [dist_eq_norm] using hbound n) hlim

private theorem gradient_window_finite (n : ℕ) :
    (volume.restrict (Ioi (0 : ℝ))) (Ioc (0 : ℝ) (tentScale n)) ≠ ⊤ := by
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
  simp

/-- True weak derivative of the piecewise affine physical tent. -/
def boundaryTentGradient (n : ℕ) : GradientHilbert :=
  indicatorConstLp 2 measurableSet_Ioc (gradient_window_finite n) ((-1 / tentScale n : ℝ) : ℂ)

theorem boundaryTentGradient_primitive (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gradientPrimitive (boundaryTentGradient n) x = ((-min (tentScale n) x / tentScale n : ℝ) : ℂ) := by
  have hmin : 0 ≤ min (tentScale n) x := le_min (tentScale_pos n).le hx
  have hinter : Ioc (0 : ℝ) (tentScale n) ∩ Ioc 0 x = Ioc 0 (min (tentScale n) x) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, le_min_iff]
    tauto
  have hreal : (volume.restrict (Ioi (0 : ℝ))).real (Ioc 0 (min (tentScale n) x)) =
      min (tentScale n) x := by
    rw [Measure.real, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self]
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hmin]
  rw [gradientPrimitive_eq_setIntegral _ hx, boundaryTentGradient,
    setIntegral_indicatorConstLp measurableSet_Ioc measurableSet_Ioc, hinter, hreal]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one]
  ring

theorem tentFunction_eq_primitive (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    tentFunction n x = 1 + gradientPrimitive (boundaryTentGradient n) x := by
  rw [boundaryTentGradient_primitive n hx]
  by_cases hxe : x ≤ tentScale n
  · rw [min_eq_right hxe, tentFunction, indicator_of_mem (show x ∈ Icc (0 : ℝ) (tentScale n) from ⟨hx, hxe⟩)]
    push_cast
    ring
  · have hnot : x ∉ Icc (0 : ℝ) (tentScale n) := fun hh ↦ hxe hh.2
    rw [min_eq_left (le_of_not_ge hxe), tentFunction, indicator_of_notMem hnot]
    have hc : (tentScale n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (tentScale_pos n))
    simp only [Complex.ofReal_div, Complex.ofReal_neg, neg_div, div_self hc, add_neg_cancel]

/-- Equality almost everywhere fixes the actual value at the distinguished
unit atom. -/
theorem eq_at_origin_of_ae_eq (M : Mass) {f g : ℝ → ℂ} (h : f =ᵐ[M.measure] g) : f 0 = g 0 := by
  by_contra hn
  have hbad : M.measure {x | f x ≠ g x} = 0 := ae_iff.mp h
  have hsub : ({0} : Set ℝ) ⊆ {x | f x ≠ g x} := by
    intro x hx
    change f x ≠ g x
    rw [mem_singleton_iff.mp hx]
    exact hn
  have hh := measure_mono_null hsub hbad
  simp at hh

theorem boundaryTent_trace (M : Mass) [IsFiniteMeasure M.measure] (n : ℕ) :
    boundaryTrace M (boundaryTent M n) = 1 := by
  rw [boundaryTrace_apply, eq_at_origin_of_ae_eq M (boundaryTent_ae M n), tentFunction_origin]

/-- The mass component and physical gradient satisfy the actual primitive
constraint defining the closed string energy graph. -/
theorem boundaryTent_energy_ae (M : Mass) [IsFiniteMeasure M.measure] (n : ℕ) :
    boundaryTent M n =ᵐ[M.measure] fun x ↦
      boundaryTrace M (boundaryTent M n) + gradientPrimitive (boundaryTentGradient n) x := by
  filter_upwards [boundaryTent_ae M n, mass_ae_nonnegative M] with x ht hx
  rw [ht, boundaryTent_trace]
  exact tentFunction_eq_primitive n hx

end
end krylov.Strings.Spectral
