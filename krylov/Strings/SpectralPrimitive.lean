import krylov.Strings.SpectralSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Article: `main_krylov`, `thm:value`, the closed energy-graph realization.
Local windows and local gradient primitives are genuine bounded operators
between the physical L² spaces. The primitive uses the actual Lebesgue
integral on the positive half-line; L² Cauchy--Schwarz supplies its bound.
Source: mathlib L² indicator inner products and local Bochner integration.
-/
namespace krylov.Strings.Spectral
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

private def windowValue (M : Mass) (L : ℝ≥0) (u : MassHilbert M) : MassHilbert M :=
  ((Lp.memLp u).indicator measurableSet_Icc).toLp ((Icc (0 : ℝ) L).indicator u)

private theorem windowValue_ae (M : Mass) (L : ℝ≥0) (u : MassHilbert M) :
    windowValue M L u =ᵐ[M.measure] (Icc (0 : ℝ) L).indicator u :=
  MemLp.coeFn_toLp _

private def windowLinear (M : Mass) (L : ℝ≥0) : MassHilbert M →ₗ[ℂ] MassHilbert M where
  toFun := windowValue M L
  map_add' u v := by
    apply Lp.ext
    filter_upwards [windowValue_ae M L (u + v), Lp.coeFn_add u v,
      Lp.coeFn_add (windowValue M L u) (windowValue M L v),
      windowValue_ae M L u, windowValue_ae M L v] with x hsum huv hout hu hv
    simp only [Pi.add_apply] at huv hout
    rw [hsum, hout, hu, hv]
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simpa only [indicator_of_mem hx] using huv
    · simp only [indicator_of_notMem hx, add_zero]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [windowValue_ae M L (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul c (windowValue M L u), windowValue_ae M L u] with x hsum hcu hout hu
    simp only [Pi.smul_apply] at hcu hout
    simp only [RingHom.id_apply]
    rw [hsum, hout, hu]
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simpa only [indicator_of_mem hx] using hcu
    · simp only [indicator_of_notMem hx, smul_zero]

/-- Multiplication by the physical window indicator `[0,L]`. -/
def windowMultiplier (M : Mass) (L : ℝ≥0) : MassHilbert M →L[ℂ] MassHilbert M :=
  (windowLinear M L).mkContinuous 1 (fun u ↦ by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [windowValue_ae M L u] with x hx
    change ‖windowValue M L u x‖ ≤ 1 * ‖u x‖
    rw [hx]
    by_cases hs : x ∈ Icc (0 : ℝ) L <;> simp [hs])

theorem windowMultiplier_ae (M : Mass) (L : ℝ≥0) (u : MassHilbert M) :
    windowMultiplier M L u =ᵐ[M.measure] (Icc (0 : ℝ) L).indicator u :=
  windowValue_ae M L u

/-- The true primitive in the physical gradient measure. -/
def gradientPrimitive (g : GradientHilbert) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x, g t ∂volume.restrict (Ioi (0 : ℝ))

theorem gradient_intervalIntegrable (g : GradientHilbert) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ g x) (volume.restrict (Ioi (0 : ℝ))) a b :=
  (((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact
    isCompact_uIcc).intervalIntegrable

theorem gradientPrimitive_continuous (g : GradientHilbert) : Continuous (gradientPrimitive g) :=
  intervalIntegral.continuous_primitive (gradient_intervalIntegrable g) 0

theorem gradientPrimitive_eq_setIntegral (g : GradientHilbert) {x : ℝ} (hx : 0 ≤ x) :
    gradientPrimitive g x = ∫ t in Ioc (0 : ℝ) x, g t ∂volume.restrict (Ioi (0 : ℝ)) :=
  intervalIntegral.integral_of_le hx

theorem gradientPrimitive_add (g h : GradientHilbert) (x : ℝ) :
    gradientPrimitive (g + h) x = gradientPrimitive g x + gradientPrimitive h x := by
  unfold gradientPrimitive
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_add g h).mono fun _ hx _ ↦ hx)]
  exact intervalIntegral.integral_add (gradient_intervalIntegrable g 0 x) (gradient_intervalIntegrable h 0 x)

theorem gradientPrimitive_smul (c : ℂ) (g : GradientHilbert) (x : ℝ) :
    gradientPrimitive (c • g) x = c • gradientPrimitive g x := by
  unfold gradientPrimitive
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_smul c g).mono fun _ hx _ ↦ hx)]
  exact intervalIntegral.integral_smul c _

/-- Cauchy--Schwarz in the actual physical L² space. -/
theorem gradientPrimitive_norm_le (g : GradientHilbert) (L : ℝ≥0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) : ‖gradientPrimitive g x‖ ≤ Real.sqrt L * ‖g‖ := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hμ : μ (Ioc (0 : ℝ) x) = ENNReal.ofReal x := by
    dsimp [μ]
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    simp
  have hμfin : μ (Ioc (0 : ℝ) x) ≠ ⊤ := by rw [hμ]; exact ENNReal.ofReal_ne_top
  let k : GradientHilbert := indicatorConstLp 2 measurableSet_Ioc hμfin (1 : ℂ)
  have hk : ‖k‖ = Real.sqrt x := by
    rw [show k = indicatorConstLp 2 measurableSet_Ioc hμfin (1 : ℂ) from rfl,
      norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp [Measure.real, hμ, Real.sqrt_eq_rpow, hx.1]
  have hid : gradientPrimitive g x = inner ℂ k g := by
    rw [gradientPrimitive_eq_setIntegral g hx.1]
    exact (L2.inner_indicatorConstLp_one measurableSet_Ioc hμfin g).symm
  rw [hid]
  calc
    ‖inner ℂ k g‖ ≤ ‖k‖ * ‖g‖ := norm_inner_le_norm k g
    _ ≤ Real.sqrt L * ‖g‖ := by rw [hk]; gcongr; exact hx.2

private def windowPrimitive (L : ℝ≥0) (g : GradientHilbert) : ℝ → ℂ :=
  (Icc (0 : ℝ) L).indicator (gradientPrimitive g)

private theorem windowPrimitive_norm_le (L : ℝ≥0) (g : GradientHilbert) (x : ℝ) :
    ‖windowPrimitive L g x‖ ≤ Real.sqrt L * ‖g‖ := by
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · simpa only [windowPrimitive, indicator_of_mem hx] using gradientPrimitive_norm_le g L hx
  · simp only [windowPrimitive, indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

private theorem windowPrimitive_memLp (M : Mass) [IsFiniteMeasure M.measure]
    (L : ℝ≥0) (g : GradientHilbert) : MemLp (windowPrimitive L g) 2 M.measure :=
  MemLp.of_bound ((gradientPrimitive_continuous g).aestronglyMeasurable.indicator measurableSet_Icc)
    (Real.sqrt L * ‖g‖) (Filter.Eventually.of_forall (windowPrimitive_norm_le L g))

private def localPrimitiveValue (M : Mass) [IsFiniteMeasure M.measure]
    (L : ℝ≥0) (g : GradientHilbert) : MassHilbert M :=
  (windowPrimitive_memLp M L g).toLp (windowPrimitive L g)

private theorem localPrimitiveValue_ae (M : Mass) [IsFiniteMeasure M.measure]
    (L : ℝ≥0) (g : GradientHilbert) :
    localPrimitiveValue M L g =ᵐ[M.measure] windowPrimitive L g := MemLp.coeFn_toLp _

private def localPrimitiveLinear (M : Mass) [IsFiniteMeasure M.measure]
    (L : ℝ≥0) : GradientHilbert →ₗ[ℂ] MassHilbert M where
  toFun := localPrimitiveValue M L
  map_add' g h := by
    apply Lp.ext
    filter_upwards [localPrimitiveValue_ae M L (g + h),
      Lp.coeFn_add (localPrimitiveValue M L g) (localPrimitiveValue M L h),
      localPrimitiveValue_ae M L g, localPrimitiveValue_ae M L h] with x hsum hout hg hh
    simp only [Pi.add_apply] at hout
    rw [hsum, hout, hg, hh]
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simp only [windowPrimitive, indicator_of_mem hx, gradientPrimitive_add]
    · simp only [windowPrimitive, indicator_of_notMem hx, add_zero]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [localPrimitiveValue_ae M L (c • g),
      Lp.coeFn_smul c (localPrimitiveValue M L g),
      localPrimitiveValue_ae M L g] with x hsum hout hg
    simp only [Pi.smul_apply] at hout
    simp only [RingHom.id_apply]
    rw [hsum, hout, hg]
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simp only [windowPrimitive, indicator_of_mem hx, gradientPrimitive_smul]
    · simp only [windowPrimitive, indicator_of_notMem hx, smul_zero]

/-- Bounded local primitive from the true physical gradient L² space into
mass L², with its actual set-integral formula. -/
def localPrimitive (M : Mass) [IsFiniteMeasure M.measure] (L : ℝ≥0) :
    GradientHilbert →L[ℂ] MassHilbert M :=
  (localPrimitiveLinear M L).mkContinuous
    (Real.sqrt L * ‖Lp.const 2 M.measure (1 : ℂ)‖) (fun g ↦ by
      have hh : ‖localPrimitiveValue M L g‖ ≤ (Real.sqrt L * ‖g‖) *
          ‖Lp.const 2 M.measure (1 : ℂ)‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [localPrimitiveValue_ae M L g,
          Lp.coeFn_const (p := 2) (μ := M.measure) (1 : ℂ)] with x hx hc
        rw [hx, hc]
        simpa only [Function.const_apply, norm_one, mul_one] using windowPrimitive_norm_le L g x
      change ‖localPrimitiveValue M L g‖ ≤ _
      calc
        ‖localPrimitiveValue M L g‖ ≤ _ := hh
        _ = (Real.sqrt L * ‖Lp.const 2 M.measure (1 : ℂ)‖) * ‖g‖ := by ring)

theorem localPrimitive_ae (M : Mass) [IsFiniteMeasure M.measure] (L : ℝ≥0)
    (g : GradientHilbert) :
    localPrimitive M L g =ᵐ[M.measure]
      (Icc (0 : ℝ) L).indicator (fun x ↦
        ∫ t in Ioc (0 : ℝ) x, g t ∂volume.restrict (Ioi (0 : ℝ))) := by
  filter_upwards [localPrimitiveValue_ae M L g] with x hx
  change localPrimitiveValue M L g x = _
  rw [hx]
  by_cases hs : x ∈ Icc (0 : ℝ) L
  · simp only [windowPrimitive, indicator_of_mem hs, gradientPrimitive_eq_setIntegral g hs.1]
  · simp only [windowPrimitive, indicator_of_notMem hs]

end
end krylov.Strings.Spectral
