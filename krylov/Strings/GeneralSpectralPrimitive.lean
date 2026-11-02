import krylov.Strings.SpectralPrimitive

/-!
Article: main_krylov, apC:prop:tauber, local energy spaces.
Use: physical local primitive operators for arbitrary string measures,
including infinite total mass and finite endpoints with diverging mass.
Only the chosen compact window must have finite mass.
Source: the actual Lebesgue L² primitive and local Cauchy--Schwarz estimate
already proved in SpectralPrimitive, with finite indicator functions.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal

/-- The actual mass Hilbert space; no total-mass finiteness is required. -/
abbrev MassHilbert (μ : Measure ℝ) := Lp ℂ 2 μ

/-- Physical gradient energy is integrated over the positive half-line.
For finite endpoints its unused tail is eliminated by energy minimization. -/
abbrev GradientHilbert := Spectral.GradientHilbert

/-- The mass and physical-gradient Hilbert product. -/
abbrev EnergyAmbient (μ : Measure ℝ) := WithLp 2 (MassHilbert μ × GradientHilbert)

/-- A genuine finite-mass physical prefix. The family can terminate at a
finite endpoint without requiring a finite mass there. -/
abbrev Window (μ : Measure ℝ) := {L : ℝ≥0 // μ (Icc (0 : ℝ) L) ≠ ⊤}

/-- The actual constant one on the chosen finite physical prefix. -/
def windowConstant (μ : Measure ℝ) (L : Window μ) : MassHilbert μ :=
  indicatorConstLp 2 measurableSet_Icc L.property (1 : ℂ)

/-- The local constant has its actual indicator representative. -/
theorem windowConstant_ae (μ : Measure ℝ) (L : Window μ) :
    windowConstant μ L =ᵐ[μ] (Icc (0 : ℝ) L.val).indicator (fun _ ↦ (1 : ℂ)) :=
  indicatorConstLp_coeFn

private def windowValue (μ : Measure ℝ) (L : Window μ) (u : MassHilbert μ) : MassHilbert μ :=
  ((Lp.memLp u).indicator measurableSet_Icc).toLp ((Icc (0 : ℝ) L.val).indicator u)

private theorem windowValue_ae (μ : Measure ℝ) (L : Window μ) (u : MassHilbert μ) :
    windowValue μ L u =ᵐ[μ] (Icc (0 : ℝ) L.val).indicator u := MemLp.coeFn_toLp _

private def windowLinear (μ : Measure ℝ) (L : Window μ) : MassHilbert μ →ₗ[ℂ] MassHilbert μ where
  toFun := windowValue μ L
  map_add' u v := by
    apply Lp.ext
    filter_upwards [windowValue_ae μ L (u + v), Lp.coeFn_add u v,
      Lp.coeFn_add (windowValue μ L u) (windowValue μ L v),
      windowValue_ae μ L u, windowValue_ae μ L v] with x hs huv ho hu hv
    simp only [Pi.add_apply] at huv ho
    rw [hs, ho, hu, hv]
    by_cases hx : x ∈ Icc (0 : ℝ) L.val
    · simpa only [indicator_of_mem hx] using huv
    · simp only [indicator_of_notMem hx, add_zero]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [windowValue_ae μ L (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul c (windowValue μ L u), windowValue_ae μ L u] with x hs hcu ho hu
    simp only [Pi.smul_apply] at hcu ho
    simp only [RingHom.id_apply]
    rw [hs, ho, hu]
    by_cases hx : x ∈ Icc (0 : ℝ) L.val
    · simpa only [indicator_of_mem hx] using hcu
    · simp only [indicator_of_notMem hx, smul_zero]

/-- Actual bounded restriction by a physical finite-prefix indicator. -/
def windowMultiplier (μ : Measure ℝ) (L : Window μ) : MassHilbert μ →L[ℂ] MassHilbert μ :=
  (windowLinear μ L).mkContinuous 1 (fun u ↦ by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [windowValue_ae μ L u] with x hx
    change ‖windowValue μ L u x‖ ≤ 1 * ‖u x‖
    rw [hx]
    by_cases hs : x ∈ Icc (0 : ℝ) L.val <;> simp [hs])

/-- The actual bounded window operator has the literal indicator formula. -/
theorem windowMultiplier_ae (μ : Measure ℝ) (L : Window μ) (u : MassHilbert μ) :
    windowMultiplier μ L u =ᵐ[μ] (Icc (0 : ℝ) L.val).indicator u := windowValue_ae μ L u

private def primitiveFunction (L : ℝ≥0) (g : GradientHilbert) : ℝ → ℂ :=
  (Icc (0 : ℝ) L).indicator (Spectral.gradientPrimitive g)

private theorem primitiveFunction_memLp (μ : Measure ℝ) (L : Window μ) (g : GradientHilbert) :
    MemLp (primitiveFunction L.val g) 2 μ := by
  have hi := memLp_indicator_const (μ := μ) 2 measurableSet_Icc
    ((Real.sqrt L.val * ‖g‖ : ℝ) : ℂ) (Or.inr L.property)
  apply hi.of_le ((Spectral.gradientPrimitive_continuous g).aestronglyMeasurable.indicator measurableSet_Icc)
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (0 : ℝ) L.val
  · simp only [indicator_of_mem hx, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact Spectral.gradientPrimitive_norm_le g L.val hx
  · simp only [indicator_of_notMem hx, norm_zero, le_refl]

private def primitiveValue (μ : Measure ℝ) (L : Window μ) (g : GradientHilbert) : MassHilbert μ :=
  (primitiveFunction_memLp μ L g).toLp (primitiveFunction L.val g)

private theorem primitiveValue_ae (μ : Measure ℝ) (L : Window μ) (g : GradientHilbert) :
    primitiveValue μ L g =ᵐ[μ] primitiveFunction L.val g := MemLp.coeFn_toLp _

private def primitiveLinear (μ : Measure ℝ) (L : Window μ) : GradientHilbert →ₗ[ℂ] MassHilbert μ where
  toFun := primitiveValue μ L
  map_add' g h := by
    apply Lp.ext
    filter_upwards [primitiveValue_ae μ L (g + h),
      Lp.coeFn_add (primitiveValue μ L g) (primitiveValue μ L h),
      primitiveValue_ae μ L g, primitiveValue_ae μ L h] with x hs ho hg hh
    simp only [Pi.add_apply] at ho
    rw [hs, ho, hg, hh]
    by_cases hx : x ∈ Icc (0 : ℝ) L.val
    · simp only [primitiveFunction, indicator_of_mem hx, Spectral.gradientPrimitive_add]
    · simp only [primitiveFunction, indicator_of_notMem hx, add_zero]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [primitiveValue_ae μ L (c • g), Lp.coeFn_smul c (primitiveValue μ L g),
      primitiveValue_ae μ L g] with x hs ho hg
    simp only [Pi.smul_apply] at ho
    simp only [RingHom.id_apply]
    rw [hs, ho, hg]
    by_cases hx : x ∈ Icc (0 : ℝ) L.val
    · simp only [primitiveFunction, indicator_of_mem hx, Spectral.gradientPrimitive_smul]
    · simp only [primitiveFunction, indicator_of_notMem hx, smul_zero]

/-- A genuine physical primitive in mass L² on any finite-mass prefix,
with a local norm bound independent of the total string mass. -/
def localPrimitive (μ : Measure ℝ) (L : Window μ) : GradientHilbert →L[ℂ] MassHilbert μ :=
  (primitiveLinear μ L).mkContinuous (Real.sqrt L.val * ‖windowConstant μ L‖) (fun g ↦ by
    have hb : ‖primitiveValue μ L g‖ ≤ (Real.sqrt L.val * ‖g‖) * ‖windowConstant μ L‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [primitiveValue_ae μ L g, windowConstant_ae μ L] with x hx hc
      rw [hx, hc]
      by_cases hs : x ∈ Icc (0 : ℝ) L.val
      · simp only [primitiveFunction, indicator_of_mem hs, norm_one, mul_one]
        exact Spectral.gradientPrimitive_norm_le g L.val hs
      · simp only [primitiveFunction, indicator_of_notMem hs, norm_zero, mul_zero, le_refl]
    exact hb.trans_eq (by ring))

/-- The local primitive is the actual Lebesgue integral of the L² gradient. -/
theorem localPrimitive_ae (μ : Measure ℝ) (L : Window μ) (g : GradientHilbert) :
    localPrimitive μ L g =ᵐ[μ]
      (Icc (0 : ℝ) L.val).indicator (Spectral.gradientPrimitive g) := primitiveValue_ae μ L g

end
end krylov.Strings.GeneralSpectral
