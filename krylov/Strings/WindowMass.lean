import krylov.Strings.WeightedVolterra
import Mathlib.MeasureTheory.Measure.Comap

/-!
Article: main_krylov, s3:def:string and apC:eq:state.
Use: Apply the measure-driven Volterra construction to a `Mass` on each compact
window. Finite-endpoint strings use the compatible compact representatives
constructed in `krylov.Strings.LocalMass`. The unit origin atom is excluded once.
Source: mathlib's measurable subtype embedding and the contracting constructions
in `krylov.Strings.Volterra` and `krylov.Strings.WeightedVolterra`.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace Mass

/-- The genuine mass on the compact state space, excluding its distinguished
unit atom. Positive-position atoms and singular mass are preserved. -/
def windowMeasure (M : Mass) (L : ℝ≥0) : Measure (Window L) :=
  Measure.comap Subtype.val (M.measure.restrict (Ioc 0 (L : ℝ)))

/-- Total local mass equals the actual cumulative increment, not an abstract
parameter or an assumed bound. -/
theorem windowMeasure_univ (M : Mass) (L : ℝ≥0) :
    M.windowMeasure L univ = ENNReal.ofReal (M.cumulative L - 1) := by
  rw [windowMeasure, Measure.comap_apply Subtype.val Subtype.val_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image']
  · rw [Subtype.coe_image_univ, Measure.restrict_apply measurableSet_Icc]
    have hi : Icc (0 : ℝ) (L : ℝ) ∩ Ioc 0 (L : ℝ) = Ioc 0 (L : ℝ) := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ioc]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨h.1.le, h.2⟩, h⟩⟩
    rw [hi, M.measure_Ioc, M.origin]
  · exact MeasurableSet.univ

instance finite_windowMeasure (M : Mass) (L : ℝ≥0) : IsFiniteMeasure (M.windowMeasure L) := by
  constructor
  rw [M.windowMeasure_univ]
  exact ENNReal.ofReal_lt_top

/-- Real total mass of the integration window. -/
theorem real_windowMeasure_univ (M : Mass) (L : ℝ≥0) :
    (M.windowMeasure L).real univ = M.cumulative L - 1 := by
  rw [Measure.real, M.windowMeasure_univ, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (M.one_le L.property)

/-- Integration on the compact state space is exactly integration against the
original post-origin Stieltjes mass. -/
theorem integral_windowMeasure (M : Mass) (L : ℝ≥0) (F : ℝ → ℝ) :
    (∫ y : Window L, F (y : ℝ) ∂M.windowMeasure L) =
      ∫ y in Ioc 0 (L : ℝ), F y ∂M.measure := by
  rw [windowMeasure, integral_subtype_comap measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc (0 : ℝ) L ∩ Ioc 0 (L : ℝ) = Ioc 0 (L : ℝ) := by
    exact inter_eq_right.mpr Ioc_subset_Icc_self
  rw [hs]

/-- Partial cumulative integration on the compact state space agrees with the
article's half-open interval, including its right-endpoint atom. -/
theorem integral_windowMeasure_cumulative (M : Mass) (L : ℝ≥0) (F : ℝ → ℝ)
    {t : ℝ} (ht : t ≤ L) :
    (∫ y : Window L, if (y : ℝ) ≤ t then F y else 0 ∂M.windowMeasure L) =
      ∫ y in Ioc 0 t, F y ∂M.measure := by
  rw [M.integral_windowMeasure L (fun y : ℝ ↦ if y ≤ t then F y else 0)]
  have hf : (fun y : ℝ ↦ if y ≤ t then F y else 0) = (Iic t).indicator F := by
    ext y
    simp only [indicator, mem_Iic]
  rw [hf, setIntegral_indicator measurableSet_Iic]
  have hs : Ioc (0 : ℝ) L ∩ Iic t = Ioc 0 t := by
    ext y
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans ht⟩, h.2⟩⟩
  rw [hs]

/-- Every `Mass` admits a genuine positive-length contraction window. The
explicit choice only uses the already finite mass at position one, so no
non-atomicity or limiting estimate at zero is required. -/
theorem exists_small_window (M : Mass) : ∃ L : ℝ≥0, 0 < L ∧
    (L : ℝ) * (M.windowMeasure L).real univ < 1 := by
  have hM : 1 ≤ M.cumulative 1 := M.one_le (by norm_num)
  have hMpos : 0 < M.cumulative 1 := lt_of_lt_of_le zero_lt_one hM
  let L : ℝ≥0 := ⟨1 / (2 * M.cumulative 1), by positivity⟩
  have hL : 0 < (L : ℝ) := by
    change 0 < 1 / (2 * M.cumulative 1)
    exact one_div_pos.mpr (mul_pos (by norm_num) hMpos)
  have hL1 : (L : ℝ) ≤ 1 := by
    dsimp [L]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  refine ⟨L, hL, ?_⟩
  rw [M.real_windowMeasure_univ]
  have hm : M.cumulative L ≤ M.cumulative 1 := M.cumulative.mono hL1
  have hden : 0 < 2 * M.cumulative 1 := by positivity
  change 1 / (2 * M.cumulative 1) * (M.cumulative L - 1) < 1
  rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hden]
  linarith

/-- Local existence, uniqueness, positivity and monotonicity of the actual
displacement equation for a `Mass`, including arbitrary positive-position atoms.
This is the Volterra form of the state equation, before the separate Fubini
identification with the coupled `(φ,p,K)` system. -/
theorem exists_local_displacement (M : Mass) :
    ∃ L : ℝ≥0, 0 < L ∧ ∃ f : C(Window L, ℝ),
      (∀ x, f x = 1 + (x : ℝ) +
        ∫ y, Window.kernel x y * f y ∂M.windowMeasure L) ∧
      (∀ x : Window L, 1 + (x : ℝ) ≤ f x) ∧ Monotone f ∧
      (∀ g : C(Window L, ℝ),
        (∀ x, g x = 1 + (x : ℝ) +
          ∫ y, Window.kernel x y * g y ∂M.windowMeasure L) → g = f) := by
  obtain ⟨L, hL, hs⟩ := M.exists_small_window
  obtain ⟨f, hf, hu⟩ := Window.existsUnique_volterra (M.windowMeasure L) 1 1 hs
  have hf' : ∀ x, f x = 1 + (x : ℝ) +
      ∫ y, Window.kernel x y * f y ∂M.windowMeasure L := by simpa using hf
  refine ⟨L, hL, f, hf', ?_, ?_, ?_⟩
  · simpa using Window.volterra_ge_free (M.windowMeasure L) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) hs hf
  · exact Window.volterra_monotone (M.windowMeasure L) (by norm_num) (by norm_num) hs hf
  · intro g hg
    exact hu g (by simpa using hg)

/-- Every finite physical window of a `Mass` has a unique displacement, above
the normalized free trajectory and monotone. The exponential weighting removes
all short-window restrictions and includes general Stieltjes mass. -/
theorem existsUnique_displacement (M : Mass) (L : ℝ≥0) :
    ∃! f : C(Window L, ℝ),
      (∀ x, f x = 1 + (x : ℝ) +
        ∫ y, Window.kernel x y * f y ∂M.windowMeasure L) ∧
      (∀ x : Window L, 1 + (x : ℝ) ≤ f x) ∧ Monotone f := by
  obtain ⟨f, hf, hu⟩ := Window.existsUnique_volterra_finite (M.windowMeasure L) 1 1
  refine ⟨f, ⟨by simpa using hf, ?_, ?_⟩, ?_⟩
  · simpa using Window.volterra_ge_free_finite (M.windowMeasure L)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hf
  · exact Window.volterra_monotone_finite (M.windowMeasure L) (by norm_num) (by norm_num) hf
  · intro g hg
    exact hu g (by simpa using hg.1)

end Mass
end
end krylov.Strings
