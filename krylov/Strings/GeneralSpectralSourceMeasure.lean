import krylov.Strings.GeneralSpectralEnergy
import krylov.Strings.LocalMass

/-!
Article: main_krylov, s3:def:string and apC:prop:tauber.
Use: realize a cumulative mass on the actual half-open finite string domain
as one physical measure, including its distinguished unit atom. No finite
endpoint value or finite total mass is required. This is a measure-theoretic
bridge; it does not identify a generalized-eigenfunction spectral transform.
Source: mathlib's Stieltjes measure on an ordered subtype and measurable
pushforward; compact compatibility uses `LocalMass`.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory
open scoped NNReal

/-- Closed order intervals strictly below a finite endpoint remain compact,
although the complete half-open string domain need not be compact. -/
instance finiteSource_compactIcc {ℓ : ℝ} : CompactIccSpace (Ico (0 : ℝ) ℓ) where
  isCompact_Icc := by
    intro a b
    rw [Subtype.isCompact_iff, image_subtype_val_Icc]
    exact isCompact_Icc

/-- The actual mass of a finite-length source string: the subtype Stieltjes
measure accounts for all positive-position increments and the separate Dirac
measure restores the distinguished atom, which a Stieltjes measure at a
minimum excludes. The source mass may diverge at its excluded endpoint. -/
def finiteSourceMeasure {ℓ : ℝ} (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) : Measure ℝ :=
  Measure.dirac 0 + f.measure.map Subtype.val

/-- The subtype Stieltjes measure has no atom at the leftmost source point. -/
theorem finiteSource_stieltjes_origin {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) :
    f.measure {⟨0, ⟨le_rfl, hℓ⟩⟩} = 0 := by
  rw [f.measure_singleton, leftLim_eq_of_isBot (show IsBot
    (⟨0, ⟨le_rfl, hℓ⟩⟩ : Ico (0 : ℝ) ℓ) from fun x ↦ x.property.1)]
  simp

/-- The actual finite-source measure retains precisely the unit origin atom. -/
theorem finiteSourceMeasure_origin {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) : finiteSourceMeasure f {0} = 1 := by
  rw [finiteSourceMeasure, Measure.add_apply,
    Measure.map_apply measurable_subtype_coe (measurableSet_singleton 0)]
  have he : Subtype.val ⁻¹' ({0} : Set ℝ) =
      ({⟨0, ⟨le_rfl, hℓ⟩⟩} : Set (Ico (0 : ℝ) ℓ)) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
  rw [he, finiteSource_stieltjes_origin hℓ f]
  simp

/-- A genuine finite-endpoint source string supplies actual mass data for
the physical energy construction, without a global boundedness assumption. -/
def StringMeasure.ofFiniteSource {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) : StringMeasure :=
  ⟨finiteSourceMeasure f, finiteSourceMeasure_origin hℓ f⟩

/-- No physical mass is introduced before the source origin. -/
theorem finiteSourceMeasure_negative {ℓ : ℝ}
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) : finiteSourceMeasure f (Iio 0) = 0 := by
  rw [finiteSourceMeasure, Measure.add_apply,
    Measure.map_apply measurable_subtype_coe measurableSet_Iio]
  have he : Subtype.val ⁻¹' Iio (0 : ℝ) = (∅ : Set (Ico (0 : ℝ) ℓ)) := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt.mpr x.property.1
  simp [he]

/-- The finite-source realization is carried by its actual half-open
physical domain; no mass is placed at or beyond the excluded endpoint. -/
theorem finiteSourceMeasure_outside {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) :
    finiteSourceMeasure f (Ico (0 : ℝ) ℓ)ᶜ = 0 := by
  rw [finiteSourceMeasure, Measure.add_apply,
    Measure.map_apply measurable_subtype_coe measurableSet_Ico.compl]
  have he : Subtype.val ⁻¹' (Ico (0 : ℝ) ℓ)ᶜ = (∅ : Set (Ico (0 : ℝ) ℓ)) := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false]
    exact ⟨fun h ↦ h x.property, False.elim⟩
  have hzero : (0 : ℝ) ∉ (Ico (0 : ℝ) ℓ)ᶜ := fun h ↦ h ⟨le_rfl, hℓ⟩
  rw [Measure.dirac_apply' 0 measurableSet_Ico.compl, indicator_of_notMem hzero, he,
    measure_empty, add_zero]

/-- The finite-source realization has exactly the source half-open mass
increments, preserving every positive-position atom and excluding zero. -/
theorem finiteSourceMeasure_Ioc {ℓ a b : ℝ}
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (ha : a ∈ Ico (0 : ℝ) ℓ) (hb : b ∈ Ico (0 : ℝ) ℓ) :
    finiteSourceMeasure f (Ioc a b) = ENNReal.ofReal (f ⟨b, hb⟩ - f ⟨a, ha⟩) := by
  rw [finiteSourceMeasure, Measure.add_apply,
    Measure.map_apply measurable_subtype_coe measurableSet_Ioc]
  have he : Subtype.val ⁻¹' Ioc a b =
      Ioc (⟨a, ha⟩ : Ico (0 : ℝ) ℓ) ⟨b, hb⟩ := by
    ext x
    rfl
  have hzero : (0 : ℝ) ∉ Ioc a b := fun h ↦ (not_lt.mpr ha.1) h.1
  rw [Measure.dirac_apply' 0 measurableSet_Ioc, indicator_of_notMem hzero,
    zero_add, he, f.measure_Ioc]

/-- Every compact prefix has its actual finite source mass; no endpoint
bound is used. The formula also records the restored unit left atom. -/
theorem finiteSourceMeasure_Icc {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (L : ℝ≥0) (hL : (L : ℝ) < ℓ) :
    finiteSourceMeasure f (Icc 0 (L : ℝ)) =
      1 + ENNReal.ofReal (f ⟨L, ⟨L.property, hL⟩⟩ - f ⟨0, ⟨le_rfl, hℓ⟩⟩) := by
  have he : Icc (0 : ℝ) L = {0} ∪ Ioc 0 (L : ℝ) := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · intro hx
      exact (eq_or_lt_of_le hx.1).elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr ⟨h, hx.2⟩)
    · rintro (rfl | hx)
      · exact ⟨le_rfl, L.property⟩
      · exact ⟨hx.1.le, hx.2⟩
  rw [he, measure_union (by simp) measurableSet_Ioc, finiteSourceMeasure_origin hℓ f]
  exact congrArg (fun a : ENNReal ↦ 1 + a)
    (finiteSourceMeasure_Ioc f ⟨le_rfl, hℓ⟩ ⟨L.property, hL⟩)

/-- Actual source prefixes below the excluded endpoint have finite mass,
even for a source whose total mass is infinite. -/
theorem finiteSourceMeasure_prefix_finite {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (L : ℝ≥0) (hL : (L : ℝ) < ℓ) :
    finiteSourceMeasure f (Icc 0 (L : ℝ)) ≠ ⊤ := by
  rw [finiteSourceMeasure_Icc hℓ f L hL]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩

/-- The single source measure and each earlier compact global representative
agree on every measurable post-origin set, including all interior atoms. -/
theorem finiteSourceMeasure_restrict_Ioc {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) (L : ℝ≥0) (hL : (L : ℝ) < ℓ) :
    (finiteSourceMeasure f).restrict (Ioc 0 (L : ℝ)) =
      (LocalMass.ofFiniteWindow hL f hinit).measure.restrict (Ioc 0 (L : ℝ)) := by
  have : IsFiniteMeasure ((finiteSourceMeasure f).restrict (Ioc 0 (L : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Ioc_subset_Icc_self).trans_lt
      (lt_top_iff_ne_top.mpr (finiteSourceMeasure_prefix_finite hℓ f L hL))
  apply Measure.ext_of_Ioc
  intro a b _hab
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  by_cases hnonempty : max a 0 < min b (L : ℝ)
  · have hlo : max a 0 ∈ Icc 0 (L : ℝ) :=
      ⟨le_max_right _ _, hnonempty.le.trans (min_le_right _ _)⟩
    have hhi : min b (L : ℝ) ∈ Icc 0 (L : ℝ) :=
      ⟨(le_max_right _ _).trans hnonempty.le, min_le_right _ _⟩
    rw [finiteSourceMeasure_Ioc f ⟨hlo.1, hlo.2.trans_lt hL⟩
      ⟨hhi.1, hhi.2.trans_lt hL⟩,
      LocalMass.ofFiniteWindow_measure_Ioc hL f hinit hlo hhi]
  · simp only [Ioc_eq_empty hnonempty, measure_empty]

/-- The distinguished atom and all compact positive increments agree with
the compact state construction on the complete closed prefix. -/
theorem finiteSourceMeasure_restrict_Icc {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) (L : ℝ≥0) (hL : (L : ℝ) < ℓ) :
    (finiteSourceMeasure f).restrict (Icc 0 (L : ℝ)) =
      (LocalMass.ofFiniteWindow hL f hinit).measure.restrict (Icc 0 (L : ℝ)) := by
  have he : Icc (0 : ℝ) L = {0} ∪ Ioc 0 (L : ℝ) := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · intro hx
      exact (eq_or_lt_of_le hx.1).elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr ⟨h, hx.2⟩)
    · rintro (rfl | hx)
      · exact ⟨le_rfl, L.property⟩
      · exact ⟨hx.1.le, hx.2⟩
  rw [he, Measure.restrict_union (by simp) measurableSet_Ioc,
    Measure.restrict_union (by simp) measurableSet_Ioc,
    finiteSourceMeasure_restrict_Ioc hℓ f hinit L hL]
  congr 1
  rw [Measure.restrict_singleton, Measure.restrict_singleton,
    finiteSourceMeasure_origin hℓ f, Mass.measure_origin]

/-- Actual source mass divergence forces infinite mass on every prefix
reaching the finite endpoint. Thus the energy construction does not silently
add finite-mass windows across a singular excluded endpoint. -/
theorem finiteSourceMeasure_prefix_infinite {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hunbounded : ∀ R : ℝ, ∃ x : Ico (0 : ℝ) ℓ, R ≤ f x)
    {L : ℝ} (hL : ℓ ≤ L) : finiteSourceMeasure f (Icc 0 L) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro R
  obtain ⟨x, hx⟩ := hunbounded ((R : ℝ) + f ⟨0, ⟨le_rfl, hℓ⟩⟩)
  have hbound : (R : ℝ) ≤ f x - f ⟨0, ⟨le_rfl, hℓ⟩⟩ := by linarith
  calc
    (R : ENNReal) = ENNReal.ofReal (R : ℝ) := by simp
    _ ≤ ENNReal.ofReal (f x - f ⟨0, ⟨le_rfl, hℓ⟩⟩) := ENNReal.ofReal_le_ofReal hbound
    _ = finiteSourceMeasure f (Ioc 0 (x : ℝ)) :=
      (finiteSourceMeasure_Ioc f ⟨le_rfl, hℓ⟩ x.property).symm
    _ ≤ finiteSourceMeasure f (Icc 0 L) := measure_mono fun y hy ↦
      ⟨hy.1.le, hy.2.trans (x.property.2.le.trans hL)⟩

end
end krylov.Strings.GeneralSpectral
