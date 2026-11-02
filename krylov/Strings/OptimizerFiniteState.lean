import krylov.Strings.GlobalState
import krylov.Strings.LocalCompatibility
import krylov.Strings.FeedbackMassInvariant

/-!
Article: main_krylov, s3:def:string and apC:eq:state, finite physical lengths.
Use: glue actual compact states for a cumulative mass on `[0,ℓ)` into one
state on that entire domain, even when mass diverges at its excluded endpoint.
Source: compact extension of Stieltjes functions, proved locality of mass and
actual state uniqueness. No bounded mass at the endpoint is assumed.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

/-- Compact windows strictly below the possibly singular physical endpoint. -/
abbrev Windows (ℓ : ℝ) := {L : ℝ≥0 // (L : ℝ) < ℓ}

/-- The genuine compact representative of the given finite-endpoint source. -/
def windowMass {ℓ : ℝ} (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) (w : Windows ℓ) : Mass :=
  LocalMass.ofFiniteWindow w.property f h₀

/-- Different representatives retain exactly the same actual mass on their
common earlier window, including all atoms and singular continuous mass. -/
theorem windowMass_compatible {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (w v : Windows ℓ) :
    (windowMass hℓ f h₀ w).measure.restrict (Ioc 0 ((min w.val v.val : ℝ≥0) : ℝ)) =
      (windowMass hℓ f h₀ v).measure.restrict (Ioc 0 ((min w.val v.val : ℝ≥0) : ℝ)) := by
  apply LocalMass.measure_restrict_eq_of_cumulative_eq
  intro x hx
  have hw : x ∈ Icc 0 (w.val : ℝ) :=
    ⟨hx.1, hx.2.trans (show ((min w.val v.val : ℝ≥0) : ℝ) ≤ (w.val : ℝ) by simp)⟩
  have hv : x ∈ Icc 0 (v.val : ℝ) :=
    ⟨hx.1, hx.2.trans (show ((min w.val v.val : ℝ≥0) : ℝ) ≤ (v.val : ℝ) by simp)⟩
  exact (LocalMass.ofFiniteWindow_cumulative w.property f h₀ hw).trans
    (LocalMass.ofFiniteWindow_cumulative v.property f h₀ hv).symm

/-- States of different compact representatives agree throughout their common
physical window. Agreement follows from the actual state equations. -/
theorem state_compatible {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (w v : Windows ℓ) {φ ψ : ℝ → ℝ} (hcφ : Continuous φ) (hcψ : Continuous ψ)
    (heφ : ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    (heψ : ∀ x ∈ Icc 0 (v.val : ℝ), ψ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ v).measure ψ t) :
    EqOn φ ψ (Icc 0 ((min w.val v.val : ℝ≥0) : ℝ)) := by
  apply Mass.state_eq_of_restrict_eq _ _ (min w.val v.val)
    (windowMass_compatible hℓ f h₀ w v) hcφ hcψ
  · intro x hx
    exact heφ x ⟨hx.1,
      hx.2.trans (show ((min w.val v.val : ℝ≥0) : ℝ) ≤ (w.val : ℝ) by simp)⟩
  · intro x hx
    exact heψ x ⟨hx.1,
      hx.2.trans (show ((min w.val v.val : ℝ≥0) : ℝ) ≤ (v.val : ℝ) by simp)⟩

/-- A finite-endpoint source has an actual state on its entire physical domain.
The single position function satisfies the true integral equation for every
compact representative; its negative extension is constant. The conclusion
permits arbitrarily many atoms and unbounded cumulative mass near `ℓ`.
-/
theorem exists_state {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Iio ℓ) ∧ φ 0 = 1 ∧ MonotoneOn φ (Iio ℓ) ∧
      (∀ x ≤ 0, φ x = 1) ∧ ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ),
        φ x = 1 + ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t := by
  choose F hc hz hm hleft he using
    fun w : Windows ℓ ↦ (windowMass hℓ f h₀ w).exists_state_on_left_constant w.val
  let windowAt (x : ℝ) (hx : x < ℓ) : Windows ℓ :=
    ⟨⟨(max x 0 + ℓ) / 2, by linarith [le_max_right x 0]⟩,
      by
        change (max x 0 + ℓ) / 2 < ℓ
        have hmax : max x 0 < ℓ := max_lt hx hℓ
        linarith⟩
  let φ : ℝ → ℝ := fun x ↦ if hx : x < ℓ then F (windowAt x hx) x else 1
  have hbound (x : ℝ) (hx : x < ℓ) : x < ((windowAt x hx).val : ℝ) := by
    change x < (max x 0 + ℓ) / 2
    linarith [le_max_left x 0]
  have hagree (w : Windows ℓ) {x : ℝ} (hx : x ≤ (w.val : ℝ)) : φ x = F w x := by
    have hxℓ : x < ℓ := hx.trans_lt w.property
    dsimp [φ]
    rw [dite_eq_left hxℓ]
    by_cases hx0 : 0 ≤ x
    · exact state_compatible hℓ f h₀ (windowAt x hxℓ) w (hc _) (hc _) (he _) (he _)
        ⟨hx0, by simpa using le_min (hbound x hxℓ).le hx⟩
    · rw [hleft _ x (le_of_not_ge hx0), hleft _ x (le_of_not_ge hx0)]
  have hcφ : ContinuousOn φ (Iio ℓ) := by
    intro x hx
    let w := windowAt x hx
    have hlt : x < (w.val : ℝ) := hbound x hx
    apply ContinuousAt.continuousWithinAt
    apply (hc w).continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with y hy
    exact hagree w hy.le
  have hzero : φ 0 = 1 := by
    rw [hagree (windowAt 0 hℓ) (hbound 0 hℓ).le, hz]
  have hmφ : MonotoneOn φ (Iio ℓ) := by
    intro x _ y hy hxy
    let w := windowAt y hy
    rw [hagree w (hxy.trans (hbound y hy).le), hagree w (hbound y hy).le]
    exact hm w hxy
  refine ⟨φ, hcφ, hzero, hmφ, ?_, ?_⟩
  · intro x hx
    have hxℓ : x < ℓ := hx.trans_lt hℓ
    have hxw : x ≤ ((windowAt x hxℓ).val : ℝ) := (hbound x hxℓ).le
    rw [hagree (windowAt x hxℓ) hxw, hleft _ x hx]
  · intro w
    apply Mass.position_equation_congr _ w.val (he w)
    intro x hx
    exact (hagree w hx.2).symm

/-- A source state continuous on its open physical domain has a continuous
compact restriction. This does not impose continuity at the excluded endpoint. -/
def stateRestriction {ℓ : ℝ} {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ))
    (w : Windows ℓ) : C(Window w.val, ℝ) where
  toFun x := φ x
  continuous_toFun := hc.comp_continuous continuous_subtype_val
    (fun x ↦ x.property.2.trans_lt w.property)

/-- The actual finite-endpoint state is unique throughout `[0,ℓ)`, including
sources with mass diverging at the endpoint. Neither positivity nor a desired
invariant is included among the uniqueness hypotheses. -/
theorem state_unique {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ ψ : ℝ → ℝ} (hcφ : ContinuousOn φ (Iio ℓ)) (hcψ : ContinuousOn ψ (Iio ℓ))
    (heφ : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    (heψ : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), ψ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure ψ t) :
    EqOn φ ψ (Ico 0 ℓ) := by
  intro x hx
  let w : Windows ℓ := ⟨⟨x, hx.1⟩, hx.2⟩
  let φw : ℝ → ℝ := IccExtend w.val.property (stateRestriction hcφ w)
  let ψw : ℝ → ℝ := IccExtend w.val.property (stateRestriction hcψ w)
  have hagreeφ : EqOn φ φw (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hcφ w) ht).symm
  have hagreeψ : EqOn ψ ψw (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hcψ w) ht).symm
  have hsame := (windowMass hℓ f h₀ w).state_unique_on w.val
    (stateRestriction hcφ w).continuous.Icc_extend'
    (stateRestriction hcψ w).continuous.Icc_extend'
    (Mass.position_equation_congr _ w.val (heφ w) hagreeφ)
    (Mass.position_equation_congr _ w.val (heψ w) hagreeψ)
  have hxw : x ∈ Icc 0 (w.val : ℝ) := ⟨hx.1, le_rfl⟩
  exact (hagreeφ hxw).trans ((hsame hxw).trans (hagreeψ hxw).symm)

/-- Monotonicity of a physical source state passes to its compact restriction. -/
theorem stateRestriction_monotone {ℓ : ℝ} {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ)) (w : Windows ℓ) :
    Monotone (stateRestriction hc w) := by
  intro x y hxy
  exact hm (x.property.2.trans_lt w.property) (y.property.2.trans_lt w.property) hxy

/-- The finite-endpoint source position is absolutely continuous on each
compact physical window. Endpoint divergence and singular mass are allowed. -/
theorem state_absolutelyContinuousOnInterval {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1) (w : Windows ℓ)
    (he : ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t) :
    AbsolutelyContinuousOnInterval φ 0 (w.val : ℝ) := by
  let φw : ℝ → ℝ := IccExtend w.val.property (stateRestriction hc w)
  have hagree : EqOn φ φw (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hc w) ht).symm
  have hzw : φw 0 = 1 := (hagree ⟨le_rfl, w.val.property⟩).symm.trans hz
  have hw := (windowMass hℓ f h₀ w).position_absolutelyContinuousOnInterval w.val
    (stateRestriction hc w).continuous.Icc_extend'
    ((stateRestriction_monotone hc hm w).IccExtend w.val.property) hzw
    (Mass.position_equation_congr _ w.val he hagree)
  apply hw.congr
  intro x hx
  have hL : (0 : ℝ) ≤ (w.val : ℝ) := w.val.property
  rw [uIcc_of_le hL] at hx
  exact (hagree hx).symm

/-- Almost-everywhere differentiation of the actual finite-endpoint state.
The derivative is its own reconstructed cumulative slope, not a supplied
smooth proxy. -/
theorem state_ae_hasDerivAt {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1) (w : Windows ℓ)
    (he : ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t) :
    ∀ᵐ x : ℝ, x ∈ Ioo 0 (w.val : ℝ) →
      HasDerivAt φ (integralSlope (windowMass hℓ f h₀ w).measure φ x) x := by
  let M := windowMass hℓ f h₀ w
  let φw : ℝ → ℝ := IccExtend w.val.property (stateRestriction hc w)
  have hagree : EqOn φ φw (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hc w) ht).symm
  have hzw : φw 0 = 1 := (hagree ⟨le_rfl, w.val.property⟩).symm.trans hz
  have hw := M.position_ae_hasDerivAt w.val
    (stateRestriction hc w).continuous.Icc_extend'
    ((stateRestriction_monotone hc hm w).IccExtend w.val.property) hzw
    (Mass.position_equation_congr _ w.val he hagree)
  filter_upwards [hw] with x hx
  intro hxin
  have hslope : integralSlope M.measure φ x = integralSlope M.measure φw x := by
    apply M.slope_eq_of_eqOn
    intro t ht
    exact hagree ⟨ht.1, ht.2.trans hxin.2.le⟩
  rw [hslope]
  apply (hx hxin).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxin.1 hxin.2] with t ht
  exact hagree ⟨ht.1.le, ht.2.le⟩

/-- The actual finite-endpoint state remains in the Bellman domain on each
compact window; the source may contain atoms or singular continuous mass. -/
theorem state_ratio_ge_one {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1) (w : Windows ℓ) {x : ℝ} (hx : x ∈ Icc 0 (w.val : ℝ)) :
    1 ≤ stateRatio (φ x) (integralSlope (windowMass hℓ f h₀ w).measure φ x)
      (integralEnergy (windowMass hℓ f h₀ w).measure φ x) := by
  have hsub : Icc (0 : ℝ) x ⊆ Iio ℓ := fun _ ht ↦
    (ht.2.trans hx.2).trans_lt w.property
  exact mass_state_ratio_ge_one _ hx.1 hz (hc.mono hsub) (hm.mono hsub)

end
end krylov.Strings.OptimizerFinite
