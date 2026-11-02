import krylov.Strings.TypeChangeAE
import krylov.Strings.TypeClockRegularity
import krylov.Strings.ACStateDerivatives

/-!
Article: main_krylov, apC:eq:reduced.
Use: derive all printed reduced equations in the actual inverse type time
for every absolutely continuous post-origin string with positive density
almost everywhere. The clock, inverse, slope and energy are the actual
measure-defined objects. No continuous representative of the density is
required and every derivative conclusion is almost everywhere in type.
Source: Lebesgue FTC, the Jacobian good-set argument, the ordinary inverse
rule and the already proved coordinate algebra in `FeedbackAlgebra`.
-/

namespace krylov.Strings.TypeChange
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The article's control evaluated at the actual inverse physical position. -/
def control (φ p v X : ℝ → ℝ) (y : ℝ) : ℝ :=
  p (X y) / (v (X y) * φ (X y))

/-- The printed reduced equations, together with the actual inverse-clock
rate. This predicate only packages conclusions, not assumed dynamics. -/
def ReducedAt (φ p K v X : ℝ → ℝ) (y : ℝ) : Prop :=
  HasDerivAt X (v (X y))⁻¹ y ∧
  HasDerivAt (fun z ↦ Real.log (φ (X z))) (control φ p v X y) y ∧
  HasDerivAt (fun z ↦ Real.log (p (X z))) (control φ p v X y)⁻¹ y ∧
  HasDerivAt (fun z ↦ Real.log (K (X z)))
    (stateRatio (φ (X y)) (p (X y)) (K (X y)) / control φ p v X y) y ∧
  HasDerivAt (fun z ↦ stateRatio (φ (X z)) (p (X z)) (K (X z)))
    (stateRatio (φ (X y)) (p (X y)) (K (X y)) / control φ p v X y *
      (control φ p v X y ^ 2 + 1 - stateRatio (φ (X y)) (p (X y)) (K (X y)))) y

/-- Ordinary chain and inverse rules give the reduced equations at every
physical good point, without differentiating the measurable density. -/
theorem reduced_at_inverse {a b : ℝ} {Y v φ p K : ℝ → ℝ} {y : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (hm : StrictMonoOn Y (Icc a b)) (hy : y ∈ Ioo (Y a) (Y b))
    (hv : v (inverse Y a b y) ≠ 0)
    (hφn : φ (inverse Y a b y) ≠ 0) (hpn : p (inverse Y a b y) ≠ 0)
    (hKn : K (inverse Y a b y) ≠ 0)
    (hY : HasDerivAt Y (v (inverse Y a b y)) (inverse Y a b y))
    (hφ : HasDerivAt φ (p (inverse Y a b y)) (inverse Y a b y))
    (hp : HasDerivAt p (φ (inverse Y a b y) * v (inverse Y a b y) ^ 2)
      (inverse Y a b y))
    (hK : HasDerivAt K (φ (inverse Y a b y) ^ 2 * v (inverse Y a b y) ^ 2)
      (inverse Y a b y)) :
    ReducedAt φ p K v (inverse Y a b) y := by
  let X := inverse Y a b
  let t := control φ p v X y
  have hX := inverse_hasDerivAt hab hc hm hy hY hv
  have ht : t ≠ 0 := div_ne_zero hpn (mul_ne_zero hv hφn)
  have hdφ : HasDerivAt (fun z ↦ φ (X z)) (t * φ (X y)) y := by
    convert hφ.comp y hX using 1
    · rfl
    · dsimp [t, control, X]
      field_simp
  have hdp : HasDerivAt (fun z ↦ p (X z)) (p (X y) / t) y := by
    convert hp.comp y hX using 1
    · rfl
    · dsimp [t, control, X]
      field_simp
  have hdK : HasDerivAt (fun z ↦ K (X z))
      (stateRatio (φ (X y)) (p (X y)) (K (X y)) * K (X y) / t) y := by
    convert hK.comp y hX using 1
    · rfl
    · dsimp [t, control, stateRatio, X]
      field_simp
  obtain ⟨hlogφ, hlogp, hlogK⟩ := feedback_log_rates hdφ hdp hdK hφn hpn hKn
  exact ⟨hX, hlogφ, hlogp, hlogK, stateRatio_type_derivative hdφ hdp hdK hKn ht⟩

/-- Positivity is derived from the actual finite-window Volterra equation,
rather than inserted as an extra admissibility hypothesis. -/
theorem actual_state_positive (M : Mass) (L : ℝ≥0) {φ : ℝ → ℝ}
    (hc : Continuous φ)
    (he : ∀ x ∈ Icc 0 (L : ℝ),
      φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t) :
    ∀ x ∈ Icc 0 (L : ℝ),
      0 < φ x ∧ 0 < integralSlope M.measure φ x ∧ 0 < integralEnergy M.measure φ x := by
  obtain ⟨ψ, hcψ, _, _, hψ⟩ := M.exists_state_on L
  have heq := M.state_unique_on L hc hcψ he (fun x hx ↦ (hψ x hx).1)
  intro x hx
  have hp : integralSlope M.measure φ x = integralSlope M.measure ψ x := by
    dsimp [integralSlope]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact heq ⟨ht.1.le, ht.2.trans hx.2⟩
  have hφ := (hψ x hx).2.1
  have hpx := (hψ x hx).2.2.1
  rw [heq hx, hp]
  exact ⟨by linarith [hx.1], by linarith, by linarith [integralEnergy_one_le M.measure φ x]⟩

/-- Full actual type change for an arbitrary absolutely continuous string
on a finite physical window. The positive density hypothesis is only a.e.;
the actual singular part vanishes on the post-origin window, leaving the
prescribed origin atom untouched. All four printed reduced equations hold
a.e. in the actual type variable. -/
theorem actual_reduced_ae (M : Mass) (L : ℝ≥0) (hL : 0 < L) {φ : ℝ → ℝ}
    (hc : Continuous φ)
    (he : ∀ x ∈ Icc 0 (L : ℝ),
      φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hv : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → 0 < M.typeDensity x) :
    ∀ᵐ y : ℝ, y ∈ Ioo 0 (M.typeClock L) →
      ReducedAt φ (integralSlope M.measure φ) (integralEnergy M.measure φ)
        M.typeDensity (inverse M.typeClock 0 L) y := by
  have hm := M.typeClock_strictMonoOn L hv
  have hclock := M.typeClock_ae_hasDerivAt L
  have hφ : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) →
      HasDerivAt φ (integralSlope M.measure φ x) x := by
    obtain ⟨ψ, hcψ, h₀, hmψ, hψ⟩ := M.exists_state_on L
    have heq := M.state_unique_on L hc hcψ he (fun x hx ↦ (hψ x hx).1)
    have hd := M.position_ae_hasDerivAt L hcψ hmψ h₀ (fun x hx ↦ (hψ x hx).1)
    filter_upwards [hd] with x hx hxin
    have hsp : integralSlope M.measure ψ x = integralSlope M.measure φ x := by
      dsimp [integralSlope]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact (heq ⟨ht.1.le, ht.2.trans hxin.2.le⟩).symm
    rw [← hsp]
    apply (hx hxin).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxin.1 hxin.2] with t ht
    exact heq ⟨ht.1.le, ht.2.le⟩
  have hphys := M.slope_energy_ae_hasDerivAt L hc hSing
  have hP : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) →
      0 < M.typeDensity x ∧ HasDerivAt M.typeClock (M.typeDensity x) x ∧
      HasDerivAt φ (integralSlope M.measure φ x) x ∧
      HasDerivAt (integralSlope M.measure φ) (φ x * M.typeDensity x ^ 2) x ∧
      HasDerivAt (integralEnergy M.measure φ) (φ x ^ 2 * M.typeDensity x ^ 2) x := by
    filter_upwards [hv, hclock, hφ, hphys] with x hxv hxY hxφ hxphys hxin
    exact ⟨hxv hxin, hxY hxin, hxφ hxin, hxphys hxin⟩
  have htransfer := ae_transfer (Y := M.typeClock) (v := M.typeDensity)
    (show (0 : ℝ) < (L : ℝ) from hL) hm (M.typeDensity_intervalIntegrable 0 L)
    (fun x _ ↦ M.typeDensity_nonneg x) (M.typeClock_sub 0 L) hclock hP
  filter_upwards [htransfer] with y hy hyt
  have hy' : y ∈ Ioo (M.typeClock 0) (M.typeClock L) := by simpa using hyt
  obtain ⟨hxv, hxY, hxφ, hxp, hxK⟩ := hy hy'
  have hxin := inverse_mem_interior L.property M.typeClock_continuous.continuousOn hm hy'
  obtain ⟨hφp, hpp, hKp⟩ := actual_state_positive M L hc he _ (Ioo_subset_Icc_self hxin)
  exact reduced_at_inverse L.property M.typeClock_continuous.continuousOn hm hy'
    hxv.ne' hφp.ne' hpp.ne' hKp.ne' hxY hxφ hxp hxK

end
end krylov.Strings.TypeChange
