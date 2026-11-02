import krylov.Strings.LocalMass
import krylov.Strings.State
import krylov.Strings.TypeClock

/-!
Article: main_krylov, s3:def:string and apC:eq:state, finite-endpoint locality.
Use: prove that constant extensions on different windows do not change
the physical state or type clock on their common earlier window.
Source: restriction of measures, locality of Radon–Nikodym derivatives and
the already proved uniqueness of the actual measure-driven state.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace Mass

/-- Agreement of mass on a window gives agreement on every earlier
post-origin interval, including all its right-endpoint atoms. -/
theorem restrict_initial_eq_of_restrict_eq (M N : Mass) {L x : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L)) (hx : x ≤ L) :
    M.measure.restrict (Ioc 0 x) = N.measure.restrict (Ioc 0 x) := by
  have hsub : Ioc (0 : ℝ) x ⊆ Ioc 0 L := fun _ ht ↦ ⟨ht.1, ht.2.trans hx⟩
  rw [← Measure.restrict_restrict_of_subset hsub, hμ,
    Measure.restrict_restrict_of_subset hsub]

/-- Locality of the actual type density follows from locality of rnDeriv;
it is an almost-everywhere equality, not a pointwise choice of densities. -/
theorem typeDensity_eq_ae_of_restrict_eq (M N : Mass) {L : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L)) :
    M.typeDensity =ᵐ[volume.restrict (Ioc 0 L)] N.typeDensity := by
  have : IsLocallyFiniteMeasure M.measure := by dsimp [measure]; infer_instance
  have : IsLocallyFiniteMeasure N.measure := by dsimp [measure]; infer_instance
  have hM := Measure.rnDeriv_restrict M.measure volume (s := Ioc (0 : ℝ) L) measurableSet_Ioc
  have hN := Measure.rnDeriv_restrict N.measure volume (s := Ioc (0 : ℝ) L) measurableSet_Ioc
  have he : (M.measure.restrict (Ioc 0 L)).rnDeriv volume =
      (N.measure.restrict (Ioc 0 L)).rnDeriv volume := congrArg (fun μ ↦ μ.rnDeriv volume) hμ
  have hi := hM.symm.trans ((Filter.EventuallyEq.of_eq he).trans hN)
  filter_upwards [ae_restrict_of_ae hi, ae_restrict_mem measurableSet_Ioc] with x hx hxmem
  rw [indicator_of_mem hxmem, indicator_of_mem hxmem] at hx
  exact congrArg (fun z : ℝ≥0∞ ↦ Real.sqrt z.toReal) hx

/-- The clock is independent of the chosen constant extension. -/
theorem typeClock_eq_of_restrict_eq (M N : Mass) {L x : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hx₀ : 0 ≤ x) (hx : x ≤ L) : M.typeClock x = N.typeClock x := by
  rw [M.typeClock_eq_integral hx₀, N.typeClock_eq_integral hx₀]
  exact integral_congr_ae
    (M.typeDensity_eq_ae_of_restrict_eq N (M.restrict_initial_eq_of_restrict_eq N hμ hx))

/-- Two actual state constructions using different mass extensions agree
where the extensions represent the same source mass. -/
theorem state_eq_of_restrict_eq (M N : Mass) (L : ℝ≥0) {φ ψ : ℝ → ℝ}
    (hμ : M.measure.restrict (Ioc 0 (L : ℝ)) = N.measure.restrict (Ioc 0 (L : ℝ)))
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (heφ : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ∈ Icc 0 (L : ℝ), ψ x = 1 + ∫ t in Ioc 0 x, integralSlope N.measure ψ t) :
    EqOn φ ψ (Icc 0 (L : ℝ)) := by
  apply M.state_unique_on L hφ hψ heφ
  intro x hx
  rw [heψ x hx]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp [integralSlope]
  rw [M.restrict_initial_eq_of_restrict_eq N hμ (ht.2.trans hx.2)]

end Mass
end
end krylov.Strings
