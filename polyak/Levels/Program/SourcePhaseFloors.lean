import polyak.Levels.Program.SourceBijection
import polyak.Levels.Program.PhaseFloors
import polyak.Duality.Separation

/-! The literal t=0 source certificate criterion in phase-floor coordinates. -/
noncomputable section
namespace polyak.Levels

theorem source_strictCertificate_iff_phaseFloors (q : General.Tuning) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta 0) 0) ↔
      ∃S : CertificateSymbol (tuningCurve q) nonzeroLags,0<S.gamma ∧
        ∀ω:Frequency,0<(ω:ℝ)→phaseFloor S.lags S.weight S.gamma ω<tuningCurve q ω := by
  rw [← Duality.infeasible_iff_strictCertificate,threshold_spectral_C_iff_fp]
  exact (infeasible_iff_strictSymbol _ _).trans (strictSymbol_iff_phaseFloors _ _)

end polyak.Levels
