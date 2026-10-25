import polyak.Growth.HorizonCertificate

/-!
Article: Appendix C, the plateau for the genuine finite-memory class.
Use: the same actual finite strict certificates exclude every enlarged memory rate
just above the exact rate. The only certificate-family input is stated explicitly;
source branches supply it separately, with their fixed lag support.
-/
namespace polyak.Growth.FiniteHorizon
noncomputable section
open Set Filter Duality Spectral
open scoped Topology

/-- More retained interpolation pairs can only decrease the actual memory rate. -/
theorem growthRate_antitone_memory {A B β : ℝ} (hB : B≠0) :
    Antitone (growthRate A B β) := by
  intro H K hHK
  apply le_of_tendsto_of_tendsto (tendsto_envelope_root hB K) (tendsto_envelope_root hB H)
  exact Eventually.of_forall (fun n => Real.rpow_le_rpow (envelope_nonneg A B β K n)
    (envelope_antitone_memory A B β hHK n) (by positivity))

/-- A strict certificate using retained lags cannot hold at the exact H-class rate. -/
theorem not_strictCertificate_at_growth {A B β : ℝ} {H : ℕ} (hB : B≠0)
    (cert : StrictCertificate
      (Waves.multiplierMap A B β (Real.log (growthRate A B β H)))
      (Real.log (growthRate A B β H))) (hmem : ∀ n∈cert.lags,n ≤ H) : False := by
  obtain ⟨K,w,hK,henergy⟩ := cert.horizonWindowEnergyBound hB hmem
  exact not_windowEnergyBound_at_growth hB hK henergy

/-- A fixed finite support of actual strict certificates just above the exact rate
forces the finite-memory rate to become exactly equal to it, not merely converge to it. -/
theorem eventually_growthRate_eq_of_certificates {A B β δ : ℝ} {H₀ : ℕ}
    (hB : B≠0) (hδ : 0<δ)
    (hcert : ∀ t : ℝ, Real.log (Growth.growthRate A B β)<t →
      t<Real.log (Growth.growthRate A B β)+δ →
      ∃ cert : StrictCertificate (Waves.multiplierMap A B β t) t,
        ∀ n∈cert.lags,n ≤ H₀) :
    ∀ᶠ H : ℕ in atTop,growthRate A B β H=Growth.growthRate A B β := by
  have hR : Growth.growthRate A B β<
      Real.exp (Real.log (Growth.growthRate A B β)+δ) := by
    calc
      _ = Real.exp (Real.log (Growth.growthRate A B β)) :=
        (Real.exp_log (Growth.growthRate_pos A B β)).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  filter_upwards [eventually_growthRate_lt hB hR,eventually_ge_atTop H₀] with H hH hmem
  apply le_antisymm _ (full_growthRate_le hB H)
  by_contra h
  have hg : Growth.growthRate A B β<growthRate A B β H := lt_of_not_ge h
  have ht : Real.log (Growth.growthRate A B β)<Real.log (growthRate A B β H) :=
    Real.log_lt_log (Growth.growthRate_pos A B β) hg
  have ht' : Real.log (growthRate A B β H)<Real.log (Growth.growthRate A B β)+δ := by
    have hh:=Real.log_lt_log (growthRate_pos A B β H) hH
    rwa [Real.log_exp] at hh
  obtain ⟨cert,hcert⟩ := hcert _ ht ht'
  exact not_strictCertificate_at_growth hB cert (fun n hn => (hcert n hn).trans hmem)

/-- The equality holds for every memory above one finite threshold. -/
theorem exists_memory_preserving_rate {A B β δ : ℝ} {H₀ : ℕ}
    (hB : B≠0) (hδ : 0<δ)
    (hcert : ∀ t : ℝ, Real.log (Growth.growthRate A B β)<t →
      t<Real.log (Growth.growthRate A B β)+δ →
      ∃ cert : StrictCertificate (Waves.multiplierMap A B β t) t,
        ∀ n∈cert.lags,n ≤ H₀) :
    ∃ H₁ : ℕ,∀ H : ℕ,H₁ ≤ H → growthRate A B β H=Growth.growthRate A B β :=
  eventually_atTop.mp (eventually_growthRate_eq_of_certificates hB hδ hcert)

end
end polyak.Growth.FiniteHorizon
