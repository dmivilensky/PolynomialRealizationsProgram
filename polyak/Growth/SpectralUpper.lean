import polyak.Duality.Separation
import polyak.Energy.Estimate
import polyak.Growth.Upper

/-!
Article: Theorem spectralgeneral(b) and Appendix A, Lemma plateau.
Use: the actual finite strict certificate yields the strict original upper rate.
Proof: the proved certificate energy estimate contradicts the growth-exponent plateau;
the original rate is bounded by the genuine free-segment growth rate.
-/

namespace polyak.Growth
noncomputable section
open Duality Spectral

/-- Article: Lemma plateau. Use: no finite strict certificate exists at the exact
growth exponent, for the actual recurrence multiplier. -/
theorem not_strictCertificate_at_growth {A B β : ℝ} (hB : B ≠ 0) :
    ¬ Nonempty (StrictCertificate
      (Waves.multiplierMap A B β (Real.log (growthRate A B β)))
      (Real.log (growthRate A B β))) := by
  rintro ⟨cert⟩
  obtain ⟨K,w,hK,henergy⟩ := cert.windowEnergyBound hB
  exact not_windowEnergyBound_at_growth hB hK henergy

/-- Article: the growth-exponent feasible spectrum. Use: duality applies at the exact
free-state rate, with a genuine probability measure and an actual interpolation parameter. -/
theorem exists_feasible_at_growth {A B β : ℝ} (hB : B ≠ 0) :
    ∃ (ν : Spectrum) (C : ℝ), Waves.MixtureFeasible ν
      (Waves.multiplierMap A B β (Real.log (growthRate A B β))) C
      (Real.log (growthRate A B β)) := by
  by_contra h
  exact not_strictCertificate_at_growth hB
    ((infeasible_iff_strictCertificate _ _).mp h)

/-- Article: spectralgeneral(b), free-state version. Use: strict certificates above
a threshold force a strict upper bound, with no worst-wave assumption. -/
theorem growthRate_lt_exp_of_certificates {A B β t₀ : ℝ} (hB : B ≠ 0)
    (hcert : ∀ t : ℝ, t₀ ≤ t →
      Nonempty (StrictCertificate (Waves.multiplierMap A B β t) t)) :
    growthRate A B β < Real.exp t₀ := by
  apply growthRate_lt_exp_of_windows hB
  intro t ht
  obtain ⟨cert⟩ := hcert t ht
  exact cert.windowEnergyBound hB

/-- Article: Theorem spectralgeneral(b). Use: the original source rate, from rest,
uniformly over every actual smooth strongly convex function and every finite dimension. -/
theorem originalRate_lt_exp_of_certificates {μ L α β t₀ : ℝ}
    (hμ : 0 < μ) (hL : μ < L) (hα : 0 < α) (hβ : 0 ≤ β)
    (hcert : ∀ t : ℝ, t₀ ≤ t → Nonempty (StrictCertificate
      (Waves.multiplierMap (Dynamics.normalizedA μ L α β)
        (Dynamics.normalizedB μ L α) β t) t)) :
    Dynamics.rate μ L α β < Real.exp t₀ := by
  apply originalRate_lt_exp_of_windows hμ hL hα hβ
  intro t ht
  obtain ⟨cert⟩ := hcert t ht
  have hB : Dynamics.normalizedB μ L α ≠ 0 := by
    dsimp [Dynamics.normalizedB]
    positivity
  exact cert.windowEnergyBound hB

end
end polyak.Growth
