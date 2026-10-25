import chebyshev1.SineJacobi.ProfileHigherDerivatives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: chebyshev1, Theorem 5.2.
Potential Bounds.
Use: `chebyshev1.SineJacobi.profilePotential_reflection` feeds
`chebyshev1.SineJacobi.energyDensity_weighted_derivatives` (Explicit fourth-order control for
the actual squared density).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set

/--
The stated quantitative bound `|profilePotential t| * t^2 ≤ 1 ∧ |profilePotential₁ t| * t^3 ≤ 4
∧ |profilePotential₂ t| * t^4 ≤ 32`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this bound to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profilePotential_weighted_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/2) :
    |profilePotential t| * t^2 ≤ 1 ∧ |profilePotential₁ t| * t^3 ≤ 4 ∧
      |profilePotential₂ t| * t^4 ≤ 32 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hs : 2*t ≤ sin (Real.pi*t) := by
    have hh := le_sin_mul (show 0 ≤ 2*t by linarith) (show 2*t ≤ 1 by linarith)
    convert hh using 1; ring_nf
  have hsp : 0 < sin (Real.pi*t) := lt_of_lt_of_le (by linarith) hs
  have hs2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*t) hs 2
  have hs3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*t) hs 3
  have hs4 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*t) hs 4
  have hpi : Real.pi ≤ 4 := pi_lt_four.le
  have hp2 := pow_le_pow_left₀ pi_pos.le hpi 2
  have hp3 := pow_le_pow_left₀ pi_pos.le hpi 3
  have hp4 := pow_le_pow_left₀ pi_pos.le hpi 4
  have hc := abs_cos_le_one (Real.pi*t)
  have hc2 := cos_sq_le_one (Real.pi*t)
  have hn0 : 0 ≤ profilePotential t := by unfold profilePotential; positivity
  have hn2 : 0 ≤ profilePotential₂ t := by unfold profilePotential₂; positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg hn0, profilePotential, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : 0 < 4*sin (Real.pi*t)^2)]
    have hh := mul_le_mul_of_nonneg_right hp2 (sq_nonneg t)
    nlinarith [hs2]
  · rw [profilePotential₁, abs_div, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.pi^3),
      abs_of_pos (by positivity : 0 < 2*sin (Real.pi*t)^3), div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : 0 < 2*sin (Real.pi*t)^3)]
    have hh := mul_le_mul hp3 hc (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4^3)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ t^3 by positivity)
    nlinarith [hs3]
  · rw [abs_of_nonneg hn2, profilePotential₂, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : 0 < 2*sin (Real.pi*t)^4)]
    have hh := mul_le_mul hp4 (show 1+2*cos (Real.pi*t)^2 ≤ 3 by linarith)
      (by positivity : 0 ≤ 1+2*cos (Real.pi*t)^2) (by norm_num : (0:ℝ) ≤ 4^4)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ t^4 by positivity)
    nlinarith [hs4]

/--
Exact identity `profilePotential (1-t) = profilePotential t ∧ profilePotential₁ (1-t) =
-profilePotential₁ t ∧ profilePotential₂ (1-t) = profilePotential₂ t`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this identity to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profilePotential_reflection (t : ℝ) :
    profilePotential (1-t) = profilePotential t ∧
      profilePotential₁ (1-t) = -profilePotential₁ t ∧
      profilePotential₂ (1-t) = profilePotential₂ t := by
  simp only [profilePotential, profilePotential₁, profilePotential₂,
    show Real.pi*(1-t) = Real.pi-Real.pi*t by ring, sin_pi_sub, cos_pi_sub, neg_sq]
  refine ⟨trivial, ?_, trivial⟩
  ring

end
end chebyshev1.SineJacobi
