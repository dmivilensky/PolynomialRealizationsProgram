import chebyshev1.SineJacobi.PotentialBounds
import chebyshev1.Analysis.WeightedDerivatives

/-!
Article: chebyshev1, Theorem 5.2.
Weighted bounds hold on either side of the interval, without endpoint derivatives.
Use: `chebyshev1.SineJacobi.sineProfile_weighted_derivatives` feeds
`chebyshev1.SineJacobi.energyDensity_weighted_derivatives` (Explicit fourth-order control for
the actual squared density).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology chebyshev1.Analysis

/--
The first five actual derivatives, with the ODE supplying orders two to four.

Use: `chebyshev1.SineJacobi.profileDerivative_eq` rewrites with this definition to
establish exact identity `iteratedDeriv n sineProfile t = profileDerivative n t`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def profileDerivative : ℕ → ℝ → ℝ
  | 0 => sineProfile
  | 1 => sineProfile₁
  | 2 => sineProfile₂
  | 3 => sineProfile₃
  | _ => sineProfile₄

/--
Defines `profileDerivativeBound` by pattern matching with result type `ℕ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev1.SineJacobi.sineProfile_weighted_derivatives` uses this definition to
establish the stated quantitative bound `WeightedDerivatives sineProfile x r (fun n =>
profileDerivativeBound n*sineProfile x) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def profileDerivativeBound : ℕ → ℝ
  | 0 | 1 | 2 => 1
  | 3 => 5
  | _ => 41

/--
Exact identity `iteratedDeriv n sineProfile t = profileDerivative n t`.

Use: `chebyshev1.SineJacobi.sineProfile_weighted_derivatives` rewrites with this identity
to prove the bound `WeightedDerivatives sineProfile x r (fun n =>
profileDerivativeBound n*sineProfile x) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.Analysis.iteratedDeriv_eq_of_derivatives`,
`chebyshev1.SineJacobi.sineProfile₃_deriv`, `chebyshev1.SineJacobi.sineProfile₂_deriv`
with the arguments shown in the proof.
-/
theorem profileDerivative_eq {n : ℕ} (hn : n ≤ 4) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    iteratedDeriv n sineProfile t = profileDerivative n t := by
  -- Use the identities/estimates `chebyshev1.Analysis.iteratedDeriv_eq_of_derivatives`,
  -- `chebyshev1.SineJacobi.sineProfile₃_deriv`,
  -- `chebyshev1.SineJacobi.sineProfile₂_deriv` with the arguments shown in the proof.
  apply iteratedDeriv_eq_of_derivatives isOpen_Ioo (F := profileDerivative) (m := 4) _ n hn ht
  intro j hj x hx
  interval_cases j <;> simp only [profileDerivative]
  · exact sineProfile_deriv hx
  · exact sineProfile₁_deriv hx
  · exact sineProfile₂_deriv hx
  · exact sineProfile₃_deriv hx

/--
Weighted bounds hold on either side of the interval, without endpoint derivatives.

The stated quantitative bound `WeightedDerivatives sineProfile x r (fun n =>
profileDerivativeBound n*sineProfile x) 4`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this identity to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_pos`,
`chebyshev1.SineJacobi.sineProfile_slope_bounds`,
`chebyshev1.SineJacobi.sineProfile₂_eq` with the arguments shown in the proof.
-/
theorem sineProfile_weighted_derivatives {x r : ℝ} (hx : x ∈ Ioo (0:ℝ) 1)
    (hr : 0 < r) (hrx : r ≤ x) (hrx' : r ≤ 1-x)
    (hq : |profilePotential x| * r^2 ≤ 1)
    (hq₁ : |profilePotential₁ x| * r^3 ≤ 4)
    (hq₂ : |profilePotential₂ x| * r^4 ≤ 32) :
    WeightedDerivatives sineProfile x r
      (fun n => profileDerivativeBound n*sineProfile x) 4 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_pos`,
  -- `chebyshev1.SineJacobi.sineProfile_slope_bounds`,
  -- `chebyshev1.SineJacobi.sineProfile₂_eq` with the arguments shown in the proof.
  have hp := (sineProfile_pos hx).le
  have h0 : |sineProfile x| * r^0 ≤ sineProfile x := by simp [abs_of_nonneg hp]
  have h1 : |sineProfile₁ x| * r ≤ sineProfile x := by
    rw [← le_div_iff₀ hr]
    apply abs_le.mpr
    have hs := sineProfile_slope_bounds hx
    rw [neg_div] at hs
    constructor
    · have hh := div_le_div_of_nonneg_left hp hr hrx'
      linarith [hs.1]
    · exact hs.2.trans (div_le_div_of_nonneg_left hp hr hrx)
  have h2 : |sineProfile₂ x| * r^2 ≤ sineProfile x := by
    rw [sineProfile₂_eq hx, abs_mul, abs_neg]
    simpa [mul_comm, mul_left_comm, mul_assoc] using weighted_mul hr.le hq h0
  have h3 : |sineProfile₃ x| * r^3 ≤ 5*sineProfile x := by
    have ha := weighted_mul hr.le hq₁ h0
    have hb := weighted_mul hr.le hq (show |sineProfile₁ x| * r^1 ≤ sineProfile x by simpa using h1)
    simp only [Nat.add_zero, Nat.reduceAdd, one_mul] at ha hb
    calc
      _ ≤ (|profilePotential₁ x*sineProfile x| + |profilePotential x*sineProfile₁ x|)*r^3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [sineProfile₃, neg_mul, abs_neg] using
          abs_sub (-(profilePotential₁ x*sineProfile x)) (profilePotential x*sineProfile₁ x)
      _ ≤ _ := by linarith
  have h4 : |sineProfile₄ x| * r^4 ≤ 41*sineProfile x := by
    have ha := weighted_mul hr.le hq₂ h0
    have hb := weighted_mul hr.le hq₁ (show |sineProfile₁ x| * r^1 ≤ sineProfile x by simpa using h1)
    have hc := weighted_mul hr.le hq h2
    simp only [Nat.add_zero, Nat.reduceAdd, one_mul] at ha hb hc
    calc
      _ ≤ (|profilePotential₂ x*sineProfile x| + 2*|profilePotential₁ x*sineProfile₁ x| +
          |profilePotential x*sineProfile₂ x|)*r^4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        unfold sineProfile₄
        have hh := (abs_sub (-profilePotential₂ x*sineProfile x-
          2*profilePotential₁ x*sineProfile₁ x) (profilePotential x*sineProfile₂ x)).trans
          (add_le_add (abs_sub (-profilePotential₂ x*sineProfile x)
            (2*profilePotential₁ x*sineProfile₁ x)) le_rfl)
        simpa only [neg_mul, abs_neg, mul_assoc, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using hh
      _ ≤ _ := by linarith
  intro n hn
  rw [profileDerivative_eq hn hx]
  interval_cases n
  · simpa [profileDerivative, profileDerivativeBound] using h0
  · simpa [profileDerivative, profileDerivativeBound] using h1
  · simpa [profileDerivative, profileDerivativeBound] using h2
  · simpa [profileDerivative, profileDerivativeBound] using h3
  · simpa [profileDerivative, profileDerivativeBound] using h4

end
end chebyshev1.SineJacobi
