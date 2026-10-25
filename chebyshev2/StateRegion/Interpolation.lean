import chebyshev2.StateRegion.Coordinates

/-!
Article: chebyshev2, Lemma 8.
Exact rational Hermite certificates for Proposition 12.
Use: `chebyshev2.StateRegion.Scales.g_le_upperInterpolant` feeds
`chebyshev2.StateRegion.Scales.third_moment_bounds` (third moment bounds).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false

/--
Defines `lowerB` of type `ℝ` by `S.k₀^2*S.b/(S.gap*(S.E y)^2)`.

Use: `chebyshev2.StateRegion.Scales.lowerInterpolant` uses this definition in the displayed
construction of `lowerInterpolant`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def lowerB (y : ℝ) : ℝ := S.k₀^2*S.b/(S.gap*(S.E y)^2)
/--
Defines `lowerC` of type `ℝ` by `-S.a*(S.D y)^2/(S.gap*(S.E y)^2)`.

Use: `chebyshev2.StateRegion.Scales.lowerInterpolant` uses this definition in the displayed
construction of `lowerInterpolant`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def lowerC (y : ℝ) : ℝ := -S.a*(S.D y)^2/(S.gap*(S.E y)^2)
/--
Defines `upperB` of type `ℝ` by `S.k*S.k₀*S.b/(S.gap*(S.E y)^2)`.

Use: `chebyshev2.StateRegion.Scales.upperInterpolant` uses this definition in the displayed
construction of `upperInterpolant`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def upperB (y : ℝ) : ℝ := S.k*S.k₀*S.b/(S.gap*(S.E y)^2)
/--
Defines `upperC` of type `ℝ` by `-S.k*S.a*(S.D y)^2/(S.gap*S.k₁*(S.E y)^2)`.

Use: `chebyshev2.StateRegion.Scales.upperInterpolant` uses this definition in the displayed
construction of `upperInterpolant`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def upperC (y : ℝ) : ℝ := -S.k*S.a*(S.D y)^2/(S.gap*S.k₁*(S.E y)^2)
/--
Defines `lowerInterpolant` of type `ℝ` by `S.lowerB y*w+S.lowerC y*S.f w`.

Use: `chebyshev2.StateRegion.Scales.lower_contact` rewrites with this definition to
establish exact identity `S.lowerInterpolant y 0 = S.g 0 ∧ S.lowerInterpolant y y = S.g y`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def lowerInterpolant (y w : ℝ) : ℝ := S.lowerB y*w+S.lowerC y*S.f w
/--
Defines `upperInterpolant` of type `ℝ` by `1+S.upperB y*(w-1)+S.upperC y*(S.f w-1)`.

Use: `chebyshev2.StateRegion.Scales.upper_contact` rewrites with this definition to
establish exact identity `S.upperInterpolant y 1 = S.g 1 ∧ S.upperInterpolant y y = S.g y`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def upperInterpolant (y w : ℝ) : ℝ :=
  1+S.upperB y*(w-1)+S.upperC y*(S.f w-1)

/--
Exact identity `S.g w-S.lowerInterpolant y w = S.k₀^2*S.a*S.b*w*(w-y)^2 / ((S.E y)^2*S.E w*S.D
w)`.

Use: `chebyshev2.StateRegion.Scales.lowerInterpolant_le` uses this identity to establish
the stated quantitative bound `S.lowerInterpolant y w ≤ S.g w`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem lower_remainder {y w : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    S.g w-S.lowerInterpolant y w =
      S.k₀^2*S.a*S.b*w*(w-y)^2 / ((S.E y)^2*S.E w*S.D w) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he := (S.E_pos hy.1).ne'
  have hew := (S.E_pos hw.1).ne'
  have hd := (S.D_pos hw.2).ne'
  dsimp [g,lowerInterpolant,lowerB,lowerC,f]
  field_simp [S.gap_pos.ne']
  dsimp [E,D,k₀,k₁,b]
  ring

/--
Exact identity `S.g w-S.upperInterpolant y w = S.k₀*S.k*S.a*S.b*(w-1)*(w-y)^2 / ((S.E y)^2*S.E
w*S.D w)`.

Use: `chebyshev2.StateRegion.Scales.g_le_upperInterpolant` uses this identity to establish
the stated quantitative bound `S.g w ≤ S.upperInterpolant y w`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem upper_remainder {y w : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    S.g w-S.upperInterpolant y w =
      S.k₀*S.k*S.a*S.b*(w-1)*(w-y)^2 / ((S.E y)^2*S.E w*S.D w) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he := (S.E_pos hy.1).ne'
  have hew := (S.E_pos hw.1).ne'
  have hd := (S.D_pos hw.2).ne'
  dsimp [g,upperInterpolant,upperB,upperC,f]
  field_simp [S.gap_pos.ne',S.k₁_pos.ne']
  dsimp [E,D,k₀,k₁,b]
  ring

/--
The stated quantitative bound `S.lowerInterpolant y w ≤ S.g w`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` uses this bound to establish the
stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ) ≤ ∫ w, S.g w
∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w ∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.lower_remainder`,
`chebyshev2.StateRegion.Scales.E_pos`, `chebyshev2.StateRegion.Scales.D_pos` with the
arguments shown in the proof.
-/
theorem lowerInterpolant_le {y w : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) : S.lowerInterpolant y w ≤ S.g w := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.lower_remainder`,
  -- `chebyshev2.StateRegion.Scales.E_pos`, `chebyshev2.StateRegion.Scales.D_pos` with
  -- the arguments shown in the proof.
  have hr := S.lower_remainder hy hw
  have hb : 0 < S.b := add_pos S.a_pos S.gap_pos
  have ha := S.a_pos
  have hw0 := hw.1
  have he := S.E_pos hw.1
  have hd := S.D_pos hw.2
  have hn : 0 ≤ S.k₀^2*S.a*S.b*w*(w-y)^2 / ((S.E y)^2*S.E w*S.D w) := by
    exact div_nonneg (by positivity) (by positivity)
  linarith

/--
The stated quantitative bound `S.g w ≤ S.upperInterpolant y w`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` uses this bound to establish the
stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ) ≤ ∫ w, S.g w
∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w ∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.upper_remainder`,
`chebyshev2.StateRegion.Scales.k₀_pos`, `chebyshev2.StateRegion.Scales.E_pos` with the
arguments shown in the proof.
-/
theorem g_le_upperInterpolant {y w : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) : S.g w ≤ S.upperInterpolant y w := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.upper_remainder`,
  -- `chebyshev2.StateRegion.Scales.k₀_pos`, `chebyshev2.StateRegion.Scales.E_pos` with
  -- the arguments shown in the proof.
  have hr := S.upper_remainder hy hw
  have hb : 0 < S.b := add_pos S.a_pos S.gap_pos
  have ha := S.a_pos
  have hk := S.k_pos
  have hk₀ := S.k₀_pos
  have hn : S.k₀*S.k*S.a*S.b*(w-1)*(w-y)^2 / ((S.E y)^2*S.E w*S.D w) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hw.2)) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (S.E_pos hw.1).le) (S.D_pos hw.2).le
  linarith

/--
Exact identity `S.lowerInterpolant y 0 = S.g 0 ∧ S.lowerInterpolant y y = S.g y`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.lower_remainder` with
the arguments shown in the proof.
-/
theorem lower_contact {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    S.lowerInterpolant y 0 = S.g 0 ∧ S.lowerInterpolant y y = S.g y := by
  constructor
  · simp [lowerInterpolant]
  · have h := S.lower_remainder hy hy
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_div] at h
    linarith

/--
Exact identity `S.upperInterpolant y 1 = S.g 1 ∧ S.upperInterpolant y y = S.g y`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.upper_remainder` with
the arguments shown in the proof.
-/
theorem upper_contact {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    S.upperInterpolant y 1 = S.g 1 ∧ S.upperInterpolant y y = S.g y := by
  constructor
  · simp [upperInterpolant]
  · have h := S.upper_remainder hy hy
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_div] at h
    linarith

end
end chebyshev2.StateRegion.Scales
