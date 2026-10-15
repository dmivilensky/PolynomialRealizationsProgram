import «2610.05164v2».PrescribedSpeed.Article

/-!
Article: 2610.05164v2, Theorem 3.4.
Prescribed-speed objects depend only on the speed on [0,2].
Use: `«2610.05164v2».PrescribedSpeed.SpeedData.density_congr` feeds
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_density` (self Consistent density).
Proof chain: `«2610.05164v2».Primal.comparison_density` — 2610.05164v2, Theorem 3.4; Signed
determinant and square-trace comparisons.
-/
namespace «2610.05164v2».PrescribedSpeed.SpeedData
noncomputable section
open Set MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (S T : «2610.05164v2».PrescribedSpeed.SpeedData)

/--
Exact identity `S.reciprocal=T.reciprocal`.

Use: `«2610.05164v2».PrescribedSpeed.SpeedData.X_congr` rewrites with this identity to
establish exact identity `S.X=T.X`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q∈Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem reciprocal_congr (hD : EqOn S.D T.D (Ioo (0:ℝ) 2)) :
    S.reciprocal=T.reciprocal := by
  funext q
  by_cases hq : q∈Ioo (0:ℝ) 2
  · simp only [reciprocal,indicator_of_mem hq,hD hq]
  · simp only [reciprocal,indicator_of_notMem hq]

/--
Exact identity `S.X=T.X`.

Use: `«2610.05164v2».PrescribedSpeed.SpeedData.density_congr` uses this identity to establish
exact identity `S.density κ=T.density κ`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem X_congr (hD : EqOn S.D T.D (Ioo (0:ℝ) 2)) : S.X=T.X := by
  funext q
  simp only [X,reciprocal_congr S T hD]

/--
Exact identity `S.q=T.q`.

Use: `«2610.05164v2».PrescribedSpeed.SpeedData.density_congr` uses this identity to establish
exact identity `S.density κ=T.density κ`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem q_congr (hD : EqOn S.D T.D (Ioo (0:ℝ) 2)) : S.q=T.q := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hX := X_congr S T hD
  funext x
  rcases le_or_gt x (S.X 0) with hl|hl
  · rw [S.q_zero_left hl,T.q_zero_left (by rwa [← hX])]
  · rcases le_or_gt (S.X 2) x with hr|hr
    · rw [S.q_two_right hr,T.q_two_right (by rwa [← hX])]
    · have hx : x∈Icc (S.X 0) (S.X 2) := ⟨hl.le,hr.le⟩
      calc
        S.q x=T.q (T.X (S.q x)) := (T.q_X (S.q_mem x)).symm
        _=T.q x := by rw [← hX,S.X_q hx]

/--
Exact identity `S.density κ=T.density κ`.

Use: `«2610.05164v2».Calibration.Data.comparisonProfile_density` uses this identity to
establish exact identity `(C.comparisonProfile hκ).density hκ=C.comparisonDensity hκ`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `x∈Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem density_congr (hD : EqOn S.D T.D (Ioo (0:ℝ) 2)) (κ : ℝ) :
    S.density κ=T.density κ := by
  -- Separate `x∈Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hX := X_congr S T hD
  have hq := q_congr S T hD
  funext x
  by_cases hx : x∈Ioo (S.X 0) (S.X 2)
  · have hxt : x∈Ioo (T.X 0) (T.X 2) := by rwa [← hX]
    have hq0 : S.q x≠0 := by
      intro hz
      have he := S.X_q ⟨hx.1.le,hx.2.le⟩
      rw [hz] at he
      exact (ne_of_lt hx.1) he
    have hq2 : S.q x≠2 := by
      intro hz
      have he := S.X_q ⟨hx.1.le,hx.2.le⟩
      rw [hz] at he
      exact (ne_of_lt hx.2) he.symm
    have hqi : S.q x∈Ioo (0:ℝ) 2 :=
      ⟨lt_of_le_of_ne (S.q_mem x).1 (Ne.symm hq0),lt_of_le_of_ne (S.q_mem x).2 hq2⟩
    simp only [density,indicator_of_mem hx,indicator_of_mem hxt]
    rw [hD hqi,hq]
    simp only [Q,hq]
  · have hxt : x∉Ioo (T.X 0) (T.X 2) := by rwa [← hX]
    simp only [density,indicator_of_notMem hx,indicator_of_notMem hxt]

end
end «2610.05164v2».PrescribedSpeed.SpeedData
