import «2610.05164v2».HalfLine.GreenBoundaryValue

/-!
Article: 2610.05164v2, Theorem 6.1.
C.1 uses L1 data on the half-line; no integrability of the arbitrary extension to its right is
required.
Use: `«2610.05164v2».HalfLine.leftDensity_idempotent` feeds
`«2610.05164v2».HalfLine.greenSolution_leftDensity` (green Solution left Density).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `leftDensity (leftDensity j x) x=leftDensity j x`.

Use: `«2610.05164v2».HalfLine.greenSlope_leftDensity` rewrites with this identity to establish
exact identity `greenSlope x (leftDensity j x)=greenSlope x j`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem leftDensity_idempotent (x : ℝ) (j : ℝ → ℝ) : leftDensity (leftDensity j x) x=leftDensity j x := by
  funext t
  by_cases ht : t < x <;> simp [leftDensity,ht]

/--
Exact identity `greenSolution x (leftDensity j x)=greenSolution x j`.

Use: `«2610.05164v2».HalfLine.greenSolution_energy_of_integrableOn` rewrites with this identity
to establish `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x,
(greenSlope x j t)^2+(greenSolution x j t)^2`.

Article: 2610.05164v2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenSolution_leftDensity (x : ℝ) (j : ℝ → ℝ) :
    greenSolution x (leftDensity j x)=greenSolution x j := by
  funext t
  simp only [greenSolution,leftDensity_idempotent]

/--
Exact identity `greenSlope x (leftDensity j x)=greenSlope x j`.

Use: `«2610.05164v2».HalfLine.greenSlope_boundary_of_integrableOn` rewrites with this identity
to establish `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Article: 2610.05164v2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenSlope_leftDensity (x : ℝ) (j : ℝ → ℝ) : greenSlope x (leftDensity j x)=greenSlope x j := by
  funext t
  simp only [greenSlope,leftDensity_idempotent]

/--
Integrability of the displayed function: `Integrable (leftDensity j x)`.

Use: `«2610.05164v2».HalfLine.greenSlope_boundary_of_integrableOn` rewrites with this
integrability result to establish `greenSlope x j x= -(∫ t in Iio x,
exp (t-x)*j t)`.

Article: 2610.05164v2, Theorem 6.1.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem leftDensity_integrable_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) : Integrable (leftDensity j x) :=
  (integrable_indicator_iff measurableSet_Iio).mpr hj

/--
C.1 uses L1 data on the half-line; no integrability of the arbitrary extension to its right is
required.

Exact identity `greenSolution x j t=∫ y in Iio x, green x t y*j y`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.greenSolution_leftDensity`,
`«2610.05164v2».HalfLine.greenSolution_integral`,
`«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn` with the arguments shown in
the proof.
-/
theorem greenSolution_integral_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) (t : ℝ) :
    greenSolution x j t=∫ y in Iio x, green x t y*j y := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.greenSolution_leftDensity`,
  -- `«2610.05164v2».HalfLine.greenSolution_integral`,
  -- `«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn` with the arguments shown
  -- in the proof.
  rw [← greenSolution_leftDensity x j,greenSolution_integral (leftDensity_integrable_of_integrableOn hj)]
  apply setIntegral_congr_fun measurableSet_Iio
  intro y hy
  change green x t y*leftDensity j x y=green x t y*j y
  rw [leftDensity,indicator_of_mem hy]

/--
Smoothness to the stated order: `ContDiff ℝ 1 (greenSolution x j) ∧ (∀ a b,
AbsolutelyContinuousOnInterval (greenSlope x j) a b)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates
`«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn`,
`«2610.05164v2».HalfLine.greenSolution_leftDensity`, `«2610.05164v2».HalfLine.greenSolution_c1`
with the arguments shown in the proof.
-/
theorem greenSolution_regular_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) : ContDiff ℝ 1 (greenSolution x j) ∧
      (∀ a b, AbsolutelyContinuousOnInterval (greenSlope x j) a b) := by
  have h := leftDensity_integrable_of_integrableOn hj
  constructor
  · simpa only [greenSolution_leftDensity] using greenSolution_c1 h x
  · intro a b
    simpa only [greenSlope_leftDensity] using greenSlope_locallyAC h x a b

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ t ∂volume.restrict (Iio x),
HasDerivAt (greenSlope x j) (greenSolution x j t-j t) t`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenSolution_ode_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) : ∀ᵐ t ∂volume.restrict (Iio x),
      HasDerivAt (greenSlope x j) (greenSolution x j t-j t) t := by
  have h := greenSolution_second_derivative (leftDensity_integrable_of_integrableOn hj) x
  rw [greenSlope_leftDensity,greenSolution_leftDensity,leftDensity_idempotent] at h
  filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_Iio] with t ht htx
  simpa only [leftDensity,indicator_of_mem htx] using ht

/--
The precise assertion is `Filter.Tendsto (greenSlope x j) Filter.atBot (𝓝 0)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.greenSlope_leftDensity`,
`«2610.05164v2».HalfLine.greenSlope_left_limit`,
`«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn` with the arguments shown in
the proof.
-/
theorem greenSlope_left_limit_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) : Filter.Tendsto (greenSlope x j) Filter.atBot (𝓝 0) := by
  simpa only [greenSlope_leftDensity] using
    greenSlope_left_limit (leftDensity_integrable_of_integrableOn hj) x

/--
The precise assertion is `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.greenSlope_leftDensity`,
`«2610.05164v2».HalfLine.greenSlope_boundary`,
`«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn` with the arguments shown in
the proof.
-/
theorem greenSlope_boundary_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) : greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t) := by
  rw [← greenSlope_leftDensity x j,greenSlope_boundary (leftDensity_integrable_of_integrableOn hj)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iio
  intro t ht
  change exp (t-x)*leftDensity j x t=exp (t-x)*j t
  rw [leftDensity,indicator_of_mem ht]

/--
The precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x, (greenSlope x
j t)^2+(greenSolution x j t)^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.greenSolution_energy`,
`«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn`,
`«2610.05164v2».HalfLine.greenSlope_leftDensity` with the arguments shown in the proof.
-/
theorem greenSolution_energy_of_integrableOn {j : ℝ → ℝ} {x : ℝ}
    (hj : IntegrableOn j (Iio x)) :
    (∫ t in Iio x, j t*greenSolution x j t)=
      ∫ t in Iio x, (greenSlope x j t)^2+(greenSolution x j t)^2 := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.greenSolution_energy`,
  -- `«2610.05164v2».HalfLine.leftDensity_integrable_of_integrableOn`,
  -- `«2610.05164v2».HalfLine.greenSlope_leftDensity` with the arguments shown in the proof.
  have h := greenSolution_energy (leftDensity_integrable_of_integrableOn hj) x
  rw [greenSolution_leftDensity,greenSlope_leftDensity] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Iio
  intro t ht
  change j t*greenSolution x j t=leftDensity j x t*greenSolution x j t
  rw [leftDensity,indicator_of_mem ht]

end
end «2610.05164v2».HalfLine
