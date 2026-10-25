import chebyshev2.Primal.ComparisonDensity
import chebyshev2.Primal.FilterBounds
import chebyshev2.Comparison.ProfileComparison
import chebyshev2.Comparison.ProfileCalibration

/-!
Article: chebyshev2, Proposition 13.
Exact finite comparison identities for two actual primal profiles.
Use: `chebyshev2.Primal.trace_profile_difference` feeds
`chebyshev2.Primal.trace_profile_difference_cubic` (trace profile difference cubic).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters chebyshev2.Continuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `actualRightFilter` of type `ℝ` by `nonlinear s (reflected ((speedData φ hφ).density
κ)) (-((speedData φ hφ).X q))`.

Use: `chebyshev2.Primal.actualComparisonA` uses this definition in the displayed
construction of `actualComparisonA`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def actualRightFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s q : ℝ) : ℝ :=
  nonlinear s (reflected ((speedData φ hφ).density κ)) (-((speedData φ hφ).X q))
/--
Defines `actualRightLinear` of type `ℝ` by `κ*causal 2 (reflected ((speedData φ hφ).density κ))
(-((speedData φ hφ).X q))`.

Use: `chebyshev2.Primal.actualComparisonA0` uses this definition in the displayed
construction of `actualComparisonA0`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def actualRightLinear {φ : ℝ → ℝ} (hφ : Continuous φ) (κ q : ℝ) : ℝ :=
  κ*causal 2 (reflected ((speedData φ hφ).density κ)) (-((speedData φ hφ).X q))
/--
Defines `actualComparisonA` of type `ℝ` by `if q∈Ioo (0:ℝ) 2 then
chebyshev2.Comparison.determinantCoefficient κ s q (speed φ q) r (actualRightFilter hφ κ s
q) else 0`.

Use: `chebyshev2.Primal.comparisonA_eq` uses this definition to establish the identity
`(comparisonProfile hφ hκ).comparisonA hκ=actualComparisonA hφ κ`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def actualComparisonA {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s q r : ℝ) : ℝ :=
  if q∈Ioo (0:ℝ) 2 then
    chebyshev2.Comparison.determinantCoefficient κ s q (speed φ q) r (actualRightFilter hφ κ s q) else 0
/--
Defines `actualComparisonA0` of type `ℝ` by `if q∈Ioo (0:ℝ) 2 then
chebyshev2.Comparison.traceCoefficient κ q (speed φ q) r (actualRightLinear hφ κ q) else
0`.

Use: `chebyshev2.Primal.comparisonA0_eq` uses this definition to establish the identity
`(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def actualComparisonA0 {φ : ℝ → ℝ} (hφ : Continuous φ) (κ q r : ℝ) : ℝ :=
  if q∈Ioo (0:ℝ) 2 then
    chebyshev2.Comparison.traceCoefficient κ q (speed φ q) r (actualRightLinear hφ κ q) else 0

/--
Exact identity `(comparisonProfile hφ hκ).comparisonA hκ=actualComparisonA hφ κ`.

Use: `chebyshev2.Primal.determinant_profile_difference` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonA_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    (comparisonProfile hφ hκ).comparisonA hκ=actualComparisonA hφ κ := by
  funext s q r
  unfold chebyshev2.Comparison.Profile.comparisonA actualComparisonA
  split_ifs with hq
  · rw [comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩]
    simp only [chebyshev2.Comparison.Profile.rightFilter,actualRightFilter,comparison_density,comparison_X]
  · rfl

/--
Exact identity `(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Use: `chebyshev2.Primal.trace_profile_difference` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonA0_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    (comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ := by
  funext q r
  unfold chebyshev2.Comparison.Profile.comparisonA0 actualComparisonA0
  split_ifs with hq
  · rw [comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩]
    simp only [chebyshev2.Comparison.Profile.rightLinear,actualRightLinear,comparison_density,comparison_X]
  · rfl

/--
The precise assertion is `logDeterminant (kernelEigenvalue ((speedData φ hφ).density_integrable
hκ) ((speedData φ hφ).density_nonneg hκ)) s- logDeterminant (kernelEigenvalue ((speedData ψ
hψ).density_integrable hκ) ((speedData ψ hψ).density_nonneg hκ)) s= ∫ x,actualComparisonA hψ κ
s ((speedData φ hφ).q x) (nonlinear s ((speedData φ hφ).density κ) x)* ((speedData φ
hφ).density κ x-(amplitude ψ κ ((speedData φ hφ).q x))^2)`.

Use: `chebyshev2.Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem determinant_profile_difference {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) :
    logDeterminant (kernelEigenvalue ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ)) s-
    logDeterminant (kernelEigenvalue ((speedData ψ hψ).density_integrable hκ)
      ((speedData ψ hψ).density_nonneg hκ)) s=
    ∫ x,actualComparisonA hψ κ s ((speedData φ hφ).q x)
      (nonlinear s ((speedData φ hφ).density κ) x)*
      ((speedData φ hφ).density κ x-(amplitude ψ κ ((speedData φ hφ).q x))^2) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in
  -- the proof.
  let G := groundWitness hφ hκ
  have h := chebyshev2.Comparison.Profile.signed_determinant_comparison G
    (comparisonProfile hψ G.coupling_positive) hs
  have hv := kernelEigenvalue_congr
    (hm:=((comparisonProfile hψ G.coupling_positive).speedData G.coupling_positive).density_integrable G.coupling_positive)
    (hn:=((comparisonProfile hψ G.coupling_positive).speedData G.coupling_positive).density_nonneg G.coupling_positive)
    (hm':=(speedData ψ hψ).density_integrable G.coupling_positive)
    (hn':=(speedData ψ hψ).density_nonneg G.coupling_positive)
    (comparison_density hψ G.coupling_positive)
  rw [hv,(speedData φ hφ).ground_coordinate hκ G,comparisonA_eq] at h
  have hk := (speedData φ hφ).groundParameter_density hκ
  have hw : kernelEigenvalue ((speedData ψ hψ).density_integrable G.coupling_positive)
      ((speedData ψ hψ).density_nonneg G.coupling_positive)=
      kernelEigenvalue ((speedData ψ hψ).density_integrable hκ)
        ((speedData ψ hψ).density_nonneg hκ) := by
    apply kernelEigenvalue_congr
    simp only [hk]
  rw [hw] at h
  simpa only [hk,comparisonProfile] using h

/--
The precise assertion is `(∫ x,(κ*causal 2 ((speedData φ hφ).density κ) x)^2)- (∫ x,(κ*causal 2
((speedData ψ hψ).density κ) x)^2)= ∫ x,actualComparisonA0 hψ κ ((speedData φ hφ).q x)
(κ*causal 2 ((speedData φ hφ).density κ) x)* ((speedData φ hφ).density κ x-(amplitude ψ κ
((speedData φ hφ).q x))^2)`.

Use: `chebyshev2.Primal.trace_profile_difference_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem trace_profile_difference {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    {κ : ℝ} (hκ : 0<κ) :
    (∫ x,(κ*causal 2 ((speedData φ hφ).density κ) x)^2)-
    (∫ x,(κ*causal 2 ((speedData ψ hψ).density κ) x)^2)=
    ∫ x,actualComparisonA0 hψ κ ((speedData φ hφ).q x)
      (κ*causal 2 ((speedData φ hφ).density κ) x)*
      ((speedData φ hφ).density κ x-(amplitude ψ κ ((speedData φ hφ).q x))^2) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in
  -- the proof.
  let G := groundWitness hφ hκ
  have h := chebyshev2.Comparison.Profile.signed_trace_comparison G
    (comparisonProfile hψ G.coupling_positive)
  have hv := chebyshev2.Filters.linear_congr
    (hm:=((comparisonProfile hψ G.coupling_positive).speedData G.coupling_positive).density_integrable G.coupling_positive)
    (hn:=((comparisonProfile hψ G.coupling_positive).speedData G.coupling_positive).density_nonneg G.coupling_positive)
    (hm':=(speedData ψ hψ).density_integrable G.coupling_positive)
    (hn':=(speedData ψ hψ).density_nonneg G.coupling_positive)
    (comparison_density hψ G.coupling_positive)
  rw [hv,(speedData φ hφ).ground_coordinate hκ G,comparisonA0_eq] at h
  simp only [chebyshev2.Filters.linear] at h
  have hk := (speedData φ hφ).groundParameter_density hκ
  have hk' := (speedData ψ hψ).groundParameter_density G.coupling_positive
  simp only [hk'] at h
  simpa only [hk,comparisonProfile] using h

end
end chebyshev2.Primal
