import chebyshev2.Comparison.ProfileComparison
import chebyshev2.Comparison.Integrability
import chebyshev2.PrescribedSpeed.Congruence

/-!
Article: chebyshev2, Proposition 8.
Theorem 3.4 is an instance of Lemma 12.
Use: `chebyshev2.Calibration.Data.comparisonProfile_A0` feeds
`chebyshev2.Calibration.Data.signed_trace_comparison` (signed trace comparison).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Continuum
open MeasureTheory

/--
Exact identity `kernelEigenvalue hm hn=kernelEigenvalue hm' hn'`.

Use: `chebyshev2.Calibration.Data.signed_determinant_comparison` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem kernelEigenvalue_congr {m n : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
    {hm' : Integrable n} {hn' : ∀ x, 0 ≤ n x} (h : m=n) :
    kernelEigenvalue hm hn=kernelEigenvalue hm' hn' := by subst n; rfl
end chebyshev2.Continuum

namespace chebyshev2.Filters
open MeasureTheory

/--
Exact identity `linear hm hn=linear hm' hn'`.

Use: `chebyshev2.Calibration.Data.signed_trace_comparison` uses this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem linear_congr {m n : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
    {hm' : Integrable n} {hn' : ∀ x, 0 ≤ n x} (h : m=n) :
    linear hm hn=linear hm' hn' := by subst n; rfl
end chebyshev2.Filters

namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Real chebyshev2.Comparison chebyshev2.PrescribedSpeed
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Pointwise equality on the specified domain: `EqOn ((C.comparisonProfile hκ).speedData hκ).D
(C.comparisonSpeed hκ).D (Ioo (0:ℝ) 2)`.

Use: `chebyshev2.Calibration.Data.comparisonProfile_A` uses this pointwise identity to
establish exact identity `(C.comparisonProfile hκ).comparisonA hκ=C.comparisonA hκ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.speed_eq` with the
arguments shown in the proof.
-/
theorem comparisonProfile_speed : EqOn ((C.comparisonProfile hκ).speedData hκ).D
    (C.comparisonSpeed hκ).D (Ioo (0:ℝ) 2) := by
  intro q hq
  change (C.comparisonProfile hκ).speed q=C.speed κ q
  rw [(C.comparisonProfile hκ).speed_eq ⟨hq.1.le,hq.2.le⟩]
  rfl

/--
Exact identity `((C.comparisonProfile hκ).speedData hκ).X=(C.comparisonSpeed hκ).X`.

Use: `chebyshev2.Calibration.Data.comparisonProfile_rightFilter` rewrites with this
identity to establish the identity `(C.comparisonProfile hκ).rightFilter hκ=C.rightFilter
hκ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_congr`,
`chebyshev2.Calibration.Data.comparisonProfile_speed` with the arguments shown in the
proof.
-/
theorem comparisonProfile_X : ((C.comparisonProfile hκ).speedData hκ).X=(C.comparisonSpeed hκ).X :=
  ((C.comparisonProfile hκ).speedData hκ).X_congr _ (C.comparisonProfile_speed hκ)

/--
Exact identity `(C.comparisonProfile hκ).density hκ=C.comparisonDensity hκ`.

Use: `chebyshev2.Calibration.Data.comparisonProfile_rightFilter` rewrites with this
identity to establish the identity `(C.comparisonProfile hκ).rightFilter hκ=C.rightFilter
hκ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.density_congr`,
`chebyshev2.Calibration.Data.comparisonProfile_speed` with the arguments shown in the
proof.
-/
theorem comparisonProfile_density : (C.comparisonProfile hκ).density hκ=C.comparisonDensity hκ :=
  ((C.comparisonProfile hκ).speedData hκ).density_congr _ (C.comparisonProfile_speed hκ) κ

/--
Exact identity `(C.comparisonProfile hκ).rightFilter hκ=C.rightFilter hκ`.

Use: `chebyshev2.Calibration.Data.comparisonProfile_A` rewrites with this identity to
establish exact identity `(C.comparisonProfile hκ).comparisonA hκ=C.comparisonA hκ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonProfile_rightFilter : (C.comparisonProfile hκ).rightFilter hκ=C.rightFilter hκ := by
  funext s q
  dsimp only [Profile.rightFilter,rightFilter]
  rw [C.comparisonProfile_density hκ,C.comparisonProfile_X hκ]

/--
Exact identity `(C.comparisonProfile hκ).rightLinear hκ=C.rightLinear hκ`.

Use: `chebyshev2.Calibration.Data.comparisonProfile_A0` rewrites with this identity to
establish exact identity `(C.comparisonProfile hκ).comparisonA0 hκ=C.comparisonA0 hκ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonProfile_rightLinear : (C.comparisonProfile hκ).rightLinear hκ=C.rightLinear hκ := by
  funext q
  dsimp only [Profile.rightLinear,rightLinear]
  rw [C.comparisonProfile_density hκ,C.comparisonProfile_X hκ]

/--
Exact identity `(C.comparisonProfile hκ).comparisonA hκ=C.comparisonA hκ`.

Use: `chebyshev2.Calibration.Data.signed_determinant_comparison` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem comparisonProfile_A : (C.comparisonProfile hκ).comparisonA hκ=C.comparisonA hκ := by
  funext s q r
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · rw [Profile.comparisonA,comparisonA,ite_eq_left hq,ite_eq_left hq,
      C.comparisonProfile_rightFilter hκ]
    congr 1
    exact C.comparisonProfile_speed hκ hq
  · simp only [Profile.comparisonA,comparisonA,ite_eq_right hq]

/--
Exact identity `(C.comparisonProfile hκ).comparisonA0 hκ=C.comparisonA0 hκ`.

Use: `chebyshev2.Calibration.Data.signed_trace_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem comparisonProfile_A0 : (C.comparisonProfile hκ).comparisonA0 hκ=C.comparisonA0 hκ := by
  funext q r
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · rw [Profile.comparisonA0,comparisonA0,ite_eq_left hq,ite_eq_left hq,
      C.comparisonProfile_rightLinear hκ]
    congr 1
    exact C.comparisonProfile_speed hκ hq
  · simp only [Profile.comparisonA0,comparisonA0,ite_eq_right hq]

end
end chebyshev2.Calibration.Data
