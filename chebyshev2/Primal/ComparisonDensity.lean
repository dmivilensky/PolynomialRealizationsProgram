import chebyshev2.Primal.ComparisonProfile
import chebyshev2.Comparison.ProfileGeometry
import chebyshev2.PrescribedSpeed.Congruence

/-!
Article: chebyshev2, Theorem 3.4.
The Definition 10 instance yields exactly the already defined primal density.
Use: `chebyshev2.Primal.comparison_density` feeds
`chebyshev2.Primal.determinant_profile_difference` (determinant profile difference).
-/
namespace chebyshev2.Primal
noncomputable section
open Set chebyshev2.PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(comparisonProfile hφ hκ).speed q=speed φ q`.

Use: `chebyshev2.Primal.comparison_X` uses this identity to establish the identity
`((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.speed_eq`,
`chebyshev2.Primal.amplitude_square` with the arguments shown in the proof.
-/
theorem comparison_speed {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 2) :
    (comparisonProfile hφ hκ).speed q=speed φ q := by
  rw [chebyshev2.Comparison.Profile.speed_eq _ hq]
  exact amplitude_square φ hκ hq

/--
Exact identity `((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X`.

Use: `chebyshev2.Primal.comparisonA0_eq` rewrites with this identity to establish exact
identity `(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_congr`,
`chebyshev2.Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_X {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    ((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X :=
  SpeedData.X_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩)

/--
Exact identity `((comparisonProfile hφ hκ).speedData hκ).q=(speedData φ hφ).q`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.4.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_congr`,
`chebyshev2.Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_q {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    ((comparisonProfile hφ hκ).speedData hκ).q=(speedData φ hφ).q :=
  SpeedData.q_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩)

/--
Exact identity `(comparisonProfile hφ hκ).density hκ=(speedData φ hφ).density κ`.

Use: `chebyshev2.Primal.comparisonA0_eq` rewrites with this identity to establish exact
identity `(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.density_congr`,
`chebyshev2.Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_density {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    (comparisonProfile hφ hκ).density hκ=(speedData φ hφ).density κ :=
  SpeedData.density_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩) κ

end
end chebyshev2.Primal
