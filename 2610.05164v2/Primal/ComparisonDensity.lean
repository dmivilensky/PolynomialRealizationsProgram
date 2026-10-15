import «2610.05164v2».Primal.ComparisonProfile
import «2610.05164v2».Comparison.ProfileGeometry
import «2610.05164v2».PrescribedSpeed.Congruence

/-!
Article: 2610.05164v2, Theorem 3.4.
The Definition 10 instance yields exactly the already defined primal density.
Use: `«2610.05164v2».Primal.comparison_density` feeds
`«2610.05164v2».Primal.determinant_profile_difference` (determinant profile difference).
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set «2610.05164v2».PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(comparisonProfile hφ hκ).speed q=speed φ q`.

Use: `«2610.05164v2».Primal.comparison_X` uses this identity to establish the identity
`((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_eq`,
`«2610.05164v2».Primal.amplitude_square` with the arguments shown in the proof.
-/
theorem comparison_speed {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 2) :
    (comparisonProfile hφ hκ).speed q=speed φ q := by
  rw [«2610.05164v2».Comparison.Profile.speed_eq _ hq]
  exact amplitude_square φ hκ hq

/--
Exact identity `((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X`.

Use: `«2610.05164v2».Primal.comparisonA0_eq` rewrites with this identity to establish exact
identity `(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_congr`,
`«2610.05164v2».Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_X {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    ((comparisonProfile hφ hκ).speedData hκ).X=(speedData φ hφ).X :=
  SpeedData.X_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩)

/--
Exact identity `((comparisonProfile hφ hκ).speedData hκ).q=(speedData φ hφ).q`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_congr`,
`«2610.05164v2».Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_q {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    ((comparisonProfile hφ hκ).speedData hκ).q=(speedData φ hφ).q :=
  SpeedData.q_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩)

/--
Exact identity `(comparisonProfile hφ hκ).density hκ=(speedData φ hφ).density κ`.

Use: `«2610.05164v2».Primal.comparisonA0_eq` rewrites with this identity to establish exact
identity `(comparisonProfile hφ hκ).comparisonA0 hκ=actualComparisonA0 hφ κ`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.density_congr`,
`«2610.05164v2».Primal.comparison_speed` with the arguments shown in the proof.
-/
theorem comparison_density {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    (comparisonProfile hφ hκ).density hκ=(speedData φ hφ).density κ :=
  SpeedData.density_congr _ _ (fun _ hq => comparison_speed hφ hκ ⟨hq.1.le,hq.2.le⟩) κ

end
end «2610.05164v2».Primal
