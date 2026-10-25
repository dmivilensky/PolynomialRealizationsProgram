import chebyshev2.Primal.Family
import chebyshev2.Filters.Relaxation

/-!
Article: chebyshev2, Theorem 5.1.
Density.
Use: `chebyshev2.Primal.density_continuous` feeds
`chebyshev2.Primal.reflectedLinearFilter_ode` (reflected Linear Filter ode).
Proof chain: `chebyshev2.Primal.determinant_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.Primal
noncomputable section
open Set MeasureTheory chebyshev2.PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `speed φ 0=0`.

Use: `chebyshev2.Primal.density_formula` rewrites with this identity to establish the
precise assertion is `(speedData φ hφ).density κ x= (speed φ ((speedData φ hφ).q x)+(speedData
φ hφ).Q x)/κ`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem speed_zero (φ : ℝ → ℝ) : speed φ 0=0 := by
  simp [speed,coordinate]
/--
Exact identity `speed φ 2=0`.

Use: `chebyshev2.Primal.density_formula` rewrites with this identity to establish the
precise assertion is `(speedData φ hφ).density κ x= (speed φ ((speedData φ hφ).q x)+(speedData
φ hφ).Q x)/κ`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem speed_two (φ : ℝ → ℝ) : speed φ 2=0 := by simp [speed,coordinate]

/--
The precise assertion is `(speedData φ hφ).density κ x= (speed φ ((speedData φ hφ).q
x)+(speedData φ hφ).Q x)/κ`.

Use: `chebyshev2.Primal.density_bound_pointwise` rewrites with this identity to establish
the stated quantitative bound `(speedData φ hφ).density κ x≤((speedData φ hφ).B+1)/κ`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Separate `x∈Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem density_formula {φ : ℝ → ℝ} (hφ : Continuous φ) (κ x : ℝ) :
    (speedData φ hφ).density κ x=
      (speed φ ((speedData φ hφ).q x)+(speedData φ hφ).Q x)/κ := by
  -- Separate `x∈Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  let S := speedData φ hφ
  by_cases hx : x∈Ioo (S.X 0) (S.X 2)
  · rw [SpeedData.density,indicator_of_mem hx]
    rfl
  · rw [S.density_zero_outside κ hx,S.Q_zero_outside hx]
    rcases le_or_gt x (S.X 0) with h|h
    · rw [S.q_zero_left h,speed_zero]
      simp
    · have hr : S.X 2≤x := not_lt.mp (fun hr => hx ⟨h,hr⟩)
      rw [S.q_two_right hr,speed_two]
      simp

/--
Continuity of the displayed function: `Continuous ((speedData φ hφ).density κ)`.

Use: `chebyshev2.Primal.determinant_cubic` rewrites with this continuity result to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem density_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ) :
    Continuous ((speedData φ hφ).density κ) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (speedData φ hφ).density κ=fun x =>
      (speed φ ((speedData φ hφ).q x)+(speedData φ hφ).Q x)/κ := by
    funext x
    exact density_formula hφ κ x
  rw [he]
  exact (((speed_continuous hφ).comp (speedData φ hφ).q_continuous).add
    (speedData φ hφ).Q_continuous).div_const κ

/--
The stated quantitative bound `speed φ q≤(speedData φ hφ).B`.

Use: `chebyshev2.Primal.density_bound_pointwise` uses this bound to establish the stated
quantitative bound `(speedData φ hφ).density κ x≤((speedData φ hφ).B+1)/κ`.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.Primal.speed_continuous` with the arguments
shown in the proof.
-/
theorem speedData_bound {φ : ℝ → ℝ} (hφ : Continuous φ) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 2) : speed φ q≤(speedData φ hφ).B :=
  (Classical.choose_spec (isCompact_Icc.bddAbove_image
    (speed_continuous hφ).continuousOn) (mem_image_of_mem _ hq)).trans (le_max_left _ _)

/--
The stated quantitative bound `(speedData φ hφ).density κ x≤((speedData φ hφ).B+1)/κ`.

Use: `chebyshev2.Primal.compactDensity` uses this bound in the displayed construction of
`compactDensity`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.Primal.density_formula`,
`chebyshev2.Primal.speedData_bound`, `chebyshev2.PrescribedSpeed.SpeedData.q_mem` with
the arguments shown in the proof.
-/
theorem density_bound_pointwise {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    (x : ℝ) : (speedData φ hφ).density κ x≤((speedData φ hφ).B+1)/κ := by
  rw [density_formula hφ κ x]
  exact div_le_div_of_nonneg_right (add_le_add (speedData_bound hφ ((speedData φ hφ).q_mem x))
    ((speedData φ hφ).Q_le_one x)) hκ.le

/--
Constructs `compactDensity` of type `chebyshev2.Filters.CompactDensity` by the displayed
record fields. Data fields specify the construction; proof fields discharge its required
properties.

Use: `chebyshev2.Primal.compactDensity_ground_exact` uses this definition to establish
exact identity `(compactDensity hφ hκ hM).coupling=κ`.

Article: chebyshev2, Theorem 5.1.
-/
def compactDensity {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    (hM : (∫ x,(speedData φ hφ).density κ x)=1) : chebyshev2.Filters.CompactDensity where
  value := (speedData φ hφ).density κ
  integrable := (speedData φ hφ).density_integrable hκ
  nonneg := (speedData φ hφ).density_nonneg hκ
  bounded := ⟨_,density_bound_pointwise hφ hκ⟩
  compactSupport := (speedData φ hφ).density_compact_support κ
  mass_one := hM

/--
Exact identity `(compactDensity hφ hκ hM).coupling=κ`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.Primal.ground_exact` with the arguments
shown in the proof.
-/
theorem compactDensity_ground_exact {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    (hM : (∫ x,(speedData φ hφ).density κ x)=1) :
    (compactDensity hφ hκ hM).coupling=κ := ground_exact hφ hκ

end
end chebyshev2.Primal
