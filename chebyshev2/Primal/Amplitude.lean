import chebyshev2.Primal.Moments
import chebyshev2.Comparison.Profile

/-!
Article: chebyshev2, Theorem 3.4.
The regular endpoint factor of every primal comparison amplitude.
Use: `chebyshev2.Primal.amplitude_square` feeds
`chebyshev2.Primal.determinant_difference_core_identity` (determinant difference core identity).
Proof chain: `chebyshev2.Primal.comparison_density` — chebyshev2, Theorem 3.4; Signed
determinant and square-trace comparisons.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory chebyshev2.Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(coordinate q)^3=min q (2-q)`.

Use: `chebyshev2.Primal.Q_coordinate` rewrites with this identity to establish exact
identity `Q q=(coordinate q)^3*(2-(coordinate q)^3)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinate_cube {q : ℝ} (hq : q∈Icc (0:ℝ) 2) :
    (coordinate q)^3=min q (2-q) := by
  have hn : 0≤min q (2-q) := le_min hq.1 (by linarith [hq.2])
  simpa only [coordinate,one_div,show ((3:ℕ):ℝ)=(3:ℝ) from rfl] using
    rpow_inv_natCast_pow hn (by norm_num : (3:ℕ)≠0)

/--
Membership in the specified domain/enclosure: `coordinate q∈Icc (0:ℝ) 1`.

Use: `chebyshev2.Primal.amplitude_square` uses this assertion to establish the identity
`κ*(amplitude φ κ q)^2-Q q=speed φ q`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.coordinate_nonneg`,
`chebyshev2.Primal.coordinate_cube` with the arguments shown in the proof.
-/
theorem coordinate_mem {q : ℝ} (hq : q∈Icc (0:ℝ) 2) : coordinate q∈Icc (0:ℝ) 1 := by
  -- Use the identities/estimates `chebyshev2.Primal.coordinate_nonneg`,
  -- `chebyshev2.Primal.coordinate_cube` with the arguments shown in the proof.
  have hn := coordinate_nonneg hq
  have hc := coordinate_cube hq
  have hm : min q (2-q)≤1 := by
    rcases le_total q 1 with h|h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  refine ⟨hn,?_⟩
  nlinarith [sq_nonneg (coordinate q-1),mul_nonneg hn (sq_nonneg (coordinate q-1))]

/--
Exact identity `Q q=(coordinate q)^3*(2-(coordinate q)^3)`.

Use: `chebyshev2.Primal.amplitude_square` rewrites with this identity to establish exact
identity `κ*(amplitude φ κ q)^2-Q q=speed φ q`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.coordinate_cube` with the arguments
shown in the proof.
-/
theorem Q_coordinate {q : ℝ} (hq : q∈Icc (0:ℝ) 2) :
    Q q=(coordinate q)^3*(2-(coordinate q)^3) := by
  -- Use the identities/estimates `chebyshev2.Primal.coordinate_cube` with the arguments
  -- shown in the proof.
  rw [coordinate_cube hq]
  rcases le_total q (2-q) with h|h
  · rw [min_eq_left h]
    rfl
  · rw [min_eq_right h]
    unfold Q
    ring

/--
Continuity of the displayed function: `Continuous (normalizedAmplitude φ κ)`.

Use: `chebyshev2.Primal.amplitude_continuous` uses this continuity result to establish
continuity of the displayed function: `Continuous (amplitude φ κ)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedAmplitude_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ) :
    Continuous (normalizedAmplitude φ κ) := by
  unfold normalizedAmplitude
  fun_prop

/--
The stated quantitative bound `0<normalizedAmplitude φ κ t`.

Use: `chebyshev2.Primal.amplitude_ratio` uses this bound to establish the identity
`(amplitude φ κ q)^2/(κ*(amplitude φ κ q)^2-Q q)+ Q q/((κ*(amplitude φ κ q)^2-Q q)*amplitude φ
κ q)+ (amplitude φ κ q)^3/Q q=regularRatio φ κ (coordinate q)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem normalizedAmplitude_positive (φ : ℝ → ℝ) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) : 0<normalizedAmplitude φ κ t := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  apply sqrt_pos.mpr
  apply div_pos _ hκ
  exact add_pos_of_pos_of_nonneg (exp_pos _) (mul_nonneg ht.1 (by linarith))

/--
Defines `amplitude` of type `ℝ` by `coordinate q*normalizedAmplitude φ κ (coordinate q)`.

Use: `chebyshev2.Primal.amplitude_square` rewrites with this definition to establish exact
identity `κ*(amplitude φ κ q)^2-Q q=speed φ q`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def amplitude (φ : ℝ → ℝ) (κ q : ℝ) : ℝ :=
  coordinate q*normalizedAmplitude φ κ (coordinate q)

/--
Continuity of the displayed function: `Continuous (amplitude φ κ)`.

Use: `chebyshev2.Primal.comparisonProfile` uses this continuity result in the displayed
construction of `comparisonProfile`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.coordinate_continuous`,
`chebyshev2.Primal.normalizedAmplitude_continuous` with the arguments shown in the proof.
-/
theorem amplitude_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ) :
    Continuous (amplitude φ κ) :=
  coordinate_continuous.mul ((normalizedAmplitude_continuous hφ κ).comp coordinate_continuous)

/--
Exact identity `κ*(amplitude φ κ q)^2-Q q=speed φ q`.

Use: `chebyshev2.Primal.amplitude_ratio` rewrites with this identity to establish exact
identity `(amplitude φ κ q)^2/(κ*(amplitude φ κ q)^2-Q q)+ Q q/((κ*(amplitude φ κ q)^2-Q
q)*amplitude φ κ q)+ (amplitude φ κ q)^3/Q q=regularRatio φ κ (coordinate q)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem amplitude_square (φ : ℝ → ℝ) {κ q : ℝ} (hκ : 0<κ)
    (hq : q∈Icc (0:ℝ) 2) : κ*(amplitude φ κ q)^2-Q q=speed φ q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht := coordinate_mem hq
  have ht3 : (coordinate q)^3≤1 := pow_le_one₀ ht.1 ht.2
  have hpos : 0≤(exp (φ (coordinate q))+coordinate q*(2-(coordinate q)^3))/κ :=
    div_nonneg (add_nonneg (exp_pos _).le (mul_nonneg ht.1 (by linarith))) hκ.le
  rw [amplitude,mul_pow,normalizedAmplitude,sq_sqrt hpos,Q_coordinate hq]
  unfold speed
  field_simp
  ring

end
end chebyshev2.Primal
