import chebyshev2.Sobolev.Operators
import chebyshev2.GroundState.SpectralTop
import chebyshev2.Continuum.SpectralIdentification

/-!
Article: chebyshev2, Theorem 3.1.
Theorem 3.1's variational characterization, for arbitrary integrable nonnegative nonzero density.
Use: `chebyshev2.GroundState.groundParameter_variational` feeds
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` (Theorem 5.1's prescribed
parameter is the actual spectral/variational ground parameter, rather than just a parameter of a
differential equation).
Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle. The
needed form is proved here.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Defines `groundParameter` of type `ℝ` by `2/kernelEigenvalue hm hn 0`.

Use: `chebyshev2.Calibration.Data.amplitude_cube_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (fun x => (C.amplitude
(groundParameter hm hn) (G.q x))^3)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.
-/
def groundParameter {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) : ℝ :=
  2/kernelEigenvalue hm hn 0

/--
Exact identity `0 < kernelEigenvalue hm hn 0 ∧ ∃ u : H1, ‖u‖=1 ∧ densityOperator m
u=kernelEigenvalue hm hn 0 • u`.

Use: `chebyshev2.GroundState.groundParameter_attained` uses this identity to establish
constructs witnesses with the exact properties `∃ u : H1, ‖u‖=1 ∧ (∫ x, m x*H1.rep u
x^2)=kernelEigenvalue hm hn 0/2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Use the identities/estimates `chebyshev2.Continuum.densityOperator_trace`,
`chebyshev2.Continuum.PositiveSpectralData.diagonal_eq`,
`chebyshev2.Continuum.PositiveSpectralData.top_attained` with the arguments shown in the
proof.
-/
theorem top_density_attained {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) :
    0 < kernelEigenvalue hm hn 0 ∧ ∃ u : H1,
      ‖u‖=1 ∧ densityOperator m u=kernelEigenvalue hm hn 0 • u := by
  -- Use the identities/estimates `chebyshev2.Continuum.densityOperator_trace`,
  -- `chebyshev2.Continuum.PositiveSpectralData.diagonal_eq`,
  -- `chebyshev2.Continuum.PositiveSpectralData.top_attained` with the arguments shown in
  -- the proof.
  let D := densitySpectralData hm hn
  have htrace : (∑' i, D.eig i)=∫ x, m x := by
    have h := densityOperator_trace D.basis hm
    simpa only [PositiveSpectralData.diagonal_eq] using h
  have h := D.top_attained (htrace ▸ hM)
  simpa only [density_kernel_eigenvalue_eq hm hn D] using h

/--
The stated quantitative bound `0 < groundParameter hm hn`.

Use: `chebyshev2.Filters.CompactDensity.coupling_positive` uses this bound to establish the
stated quantitative bound `0 < m.coupling`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Use the identities/estimates `chebyshev2.GroundState.top_density_attained` with the
arguments shown in the proof.
-/
theorem groundParameter_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : 0 < groundParameter hm hn :=
  div_pos (by norm_num) (top_density_attained hm hn hM).1

/--
Integrability of the displayed function: `Integrable (fun x => m x*H1.rep u x^2)`.

Use: `chebyshev2.GroundState.RiccatiData.squareDerivative_integrable` uses this
integrability result to establish integrability of the displayed function: `Integrable
(R.squareDerivative f)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.continuous_rep`,
`chebyshev2.Sobolev.H1.evaluation_bound` with the arguments shown in the proof.
-/
theorem weighted_square_integrable {m : ℝ → ℝ} (hm : Integrable m) (u : H1) :
    Integrable (fun x => m x*H1.rep u x^2) := by
  -- Use the identities/estimates `chebyshev2.Sobolev.H1.continuous_rep`,
  -- `chebyshev2.Sobolev.H1.evaluation_bound` with the arguments shown in the proof.
  apply (hm.norm.mul_const ((‖u‖/sqrt 2)^2)).mono'
  · exact hm.aestronglyMeasurable.mul ((H1.continuous_rep u).pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [norm_mul, Real.norm_eq_abs, abs_pow, sq_abs]
      have hb := (sq_le_sq₀ (abs_nonneg (H1.rep u x)) (by positivity)).mpr (H1.evaluation_bound u x)
      rw [sq_abs] at hb
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _))

/--
The stated quantitative bound `groundParameter hm hn*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2`.

Use: `chebyshev2.GroundState.groundParameter_variational` uses this bound to establish
equivalence of the displayed criteria: `(∀ u : H1, c*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2) ↔ c ≤
groundParameter hm hn`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem groundParameter_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) (u : H1) :
    groundParameter hm hn*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let D := densitySpectralData hm hn
  have ht := D.top_quadratic_bound u
  rw [density_kernel_eigenvalue_eq hm hn D, sobolevDensityOperator_quadratic hm] at ht
  have hp := (top_density_attained hm hn hM).1
  apply (mul_le_mul_iff_left₀ hp).mp
  change groundParameter hm hn*(∫ x, m x*H1.rep u x^2)*kernelEigenvalue hm hn 0 ≤
    ‖u‖^2*kernelEigenvalue hm hn 0
  have he : groundParameter hm hn*(∫ x, m x*H1.rep u x^2)*kernelEigenvalue hm hn 0 =
      2*(∫ x, m x*H1.rep u x^2) := by
    dsimp [groundParameter]
    field_simp
  rw [he]
  simpa only [mul_comm] using ht

/--
Constructs witnesses with the exact properties `∃ u : H1, ‖u‖=1 ∧ (∫ x, m x*H1.rep u
x^2)=kernelEigenvalue hm hn 0/2`.

Use: `chebyshev2.GroundState.groundParameter_variational` uses this identity to establish
equivalence of the displayed criteria: `(∀ u : H1, c*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2) ↔ c ≤
groundParameter hm hn`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Use the identities/estimates `chebyshev2.GroundState.top_density_attained`,
`chebyshev2.Sobolev.sobolevDensityOperator_quadratic` with the arguments shown in the
proof.
-/
theorem groundParameter_attained {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ u : H1, ‖u‖=1 ∧
      (∫ x, m x*H1.rep u x^2)=kernelEigenvalue hm hn 0/2 := by
  -- Use the identities/estimates `chebyshev2.GroundState.top_density_attained`,
  -- `chebyshev2.Sobolev.sobolevDensityOperator_quadratic` with the arguments shown in the
  -- proof.
  obtain ⟨_,u,hu,he⟩ := top_density_attained hm hn hM
  refine ⟨u,hu,?_⟩
  have ht := congrArg (fun v => inner ℝ u v) he
  rw [sobolevDensityOperator_quadratic hm, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu] at ht
  simp only [one_pow, mul_one] at ht
  linarith

/--
Theorem 3.1's variational characterization, for arbitrary integrable nonnegative nonzero
density. All test functions are actual H1 representatives.

Equivalence of the displayed criteria: `(∀ u : H1, c*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2) ↔ c ≤
groundParameter hm hn`.

Use: `chebyshev2.Comparison.groundParameter_reflection` uses this bound to establish exact
identity `groundParameter (reflected_integrable hm) (reflected_nonneg hn)=groundParameter hm
hn`.

Article: chebyshev2, Theorem 3.1.

Source: Simon, Trace Ideals and Their Applications — Birman–Schwinger variational principle.

Proof: Use the identities/estimates `chebyshev2.GroundState.groundParameter_attained`,
`chebyshev2.GroundState.top_density_attained`,
`chebyshev2.GroundState.groundParameter_bound` with the arguments shown in the proof.
-/
theorem groundParameter_variational {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) (c : ℝ) :
    (∀ u : H1, c*(∫ x, m x*H1.rep u x^2) ≤ ‖u‖^2) ↔ c ≤ groundParameter hm hn := by
  -- Use the identities/estimates `chebyshev2.GroundState.groundParameter_attained`,
  -- `chebyshev2.GroundState.top_density_attained`,
  -- `chebyshev2.GroundState.groundParameter_bound` with the arguments shown in the proof.
  constructor
  · intro h
    obtain ⟨u,hu,hi⟩ := groundParameter_attained hm hn hM
    have hb := h u
    rw [hu,hi] at hb
    have hp := (top_density_attained hm hn hM).1
    dsimp [groundParameter]
    apply (le_div_iff₀ hp).mpr
    norm_num at hb
    linarith
  · intro hc u
    apply (mul_le_mul_of_nonneg_right hc ?_).trans (groundParameter_bound hm hn hM u)
    exact integral_nonneg (fun x => mul_nonneg (hn x) (sq_nonneg _))

end
end chebyshev2.GroundState
