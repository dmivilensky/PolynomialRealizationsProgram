import chebyshev1.Jacobi.Kernel
import chebyshev1.Realization.GainBounds
import chebyshev1.Chebyshev.Coordinates

/-!
Article: chebyshev1, Theorem 4.2.
The supremum formula of Theorem 4.2, with exactly the article's z-coordinate domain.
Use: `chebyshev1.JacobiData.gain_eq_blocks` feeds `chebyshev2.Jacobi.gain_formula` (The
exact maximizing polynomial expression in Theorem 2.2).
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

/--
Defines `blockKernelNorm` of type `ℝ` by `Real.sqrt (∑ s ∈ Finset.range N, ((J.block (s + 1) (N
- (s + 1))).eval x * (J.leading s).eval y) ^ 2)`.

Use: `chebyshev1.JacobiData.blockGainValues` uses this definition in the displayed
construction of `blockGainValues`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 4.2 via `chebyshev1.JacobiData.kernelNorm_eq_blocks`.
-/
def blockKernelNorm (N : ℕ) (x y : ℝ) : ℝ :=
  Real.sqrt (∑ s ∈ Finset.range N,
    ((J.block (s + 1) (N - (s + 1))).eval x * (J.leading s).eval y) ^ 2)

/--
Defines `blockGainValues` of type `Set ℝ` by `{v | ∃ x ∈ Set.Icc (-1) 1, ∃ y ∈ Set.Icc (-1) 1,
v = J.blockKernelNorm N x y}`.

Use: `chebyshev1.JacobiData.gain_eq_blocks` uses this definition to establish exact
identity `(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues
N)`.

Article: chebyshev1, Theorem 4.2 via `chebyshev1.JacobiData.gain_eq_blocks`.
-/
def blockGainValues (N : ℕ) : Set ℝ :=
  {v | ∃ x ∈ Set.Icc (-1) 1, ∃ y ∈ Set.Icc (-1) 1, v = J.blockKernelNorm N x y}

/--
Exact identity `(J.realization I).kernelNorm N lam nu = (2 / (I.delta * J.den I N)) *
J.blockKernelNorm N (I.z lam) (I.z nu)`.

Use: `chebyshev1.JacobiData.gain_eq_blocks` rewrites with this identity to establish exact
identity `(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues
N)`.

Article: chebyshev1, Theorem 4.2.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem kernelNorm_eq_blocks {N : ℕ} (h : J.Admissible I N) (lam nu : ℝ) :
    (J.realization I).kernelNorm N lam nu =
      (2 / (I.delta * J.den I N)) * J.blockKernelNorm N (I.z lam) (I.z nu) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  unfold Realization.kernelNorm blockKernelNorm
  have he : (∑ s ∈ Finset.range N, ((J.realization I).kernel N s lam nu) ^ 2) =
      (2 / (I.delta * J.den I N)) ^ 2 * ∑ s ∈ Finset.range N,
        ((J.block (s + 1) (N - (s + 1))).eval (I.z lam) * (J.leading s).eval (I.z nu)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [J.kernel_eq I h s (Finset.mem_range.mp hs)]
    ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (div_pos (by norm_num) (mul_pos I.delta_pos (h N le_rfl)))]

/--
The supremum formula of Theorem 4.2, with exactly the article's z-coordinate domain.

Exact identity `(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup
(J.blockGainValues N)`.

Use: `chebyshev2.Jacobi.gain_formula` rewrites with this identity to establish exact
identity `J.gain I h = 2/(I.delta*J.data.den I N)*sSup (J.data.blockGainValues N)`.

Article: chebyshev1, Theorem 4.2.

Proof: Use the identities/estimates `chebyshev1.Realization.gain_attained`,
`chebyshev1.SpectralInterval.delta_pos`, `chebyshev1.SpectralInterval.z_mem` with the
arguments shown in the proof.
-/
theorem gain_eq_blocks {N : ℕ} (h : J.Admissible I N) :
    (J.realization I).gain I N =
      (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues N) := by
  -- Use the identities/estimates `chebyshev1.Realization.gain_attained`,
  -- `chebyshev1.SpectralInterval.delta_pos`, `chebyshev1.SpectralInterval.z_mem` with
  -- the arguments shown in the proof.
  obtain ⟨lam, hl, nu, hn, he⟩ := (J.realization I).gain_attained I N
  have hc : 0 < 2 / (I.delta * J.den I N) := div_pos (by norm_num) (mul_pos I.delta_pos (h N le_rfl))
  have hg : IsGreatest (J.blockGainValues N) (J.blockKernelNorm N (I.z lam) (I.z nu)) := by
    refine ⟨⟨I.z lam, I.z_mem hl, I.z nu, I.z_mem hn, rfl⟩, ?_⟩
    rintro v ⟨x, hx, y, hy, rfl⟩
    have hb := (J.realization I).kernelNorm_le_gain I N (I.lambda_mem hx) (I.lambda_mem hy)
    rw [← he, J.kernelNorm_eq_blocks I h, J.kernelNorm_eq_blocks I h, I.z_lambda, I.z_lambda] at hb
    exact (mul_le_mul_iff_right₀ hc).mp hb
  rw [hg.csSup_eq, abs_of_pos (h N le_rfl), ← J.kernelNorm_eq_blocks I h, he]

end
end chebyshev1.JacobiData
