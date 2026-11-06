import chebyshev1.Spectral.LinearResponseBound
import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.Real.Sqrt

/-! A factorized scalar kernel determines the matrix insertion response. Common
maxima then give the exact gain constant for time-l2 operator-norm inputs. -/
namespace chebyshev1.Realization
noncomputable section
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Scalar kernel factorization implies the actual operator factorization;
the latter is not a premise. -/
theorem linearResponse_eq_sum_of_kernel_factorization (R : Realization ι)
    (I : SpectralInterval) (N : ℕ) (c : ℕ → ℝ) (p q : ℕ → ℝ[X])
    (hfactor : ∀ s < N, ∀ lam ∈ Set.Icc I.mu I.L, ∀ nu ∈ Set.Icc I.mu I.L,
      R.kernel N s lam nu = c s*(p s).eval lam*(q s).eval nu)
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    R.linearResponse N H E = ∑ s ∈ Finset.range N,
      c s • (aeval H (p s)*E s*aeval H (q s)) := by
  let B := SpectralBasis.ofHermitian H hH
  have heig : ∀ i, B.eigenvalues i ∈ Set.Icc I.mu I.L :=
    fun i => SpectralBasis.eigenvalues_mem_interval I H hH hspec i
  apply B.coordinates_injective
  have hl := R.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose N E
  rw [B.diagonalize] at hl
  change R.linearResponse N (Matrix.diagonal B.eigenvalues)
    (fun s => B.coordinates (E s)) = B.coordinates (R.linearResponse N H E) at hl
  rw [← hl]
  have hsum : B.coordinates (∑ s ∈ Finset.range N, c s • (aeval H (p s)*E s*aeval H (q s))) =
      ∑ s ∈ Finset.range N, c s • B.coordinates (aeval H (p s)*E s*aeval H (q s)) := by
    simp [SpectralBasis.coordinates,Matrix.mul_sum,Matrix.sum_mul]
  rw [hsum]
  simp_rw [B.coordinates_mul]
  have hae (r : ℝ[X]) : B.coordinates (aeval H r) =
      Matrix.diagonal (fun i => r.eval (B.eigenvalues i)) := aeval_coordinates r H hH
  simp_rw [hae]
  ext i j
  simp only [R.diagonal_linearResponse_entry,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_mul,Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hfactor s (Finset.mem_range.mp hs) _ (heig i) _ (heig j)]
  ring

/-- Common maxima of both polynomial factors upgrade the HS gain estimate to
the actual Euclidean operator norm, with exactly the same A_N. -/
theorem opNorm_linearResponse_le_gain_l2_of_kernel_factorization (R : Realization ι)
    (I : SpectralInterval) (N : ℕ) (c : ℕ → ℝ) (p q : ℕ → ℝ[X])
    (hfactor : ∀ s < N, ∀ lam ∈ Set.Icc I.mu I.L, ∀ nu ∈ Set.Icc I.mu I.L,
      R.kernel N s lam nu = c s*(p s).eval lam*(q s).eval nu)
    (lam0 nu0 : ℝ) (hlam0 : lam0 ∈ Set.Icc I.mu I.L) (hnu0 : nu0 ∈ Set.Icc I.mu I.L)
    (hp : ∀ s < N, ∀ lam ∈ Set.Icc I.mu I.L, |(p s).eval lam| ≤ |(p s).eval lam0|)
    (hq : ∀ s < N, ∀ nu ∈ Set.Icc I.mu I.L, |(q s).eval nu| ≤ |(q s).eval nu0|)
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    opNorm (R.linearResponse N H E) ≤
      R.gain I N*Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) := by
  have hterm (s : ℕ) (hs : s < N) :
      opNorm (c s • (aeval H (p s)*E s*aeval H (q s))) ≤
        |R.kernel N s lam0 nu0| * opNorm (E s) := by
    have hpl := opNorm_aeval_le (p s) I H hH hspec |(p s).eval lam0| (abs_nonneg _) (hp s hs)
    have hql := opNorm_aeval_le (q s) I H hH hspec |(q s).eval nu0| (abs_nonneg _) (hq s hs)
    rw [opNorm_smul,hfactor s hs lam0 hlam0 nu0 hnu0,abs_mul,abs_mul]
    calc
      _ ≤ |c s| * ((opNorm (aeval H (p s))*opNorm (E s))*opNorm (aeval H (q s))) :=
        mul_le_mul_of_nonneg_left ((opNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _))) (abs_nonneg _)
      _ ≤ |c s| * ((|(p s).eval lam0| * opNorm (E s))*|(q s).eval nu0|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul
          (mul_le_mul_of_nonneg_right hpl (opNorm_nonneg _)) hql (opNorm_nonneg _)
          (mul_nonneg (abs_nonneg _) (opNorm_nonneg _))) (abs_nonneg _)
      _ = _ := by ring
  have hsum : opNorm (R.linearResponse N H E) ≤
      ∑ s ∈ Finset.range N, |R.kernel N s lam0 nu0| * opNorm (E s) := by
    rw [R.linearResponse_eq_sum_of_kernel_factorization I N c p q hfactor H hH hspec E]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => hterm s (Finset.mem_range.mp hs))
  calc
    _ ≤ _ := hsum
    _ ≤ Real.sqrt (∑ s ∈ Finset.range N, |R.kernel N s lam0 nu0|^2)*
        Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = R.kernelNorm N lam0 nu0*Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) := by
      simp only [sq_abs,kernelNorm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (R.kernelNorm_le_gain I N hlam0 hnu0) (Real.sqrt_nonneg _)

end
end chebyshev1.Realization
