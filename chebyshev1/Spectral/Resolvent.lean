import chebyshev1.Spectral.Weights
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Spectral-weight formulas for resolvents and their squared eigenvalues. -/
namespace chebyshev1.SpectralBasis
noncomputable section
open Polynomial Filter Topology
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {H : Matrix d d ℝ}

/-- The resolvent diagonal is represented by the spectral weights. -/
theorem resolvent_diagonal_sum (B : SpectralBasis H) (x : ℝ)
    (hx : ∀ j, x - B.eigenvalues j ≠ 0) (s : d) :
    (Matrix.scalar d x - H)⁻¹ s s =
      ∑ j, B.weight s j / (x - B.eigenvalues j) := by
  have he : Matrix.scalar d x - H =
      B.Q * Matrix.diagonal (fun j => x - B.eigenvalues j) * B.Qᵀ := by
    have hs : B.Q * Matrix.scalar d x * B.Qᵀ = Matrix.scalar d x := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, B.mul_transpose]
    calc
      _ = B.Q * Matrix.scalar d x * B.Qᵀ -
          B.Q * Matrix.diagonal B.eigenvalues * B.Qᵀ :=
        (congrArg₂ Sub.sub hs B.reconstruct).symm
      _ = _ := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.scalar_apply,
          ← Matrix.diagonal_sub]
  have hinv : (Matrix.scalar d x - H)⁻¹ =
      B.Q * Matrix.diagonal (fun j => (x - B.eigenvalues j)⁻¹) * B.Qᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [he]
    have hd : Matrix.diagonal (fun j => x - B.eigenvalues j) *
        Matrix.diagonal (fun j => (x - B.eigenvalues j)⁻¹) = (1 : Matrix d d ℝ) := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, hx]
    calc
      _ = B.Q * (Matrix.diagonal (fun j => x - B.eigenvalues j) *
          Matrix.diagonal (fun j => (x - B.eigenvalues j)⁻¹)) * B.Qᵀ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc B.Qᵀ B.Q, B.transpose_mul, Matrix.one_mul]
      _ = 1 := by rw [hd, Matrix.mul_one, B.mul_transpose]
  rw [hinv, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, weight]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weight_column_sum (B : SpectralBasis H) (j : d) : ∑ s, B.weight s j = 1 := by
  have h := congrArg (fun M : Matrix d d ℝ => M j j) B.transpose_mul
  simpa only [weight, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two]
    using h

/-- Squared diagonal entries are bounded by the squared spectral values. -/
theorem weighted_diagonal_energy_le (B : SpectralBasis H) (v : d → ℝ) :
    (∑ s, (∑ j, B.weight s j * v j)^2) ≤ ∑ j, (v j)^2 := by
  have hlocal (s : d) : (∑ j, B.weight s j * v j)^2 ≤ ∑ j, B.weight s j * (v j)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => B.Q s j) (fun j => B.Q s j*v j)
    have h₁ : (∑ j, B.Q s j * (B.Q s j*v j)) = ∑ j, B.weight s j*v j := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [weight]
      ring
    have h₂ : (∑ j, (B.Q s j*v j)^2) = ∑ j, B.weight s j*(v j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [weight]
      ring
    have hsum : (∑ j, (B.Q s j)^2) = 1 := B.weight_sum s
    rw [h₁, h₂, hsum, one_mul] at h
    exact h
  calc
    _ ≤ ∑ s, ∑ j, B.weight s j*(v j)^2 := Finset.sum_le_sum (fun s _ => hlocal s)
    _ = ∑ j, (v j)^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, B.weight_column_sum, one_mul]

theorem charpoly_log_derivative (B : SpectralBasis H) (x : ℝ)
    (hx : ∀ j, x-B.eigenvalues j ≠ 0) :
    H.charpoly.derivative.eval x / H.charpoly.eval x = ∑ j, 1/(x-B.eigenvalues j) := by
  have hfun : (fun y : ℝ => H.charpoly.eval y) =
      fun y => ∏ j, (y-B.eigenvalues j) := by
    funext y
    rw [B.charpoly_factor, eval_prod]
    simp
  have hlog := logDeriv_fun_prod (s := Finset.univ)
    (f := fun j (y : ℝ) => y-B.eigenvalues j)
    (by intro j _; exact hx j) (by intro j _; fun_prop)
  rw [← hfun, logDeriv_apply, H.charpoly.deriv] at hlog
  convert hlog using 1
  apply Finset.sum_congr rfl
  intro j _
  simp [logDeriv_apply]

theorem reciprocal_gap_square_sum (B : SpectralBasis H) (x : ℝ)
    (hx : ∀ j, x-B.eigenvalues j ≠ 0) :
    (∑ j, (1/(x-B.eigenvalues j))^2) =
      (H.charpoly.derivative.eval x / H.charpoly.eval x)^2 -
        H.charpoly.derivative.derivative.eval x / H.charpoly.eval x := by
  have hp : H.charpoly.eval x ≠ 0 := by
    rw [B.charpoly_factor, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (by simpa using hx)
  have hleft := (H.charpoly.derivative.hasDerivAt x).div (H.charpoly.hasDerivAt x) hp
  have hright := HasDerivAt.fun_sum (u := Finset.univ) (fun j (_ : j ∈ Finset.univ) =>
    ((hasDerivAt_id x).sub_const (B.eigenvalues j)).inv (hx j))
  have hne : ∀ᶠ y in 𝓝 x, ∀ j, y-B.eigenvalues j ≠ 0 := by
    rw [eventually_all]
    intro j
    exact (continuousAt_id.sub_const (B.eigenvalues j)).eventually_ne (hx j)
  have heq : (fun y => ∑ j, (y-B.eigenvalues j)⁻¹) =ᶠ[𝓝 x]
      (fun y => H.charpoly.derivative.eval y / H.charpoly.eval y) := by
    filter_upwards [hne] with y hy
    simpa only [one_div] using (B.charpoly_log_derivative y hy).symm
  have he := hleft.unique (hright.congr_of_eventuallyEq heq.symm)
  simp only [id_eq, neg_div, Finset.sum_neg_distrib, div_pow, one_pow] at he ⊢
  field_simp [hp] at he ⊢
  nlinarith

end
end chebyshev1.SpectralBasis
