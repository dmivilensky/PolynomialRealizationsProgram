import krylov.Strings.DiscreteDivergence
import krylov.Strings.DiscreteSpectral
import krylov.LinearAlgebra.SpectralConditioning
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
Article: main_krylov, apC:lem:stieltjes(b,c).
Use: identify the actual operator norm with its full spectral support and
bound it by the literal mass-normalized path rows. These estimates control
the spectral support of the recovery strings.
Source: orthogonal invariance of the Euclidean operator norm and the
standard Gershgorin theorem from mathlib.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix.Norms.L2Operator

/-- The actual norm identity holds for every complete orthogonal eigenbasis,
including the particular basis produced by inverse spectral reconstruction. -/
theorem spectralBasis_norm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (B : SpectralBasis H) : ‖H‖ = ‖B.eigenvalues‖ := by
  let U : unitary (Matrix ι ι ℝ) := ⟨B.Q, by
    simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      And.intro B.transpose_mul B.mul_transpose⟩
  conv_lhs => rw [← B.reconstruct]
  change ‖(U : Matrix ι ι ℝ) * diagonal B.eigenvalues * B.Qᵀ‖ = _
  have ht : B.Qᵀ = (star U : unitary (Matrix ι ι ℝ)) := by
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U]
  rw [ht, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

/-- Positivity of the genuine matrix gives nonnegative values in any actual
orthogonal eigenbasis, without choosing or sorting a second spectrum. -/
theorem spectralBasis_eigenvalues_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (B : SpectralBasis H) (hH : H.PosSemidef) (i : ι) :
    0 ≤ B.eigenvalues i := by
  have hp := (coordinates_posSemidef_iff B H).2 hH
  change (B.Qᵀ * H * B.Q).PosSemidef at hp
  rw [B.diagonalize, Matrix.posSemidef_diagonal_iff] at hp
  exact hp i

end
end krylov.LinearAlgebra

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Finset chebyshev1
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- The full actual finite spectral support has the true physical operator
norm, independently of the ordering of its atoms. -/
theorem spectralRadius_eq_spectralBasis_norm (B : SpectralBasis S.operator) :
    S.spectralRadius = ‖B.eigenvalues‖ :=
  LinearAlgebra.spectralBasis_norm_eq B

/-- The genuine spectral radius is the largest physical spectral node. -/
theorem spectralRadius_isGreatest (B : SpectralBasis S.operator) :
    IsGreatest (Set.range B.eigenvalues) S.spectralRadius := by
  have h0 (i) := LinearAlgebra.spectralBasis_eigenvalues_nonneg B S.operator_posSemidef i
  have hn := S.spectralRadius_eq_spectralBasis_norm B
  obtain ⟨i, hi⟩ := Finset.exists_max_image univ B.eigenvalues univ_nonempty
  refine ⟨⟨i, ?_⟩, ?_⟩
  · apply le_antisymm
    · rw [hn]
      simpa only [Real.norm_of_nonneg (h0 i)] using norm_le_pi_norm B.eigenvalues i
    · rw [hn, pi_norm_le_iff_of_nonneg (h0 i)]
      intro j
      rw [Real.norm_of_nonneg (h0 j)]
      exact hi.2 j (mem_univ j)
  · rintro _ ⟨j, rfl⟩
    rw [hn]
    simpa only [Real.norm_of_nonneg (h0 j)] using norm_le_pi_norm B.eigenvalues j

/-- A physical upper Gershgorin row bound controls the actual positive
operator norm. No diagonal-dominance lower bound is required. -/
theorem spectralRadius_le_of_rows {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ i, S.operator i i + ∑ j ∈ univ.erase i, ‖S.operator i j‖ ≤ b) :
    S.spectralRadius ≤ b := by
  apply LinearAlgebra.spectral_norm_le_of_eigenvalues _ S.operator_isHermitian hb
  intro i
  refine ⟨S.operator_eigenvalue_nonneg i, ?_⟩
  have he : Module.End.HasEigenvalue (Matrix.toLin' S.operator)
      (S.operator_isHermitian.eigenvalues i) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact S.operator_isHermitian.eigenvalues_mem_spectrum_real i
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall, Real.dist_eq] at hj
  linarith [(abs_le.mp hj).2, hrow j]

/-- The two physical off-diagonal conductances incident to a site. -/
def offDiagonalRow (i : Fin (N + 1)) : ℝ :=
  (if 0 < i.val then (S.gap (i.val - 1))⁻¹ *
    (Real.sqrt (S.mass (i.val - 1)))⁻¹ * (Real.sqrt (S.mass i.val))⁻¹ else 0) +
  (if i.val < N then (S.gap i.val)⁻¹ *
    (Real.sqrt (S.mass i.val))⁻¹ * (Real.sqrt (S.mass (i.val + 1)))⁻¹ else 0)

/-- Exact physical source row, including the missing-edge conventions and
the genuine terminal Robin term. -/
def gershgorinRow (i : Fin (N + 1)) : ℝ :=
  (if i.val < N then (S.gap i.val)⁻¹ * (S.mass i.val)⁻¹ else 0) +
  (if 0 < i.val then (S.gap (i.val - 1))⁻¹ * (S.mass i.val)⁻¹ else 0) +
  (if i.val = N then S.robin * (S.mass i.val)⁻¹ else 0) + S.offDiagonalRow i

private theorem offDiagonal_entry (i j : Fin (N + 1)) (hij : i ≠ j) :
    ‖S.operator i j‖ =
      (if j.val + 1 = i.val then (S.gap (i.val - 1))⁻¹ *
        (Real.sqrt (S.mass (i.val - 1)))⁻¹ * (Real.sqrt (S.mass i.val))⁻¹ else 0) +
      (if i.val + 1 = j.val then (S.gap i.val)⁻¹ *
        (Real.sqrt (S.mass i.val))⁻¹ * (Real.sqrt (S.mass (i.val + 1)))⁻¹ else 0) := by
  have hv : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  by_cases hl : j.val + 1 = i.val
  · have he : S.operator i j = S.operator j i := by
      have h := congrArg (fun A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ↦ A j i)
        S.operator_isHermitian.eq
      simpa only [Matrix.conjTranspose_apply, star_trivial] using h
    rw [he, Real.norm_eq_abs, abs_of_neg (S.operator_adjacent_neg j i hl),
      S.operator_adjacent j i hl]
    have hp : i.val - 1 = j.val := by omega
    simp only [hl, ite_true, show ¬i.val + 1 = j.val by omega, ite_false, add_zero, hp]
    ring
  · by_cases hr : i.val + 1 = j.val
    · rw [Real.norm_eq_abs, abs_of_neg (S.operator_adjacent_neg i j hr),
        S.operator_adjacent i j hr]
      simp only [hl, ite_false, hr, ite_true, zero_add]
      ring
    · rw [S.operator_tridiagonal i j (by omega), norm_zero]
      simp only [hl, hr, ite_false, add_zero]

/-- Summing the actual path entries gives exactly the two source edge
terms; there are no hidden dimension factors. -/
theorem offDiagonalRow_eq (i : Fin (N + 1)) :
    (∑ j ∈ univ.erase i, ‖S.operator i j‖) = S.offDiagonalRow i := by
  have he : (∑ j ∈ univ.erase i, ‖S.operator i j‖) =
      ∑ j : Fin (N + 1),
        ((if j.val + 1 = i.val then (S.gap (i.val - 1))⁻¹ *
          (Real.sqrt (S.mass (i.val - 1)))⁻¹ * (Real.sqrt (S.mass i.val))⁻¹ else 0) +
        (if i.val + 1 = j.val then (S.gap i.val)⁻¹ *
          (Real.sqrt (S.mass i.val))⁻¹ * (Real.sqrt (S.mass (i.val + 1)))⁻¹ else 0)) := by
    rw [← sum_erase_add _ _ (mem_univ i)]
    have hz : ((if i.val + 1 = i.val then (S.gap (i.val - 1))⁻¹ *
          (Real.sqrt (S.mass (i.val - 1)))⁻¹ * (Real.sqrt (S.mass i.val))⁻¹ else 0) +
        (if i.val + 1 = i.val then (S.gap i.val)⁻¹ *
          (Real.sqrt (S.mass i.val))⁻¹ * (Real.sqrt (S.mass (i.val + 1)))⁻¹ else 0)) = 0 := by
      simp only [show ¬i.val + 1 = i.val by omega, ite_false, add_zero]
    rw [hz, add_zero]
    exact sum_congr rfl fun j hj ↦ S.offDiagonal_entry i j (ne_of_mem_erase hj).symm
  rw [he, sum_add_distrib]
  unfold offDiagonalRow
  congr 1
  · by_cases hi : 0 < i.val
    · have hp : i.val - 1 < N + 1 := by omega
      have he (j : Fin (N + 1)) : j.val + 1 = i.val ↔ j = ⟨i.val - 1, hp⟩ := by
        simp only [Fin.ext_iff]
        omega
      simp only [he, sum_ite_eq', mem_univ, ite_true, hi]
    · have he (j : Fin (N + 1)) : ¬j.val + 1 = i.val := by omega
      simp only [he, ite_false, sum_const_zero, hi]
  · by_cases hi : i.val < N
    · have hp : i.val + 1 < N + 1 := by omega
      have he (j : Fin (N + 1)) : i.val + 1 = j.val ↔ j = ⟨i.val + 1, hp⟩ := by
        simp only [Fin.ext_iff]
        omega
      simp only [he, sum_ite_eq', mem_univ, ite_true, hi]
    · have he (j : Fin (N + 1)) : ¬i.val + 1 = j.val := by omega
      simp only [he, ite_false, sum_const_zero, hi]

/-- Literal Gershgorin bound from the original string masses and gaps. -/
theorem spectralRadius_le_of_gershgorinRows {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ i, S.gershgorinRow i ≤ b) : S.spectralRadius ≤ b := by
  apply S.spectralRadius_le_of_rows hb
  intro i
  rw [S.operator_diagonal, S.offDiagonalRow_eq]
  exact hrow i

end
end krylov.Strings.DiscreteString
