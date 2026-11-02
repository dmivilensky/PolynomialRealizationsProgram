import krylov.Strings.DiscreteState
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import krylov.LinearAlgebra.GershgorinInterval
import krylov.LinearAlgebra.SpectralUpperForm

/-!
Article: `main_krylov`, `apC:lem:stieltjes`, physical finite string operator.
The symmetric mass-normalized operator is constructed as the sum of the
actual positive edge energies and the terminal Robin energy. This proves
positivity from masses and gaps before any spectral theorem is used.
Source: the standard weighted path Laplacian quadratic form.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {N : ℕ} (S : DiscreteString N)

/-- Actual physical edge vector in the mass-normalized coordinates. -/
def edgeVector (k : Fin N) (i : Fin (N + 1)) : ℝ :=
  (if i.val = k.val then (Real.sqrt (S.mass i.val))⁻¹ else 0) -
    (if i.val = k.val + 1 then (Real.sqrt (S.mass i.val))⁻¹ else 0)

/-- Actual mass-normalized last-site vector. -/
def lastVector (i : Fin (N + 1)) : ℝ :=
  if i.val = N then (Real.sqrt (S.mass i.val))⁻¹ else 0

/-- The actual symmetric representation `M⁻¹ᐟ² G M⁻¹ᐟ²`, built from its
positive physical edge energies and terminal boundary energy. -/
def operator : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (∑ k : Fin N, (S.gap k.val)⁻¹ • vecMulVec (S.edgeVector k) (S.edgeVector k)) +
    S.robin • vecMulVec S.lastVector S.lastVector

/-- Positive masses, gaps and Robin parameter give the genuine positive
semidefinite physical operator, with no spectral positivity premise. -/
theorem operator_posSemidef : S.operator.PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.posSemidef_sum
    intro k _
    have he : (vecMulVec (S.edgeVector k) (S.edgeVector k)).PosSemidef := by
      simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (S.edgeVector k)
    exact he.smul (inv_nonneg.mpr (S.gap_pos k.val k.isLt).le)
  · have he : (vecMulVec S.lastVector S.lastVector).PosSemidef := by
      simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star S.lastVector
    exact he.smul S.robin_nonneg

/-- The normalized physical operator is genuinely selfadjoint. -/
theorem operator_isHermitian : S.operator.IsHermitian := S.operator_posSemidef.isHermitian

/-- An edge has no component at a nonincident physical site. -/
theorem edgeVector_eq_zero {k : Fin N} {i : Fin (N + 1)}
    (h₀ : i.val ≠ k.val) (h₁ : i.val ≠ k.val + 1) : S.edgeVector k i = 0 := by
  simp only [edgeVector, ite_eq_right h₀, ite_eq_right h₁, sub_zero]

/-- The actual positive edge-energy construction has the exact tridiagonal
band of the source weighted path Laplacian. -/
theorem operator_tridiagonal (i j : Fin (N + 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : S.operator i j = 0 := by
  have he : ∀ k : Fin N, S.edgeVector k i * S.edgeVector k j = 0 := by
    intro k
    by_cases hi : i.val = k.val ∨ i.val = k.val + 1
    · rw [S.edgeVector_eq_zero (i := j) (by omega) (by omega), mul_zero]
    · rw [S.edgeVector_eq_zero (i := i) (by omega) (by omega), zero_mul]
  have ht : S.lastVector i * S.lastVector j = 0 := by
    by_cases hi : i.val = N
    · simp only [lastVector, ite_eq_left hi, ite_eq_right (show j.val ≠ N by omega), mul_zero]
    · simp only [lastVector, ite_eq_right hi, zero_mul]
  simp only [operator, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, he,
    ht, mul_zero, Finset.sum_const_zero, zero_add]

/-- Every actual adjacent physical entry has precisely the source negative
coupling, with both true masses and the actual intervening gap. -/
theorem operator_adjacent (i j : Fin (N + 1)) (hij : i.val + 1 = j.val) :
    S.operator i j = -(S.gap i.val)⁻¹ * (Real.sqrt (S.mass i.val))⁻¹ *
      (Real.sqrt (S.mass j.val))⁻¹ := by
  let k : Fin N := ⟨i.val, by omega⟩
  have hi : S.edgeVector k i = (Real.sqrt (S.mass i.val))⁻¹ := by
    simp [edgeVector, k]
  have hj : S.edgeVector k j = -(Real.sqrt (S.mass j.val))⁻¹ := by
    simp only [edgeVector, k, ite_eq_right (show j.val ≠ i.val by omega), ite_eq_left hij.symm, zero_sub]
  have hz : ∀ r : Fin N, r ≠ k → S.edgeVector r i * S.edgeVector r j = 0 := by
    intro r hr
    have hri : i.val ≠ r.val := fun h ↦ hr (Fin.ext h.symm)
    by_cases hip : i.val = r.val + 1
    · rw [S.edgeVector_eq_zero (i := j) (by omega) (by omega), mul_zero]
    · rw [S.edgeVector_eq_zero hri hip, zero_mul]
  have hs : (∑ r : Fin N, (S.gap r.val)⁻¹ * (S.edgeVector r i * S.edgeVector r j)) =
      (S.gap i.val)⁻¹ * ((Real.sqrt (S.mass i.val))⁻¹ * -(Real.sqrt (S.mass j.val))⁻¹) := by
    rw [Finset.sum_eq_single k]
    · rw [hi, hj]
    · intro r _ hr
      rw [hz r hr, mul_zero]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  have ht : S.lastVector i = 0 := by
    simp only [lastVector, ite_eq_right (show i.val ≠ N by omega)]
  simp only [operator, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
    hs, ht, zero_mul, mul_zero, add_zero]
  ring

/-- Every genuine normalized adjacent coupling is strictly negative. -/
theorem operator_adjacent_neg (i j : Fin (N + 1)) (hij : i.val + 1 = j.val) :
    S.operator i j < 0 := by
  rw [operator_adjacent S i j hij]
  have hg := inv_pos.mpr (S.gap_pos i.val (by omega))
  have hm := inv_pos.mpr (Real.sqrt_pos.mpr (S.mass_pos i.val (by omega)))
  have hn := inv_pos.mpr (Real.sqrt_pos.mpr (S.mass_pos j.val (by omega)))
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hg) hm) hn

/-- The actual finite physical spectral radius. All spectral values are
nonnegative, so this is the top energy rather than an absolute-value bound. -/
def spectralRadius : ℝ := ‖S.operator‖

/-- Every actual eigenvalue of the physical string is nonnegative. -/
theorem operator_eigenvalue_nonneg (i : Fin (N + 1)) :
    0 ≤ S.operator_isHermitian.eigenvalues i :=
  S.operator_posSemidef.eigenvalues_nonneg i

/-- Every actual physical spectral value is bounded by the operator norm. -/
theorem operator_eigenvalue_le (i : Fin (N + 1)) :
    S.operator_isHermitian.eigenvalues i ≤ S.spectralRadius := by
  exact (le_abs_self _).trans (by
    simpa only [spectralRadius, Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem
      (S.operator_isHermitian.eigenvalues_mem_spectrum_real i))

/-- The actual physical Rayleigh quotient at a site is bounded by the true
operator norm. -/
theorem operator_diagonal_le (i : Fin (N + 1)) : S.operator i i ≤ S.spectralRadius := by
  let B := chebyshev1.SpectralBasis.ofHermitian S.operator S.operator_isHermitian
  have hp : (S.spectralRadius • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - S.operator).PosSemidef := by
    rw [← krylov.LinearAlgebra.coordinates_posSemidef_iff B,
      krylov.LinearAlgebra.coordinates_upper_shift, Matrix.posSemidef_diagonal_iff]
    intro k
    exact sub_nonneg.mpr (S.operator_eigenvalue_le k)
  have h := hp.diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, sub_nonneg] using h

/-- Every positive edge energy contributes its actual squared component to
the physical Rayleigh quotient at an incident site. -/
theorem edge_diagonal_le (k : Fin N) (i : Fin (N + 1)) :
    (S.gap k.val)⁻¹ * S.edgeVector k i ^ 2 ≤ S.operator i i := by
  have hs : (S.gap k.val)⁻¹ * S.edgeVector k i ^ 2 ≤
      ∑ r : Fin N, (S.gap r.val)⁻¹ * S.edgeVector r i ^ 2 := by
    apply Finset.single_le_sum (f := fun r : Fin N ↦ (S.gap r.val)⁻¹ * S.edgeVector r i ^ 2)
      (s := Finset.univ) (a := k)
    · intro r _
      exact mul_nonneg (inv_nonneg.mpr (S.gap_pos r.val r.isLt).le) (sq_nonneg _)
    · exact Finset.mem_univ k
  have ht : 0 ≤ S.robin * S.lastVector i ^ 2 := mul_nonneg S.robin_nonneg (sq_nonneg _)
  calc
    _ ≤ (∑ r : Fin N, (S.gap r.val)⁻¹ * S.edgeVector r i ^ 2) + S.robin * S.lastVector i ^ 2 := by
      linarith
    _ = S.operator i i := by
      simp only [operator, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, vecMulVec_apply, pow_two]

/-- The source strict gap-mass inequality follows directly from the genuine
physical Rayleigh quotient, without presupposing a top solution. -/
theorem top_gap_mass {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (j : ℕ) (hj : j < N) :
    1 < Λ * S.mass (j + 1) * S.gap j := by
  let k : Fin N := ⟨j, hj⟩
  let i : Fin (N + 1) := ⟨j + 1, by omega⟩
  have hv : S.edgeVector k i = -(Real.sqrt (S.mass (j + 1)))⁻¹ := by
    simp [edgeVector, k, i]
  have he : S.edgeVector k i ^ 2 = (S.mass (j + 1))⁻¹ := by
    rw [hv, neg_sq, inv_pow, Real.sq_sqrt (S.mass_pos (j + 1) (by omega)).le]
  have h := (S.edge_diagonal_le k i).trans_lt ((S.operator_diagonal_le i).trans_lt hΛ)
  rw [he] at h
  change (S.gap j)⁻¹ * (S.mass (j + 1))⁻¹ < Λ at h
  have hm := S.mass_pos (j + 1) (by omega)
  have hl := S.gap_pos j hj
  have hh := mul_lt_mul_of_pos_right h (mul_pos hm hl)
  have hid : (S.gap j)⁻¹ * (S.mass (j + 1))⁻¹ * (S.mass (j + 1) * S.gap j) = 1 := by
    field_simp
  rw [hid] at hh
  nlinarith

end
end krylov.Strings.DiscreteString
