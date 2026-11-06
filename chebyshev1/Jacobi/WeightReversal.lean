import chebyshev1.Jacobi.SpectralWeights
import chebyshev1.Jacobi.Reversal

/-! Normalized inverse-spectral laws, with no unspecified proportionality constants. -/
namespace chebyshev1.JacobiData
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) {n : ℕ} (B : SpectralBasis (J.matrix 0 (n + 1)))

/-- The inverse-spectral persymmetry criterion with its normalization explicit. -/
theorem persymmetric_iff_normalized_spectral_weights
    (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n + 1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues) :
    (J.matrix 0 (n + 1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n + 1) ↔
      ∀ j, B.weight 0 j =
        (1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues j)|) /
          (∑ k, 1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)|) := by
  have hd (j : Fin (n + 1)) : (J.leading (n + 1)).derivative.eval (B.eigenvalues j) ≠ 0 := by
    rw [leading, J.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi j
  have hs : 0 < ∑ k, 1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)| :=
    Finset.sum_pos (fun k _ => one_div_pos.mpr (abs_pos.mpr (hd k))) Finset.univ_nonempty
  rw [J.persymmetric_iff_spectral_weights B hsq hpos hi]
  constructor
  · rintro ⟨c, hc, hw⟩
    have he : c * (∑ k, 1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)|) = 1 := by
      rw [Finset.mul_sum]
      simp_rw [mul_one_div, ← hw]
      exact B.weight_sum 0
    intro j
    rw [hw j]
    have hc' : c = 1 / (∑ k, 1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)|) :=
      (eq_div_iff hs.ne').mpr he
    rw [hc']
    ring
  · intro hw
    refine ⟨1 / (∑ k, 1 / |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)|),
      one_div_pos.mpr hs, ?_⟩
    intro j
    rw [hw j]
    ring

/-- Reversing the chain replaces a first spectral weight by the old last weight. -/
theorem spectral_weight_reversed (hsq : ∀ t, 0 ≤ J.aSq t)
    (hi : Function.Injective B.eigenvalues)
    (Brev : SpectralBasis ((J.reversed (n + 1)).matrix 0 (n + 1)))
    (heig : ∀ j, Brev.eigenvalues j = B.eigenvalues j) (j : Fin (n + 1)) :
    Brev.weight 0 j = B.weight (Fin.last n) j := by
  have hir : Function.Injective Brev.eigenvalues := by
    intro j k he
    apply hi
    simpa only [heig] using he
  have hr := (J.reversed (n + 1)).spectral_weight_cofactor Brev
    (J.reversed_aSq_nonneg hsq (n + 1)) hir 0 j
  have hl := J.spectral_weight_cofactor B hsq hi (Fin.last n) j
  rw [J.reversed_leading_terminal hsq (n + 1), heig j] at hr
  simp only [Fin.val_zero, leading_zero, Polynomial.eval_one, one_mul, Nat.zero_add,
    Nat.sub_zero] at hr
  rw [J.reversed_block hsq (n + 1) 1 n (by omega)] at hr
  simp only [Nat.add_sub_cancel, Nat.sub_self] at hr
  simp only [Fin.val_last, Nat.sub_self, block, Polynomial.eval_one, mul_one] at hl
  have hd : (J.leading (n + 1)).derivative.eval (B.eigenvalues j) ≠ 0 := by
    rw [leading, J.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi j
  exact mul_right_cancel₀ hd (hr.trans hl.symm)

/-- The last endpoint measure is the normalized reciprocal of `w_j P'_N(z_j)^2`. -/
theorem spectral_endpoint_weight_normalized
    (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n + 1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues) (j : Fin (n + 1)) :
    B.weight (Fin.last n) j =
      (1 / (B.weight 0 j * ((J.leading (n + 1)).derivative.eval (B.eigenvalues j)) ^ 2)) /
        (∑ k, 1 / (B.weight 0 k *
          ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)) ^ 2)) := by
  have hd (k : Fin (n + 1)) : (J.leading (n + 1)).derivative.eval (B.eigenvalues k) ≠ 0 := by
    rw [leading, J.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi k
  have hw (k : Fin (n + 1)) : B.weight 0 k ≠ 0 :=
    (J.spectral_endpoint_positive B hsq hpos hi k).1.ne'
  have he (k : Fin (n + 1)) : B.weight (Fin.last n) k =
      J.couplingProduct 1 n *
        (1 / (B.weight 0 k * ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)) ^ 2)) := by
    have hp := J.spectral_endpoint_product B hsq hi k
    field_simp [hw k, hd k]
    nlinarith [hp]
  have hs : J.couplingProduct 1 n *
      (∑ k, 1 / (B.weight 0 k *
        ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)) ^ 2)) = 1 := by
    rw [Finset.mul_sum]
    simp_rw [← he]
    exact B.weight_sum (Fin.last n)
  have hsne : (∑ k, 1 / (B.weight 0 k *
      ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)) ^ 2)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hs
    norm_num at hs
  rw [he j]
  apply (eq_div_iff hsne).mpr
  linear_combination (1 / (B.weight 0 j *
    ((J.leading (n + 1)).derivative.eval (B.eigenvalues j)) ^ 2)) * hs

end
end chebyshev1.JacobiData
