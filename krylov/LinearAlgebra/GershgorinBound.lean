import krylov.Stability.UniformGram
import krylov.LinearAlgebra.SpectralConditioning
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
Article: main_krylov, s4:cor-Q and apD:uniform, sharp actual Gram dimension factor.
Use: a true symmetric zero-diagonal entry bound has spectral factor n−1,
needed by the original pre-quadratic budget slack and uniform flag geometry.
Source: Gershgorin's circle theorem, mathlib eigenvalue_mem_ball, and the
existing genuine Hermitian spectral norm identity opNorm_aeval_eq.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset chebyshev1 krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- A genuine Hermitian zero-diagonal matrix with off-diagonal magnitudes at most η has spectral norm at most (n−1)η, including empty coefficient spaces.
Use: retain the original sharp dimension factor in the pre-quadratic source slack.
Article: main_krylov, s4:cor-Q and apD:uniform, true off-diagonal spectral bound.
Source: Gershgorin circle theorem, mathlib eigenvalue_mem_ball.
Proof: every genuine real Hermitian eigenvalue lies in an actual zero-centred
Gershgorin disc. Its radius sums exactly n−1 bounded real entries. The proved
true Hermitian spectral norm formula takes the maximum of those absolute
eigenvalues, with the empty matrix handled by the same finite norm formula. -/
theorem hermitian_zero_diagonal_norm_bound (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    (hdiag : ∀ i, H i i=0) {η : ℝ} (hη : 0≤η) (hentry : ∀ i j, i≠j → |H i j|≤η) :
    ‖H‖≤((p-1 : ℕ) : ℝ)*η := by
  -- Use actual Hermitian eigenvalues and their true Gershgorin radii before taking the spectral norm.
  have hn := opNorm_aeval_eq (Polynomial.X : Polynomial ℝ) H hH
  simp only [Polynomial.aeval_X,Polynomial.eval_X,opNorm] at hn
  rw [hn,pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hη)]
  intro i
  have he : Module.End.HasEigenvalue (Matrix.toLin' H) (hH.eigenvalues i) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact hH.eigenvalues_mem_spectrum_real i
  obtain ⟨j,hj⟩ := eigenvalue_mem_ball he
  have hr : ‖hH.eigenvalues i‖≤∑ l∈univ.erase j, ‖H j l‖ := by
    simpa only [Metric.mem_closedBall,hdiag,dist_zero_right] using hj
  apply hr.trans
  calc
    _ ≤ ∑ _l∈univ.erase j, η := sum_le_sum fun l hl => by
      simpa only [Real.norm_eq_abs] using hentry j l (ne_of_mem_erase hl).symm
    _ = _ := by simp only [sum_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin,nsmul_eq_mul]


/-- The actual Gram of n genuine unit vectors with pairwise angles at most η differs from identity in spectral norm by at most (n−1)η.
Use: prove the exact original pre-quadratic near-conjugacy constant without any smallest-step-energy denominator.
Article: main_krylov, s4:cor-Q, ε≤(n−1)W₀.
Proof: the genuine Gram difference is Hermitian with exactly zero diagonal.
Its actual off-diagonal entries are the original unit-vector pairings, so
the proved true zero-diagonal Gershgorin norm bound applies directly. -/
theorem unitGram_deviation_sharp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Fin p → E) (ht : ∀ i, ‖t i‖=1) {η : ℝ} (hη : 0≤η)
    (ha : ∀ i j, i≠j → |inner ℝ (t i) (t j)|≤η) :
    ‖crossGram t t-1‖≤((p-1 : ℕ) : ℝ)*η := by
  -- Unit normalization removes the true diagonal exactly; only the genuine pairwise angles remain.
  have hsym : (crossGram t t-1).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (by
    ext i j
    simp only [Matrix.transpose_apply,Matrix.sub_apply,crossGram,real_inner_comm,Matrix.one_apply]
    split_ifs <;> simp_all)
  have hdiag (i : Fin p) : (crossGram t t-1) i i=0 := by
    simp only [Matrix.sub_apply,crossGram,Matrix.one_apply_eq,real_inner_self_eq_norm_sq,ht,one_pow,sub_self]
  apply hermitian_zero_diagonal_norm_bound _ hsym hdiag hη
  intro i j hij
  simpa only [Matrix.sub_apply,crossGram,Matrix.one_apply_ne hij,sub_zero] using ha i j hij

end
end krylov.LinearAlgebra
