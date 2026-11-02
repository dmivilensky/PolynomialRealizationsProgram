import krylov.LinearAlgebra.SpectralConditioning

/-!
Article: main_krylov, thm:UCq and thm:UCg, true normalized spectral bounds.
Use: Recover actual lower eigenvalue bounds from real quadratic forms,
transfer them through a controlled norm perturbation and true diagonal
normalization, including empty coefficient spaces and zero endpoints.
Source: the reused real spectral coordinates and positive-semidefinite
criterion; standard Rayleigh form, operator norm and congruence estimates.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {p : ℕ}

/-- A genuine lower Euclidean quadratic-form bound implies the same lower bound for every true Hermitian eigenvalue.
Use: Transfer actual measured spectral-gate bounds to the true step-normalized model and Gram matrix.
Article: main_krylov, thm:UCq and thm:UCg, genuine spectral normalization.
Proof: Test the actual shifted quadratic form, use true orthogonal spectral coordinates and retain exact real matrix actions.
-/
theorem spectral_lower_of_form (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    {a : ℝ} (hform : ∀ v : EuclideanSpace ℝ (Fin p),
      a*‖v‖^2 ≤ (inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H v))) :
    ∀ i, a≤hH.eigenvalues i := by
  -- The true shifted form is positive semidefinite; its genuine diagonal spectral coordinates give every original lower eigenvalue.
  let B := SpectralBasis.ofHermitian H hH
  have hp : ((-a) • (1 : Matrix (Fin p) (Fin p) ℝ)+H).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.ext
      intro i j
      have he : H j i=H i j := by simpa only [star_trivial] using hH.apply i j
      simp [Matrix.one_apply,he,eq_comm]
    · intro x
      rw [← Matrix.inner_toEuclideanCLM]
      simp only [map_add,map_smul,map_one,_root_.add_apply,_root_.smul_apply,one_apply_eq_self]
      change 0 ≤ (inner ℝ (WithLp.toLp 2 x)
        ((-a) • (WithLp.toLp 2 x)+Matrix.toEuclideanCLM (𝕜 := ℝ) H (WithLp.toLp 2 x)))
      rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
      linarith [hform (WithLp.toLp 2 x)]
  have hc := (coordinates_posSemidef_iff B _).mpr hp
  rw [coordinates_lower_shift,Matrix.posSemidef_diagonal_iff] at hc
  intro i
  have hi := hc i
  change 0≤-a+hH.eigenvalues i at hi
  linarith


/-- An actual operator norm perturbation lowers every true Hermitian spectral lower bound by at most its norm bound.
Use: Transfer actual measured spectral-gate bounds to the true step-normalized model and Gram matrix.
Article: main_krylov, thm:UCq and thm:UCg, genuine spectral normalization.
Proof: Test the actual shifted quadratic form, use true orthogonal spectral coordinates and retain exact real matrix actions.
-/
theorem spectral_lower_perturbation (H G : Matrix (Fin p) (Fin p) ℝ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) {a δ : ℝ}
    (hlo : ∀ i, a≤hH.eigenvalues i) (hd : ‖G-H‖≤δ) :
    ∀ i, a-δ≤hG.eigenvalues i := by
  -- The actual norm of the model difference controls its real Rayleigh form on the same unchanged vector.
  apply spectral_lower_of_form G hG
  intro v
  have hl := spectral_lower_form H hH hlo v
  have hn := norm_inner_le_norm (𝕜 := ℝ) v (Matrix.toEuclideanCLM (𝕜 := ℝ) (G-H) v)
  rw [Real.norm_eq_abs] at hn
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) (G-H)).le_opNorm v
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  have hi : |inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (G-H) v)|≤δ*‖v‖^2 := by
    calc
      _ ≤ ‖v‖*(‖G-H‖*‖v‖) := hn.trans (mul_le_mul_of_nonneg_left ho (norm_nonneg _))
      _ ≤ δ*‖v‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v‖)]
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) G v=
      Matrix.toEuclideanCLM (𝕜 := ℝ) H v+Matrix.toEuclideanCLM (𝕜 := ℝ) (G-H) v := by
    rw [map_sub,_root_.sub_apply]
    abel
  rw [he,inner_add_right]
  have hlower := (abs_le.mp hi).1
  nlinarith


/-- A genuine diagonal congruence with squared entries bounded below transfers the actual positive spectral lower endpoint with the exact scalar factor.
Use: Transfer actual measured spectral-gate bounds to the true step-normalized model and Gram matrix.
Article: main_krylov, thm:UCq and thm:UCg, genuine spectral normalization.
Proof: Test the actual shifted quadratic form, use true orthogonal spectral coordinates and retain exact real matrix actions.
-/
theorem diagonal_congruence_spectral_lower (H : Matrix (Fin p) (Fin p) ℝ)
    (hH : H.IsHermitian) (q : Fin p → ℝ)
    (hG : (diagonal q*H*diagonal q).IsHermitian)
    {γ r : ℝ} (hγ : 0≤γ) (hlo : ∀ i, γ≤hH.eigenvalues i) (hq : ∀ i, r≤(q i)^2) :
    ∀ i, γ*r≤hG.eigenvalues i := by
  -- The genuine diagonal map expands every coefficient norm by at least the certified squared factor before testing the original lower spectral form.
  have hQ : (diagonal q).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij,eq_comm]
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  apply spectral_lower_of_form _ hG
  intro v
  have hnorm : r*‖v‖^2≤‖Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal q) v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec_diagonal]
    change r*(∑ i, (v i)^2)≤∑ i, (q i*v i)^2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_right (hq i) (sq_nonneg (v i))]
  have hlow := spectral_lower_form H hH hlo (Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal q) v)
  have he : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal q*H*diagonal q) v)=
      inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal q) v)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) H (Matrix.toEuclideanCLM (𝕜 := ℝ) (diagonal q) v)) := by
    rw [map_mul,map_mul]
    exact (hsym v _).symm
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hnorm hγ]

end
end krylov.LinearAlgebra
