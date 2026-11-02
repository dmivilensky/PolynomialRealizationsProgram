import krylov.LinearAlgebra.SpectralConditioning
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual physical upper spectral form.
Use: derive true original physical quadratic window bounds from genuine matrix eigenvalue bounds before compressing the actual CG reference.
Source: actual orthogonal spectral coordinates and genuine shifted positive semidefinite quadratic forms.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
variable {p : ℕ}

/-- A true upper eigenvalue bound controls the genuine physical Euclidean quadratic form.
Use: A true upper eigenvalue bound controls the genuine physical Euclidean quadratic form.
Article: main_krylov, prop:phi(a), actual physical upper spectral form.
Proof: Diagonalize the original upper shifted form, prove its actual positivity and test the true physical vector. -/
theorem spectral_upper_form (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    {b : ℝ} (he : ∀ i,hH.eigenvalues i≤b) (v : EuclideanSpace ℝ (Fin p)) :
    inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H v)≤b*‖v‖^2 := by
  -- The actual upper shifted form is tested on the original physical vector after genuine spectral positivity is established.
  let B := SpectralBasis.ofHermitian H hH
  have hp : (b • (1 : Matrix (Fin p) (Fin p) ℝ)-H).PosSemidef := by
    rw [← coordinates_posSemidef_iff B,coordinates_upper_shift,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (he i)
  have ht := hp.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  simp only [star_trivial] at ht
  rw [← Matrix.inner_toEuclideanCLM] at ht
  simp only [map_sub,map_smul,map_one,_root_.sub_apply,_root_.smul_apply,one_apply_eq_self] at ht
  change 0≤ inner ℝ v (b • v-Matrix.toEuclideanCLM (𝕜 := ℝ) H v) at ht
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at ht
  linarith
end
end krylov.LinearAlgebra
