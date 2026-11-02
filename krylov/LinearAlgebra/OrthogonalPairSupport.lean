import krylov.LinearAlgebra.PlanarWitness

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine symmetric two-plane support attainer.
Use: realize the actual last-nontrivial singleton tilt bound by a real
symmetric rank-two unit spectral-norm increment on its true orthogonal plane.
Source: standard real inner-product Cauchy--Schwarz and the already proved
actual planar spectral witness and genuine matrix/operator action.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine pairing with an actual unit vector and every real unit spectral-budget matrix is bounded by the true other-vector norm.
Use: The genuine pairing with an actual unit vector and every real unit spectral-budget matrix is bounded by the true other-vector norm.
Article: main_krylov, thm:select, genuine symmetric two-plane support attainer.
Proof: Apply real Cauchy--Schwarz and the actual Euclidean matrix operator norm bound. -/
theorem symmetric_pairing_unit_bound (a b : EuclideanSpace ℝ (Fin n)) (hb : ‖b‖=1)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : ‖D‖≤1) :
    |inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) D b)|≤‖a‖ := by
  have hd : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D b‖≤1 := by
    have he := (Matrix.toEuclideanCLM (𝕜 := ℝ) D).le_opNorm b
    rw [hb,mul_one] at he
    exact he.trans hD
  exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg a])

/-- For every genuine nonzero vector and actual orthogonal unit vector, a real symmetric unit-budget rank-two matrix attains their true norm pairing.
Use: For every genuine nonzero vector and actual orthogonal unit vector, a real symmetric unit-budget rank-two matrix attains their true norm pairing.
Article: main_krylov, thm:select, genuine symmetric two-plane support attainer.
Proof: Normalize the actual nonzero vector and reuse the genuine symmetric cross-plane spectral witness; its real action sends the true unit vector to the actual normalized other vector. -/
theorem orthogonal_symmetric_pairing_attained (a b : EuclideanSpace ℝ (Fin n))
    (ha : a≠0) (hb : ‖b‖=1) (hab : inner ℝ a b=0) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ, D.IsSymm ∧ ‖D‖≤1 ∧
      inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) D b)=‖a‖ := by
  -- The genuine normalized other vector and the real orthogonal unit vector give the actual attaining two-plane matrix.
  let e := NormedSpace.normalize a
  have he : ‖e‖=1 := NormedSpace.norm_normalize ha
  have hbe : inner ℝ b e=0 := by
    dsimp only [e,NormedSpace.normalize]
    rw [real_inner_smul_right,real_inner_comm a b,hab,mul_zero]
  refine ⟨planarMatrix b e 0 1 0,planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · have hp := planar_spectral_norm_le b e hb he hbe 0 1 (by norm_num)
    simpa only [neg_zero,chebyshev1.opNorm,Matrix.cstar_norm_def] using hp
  · have hbb : inner ℝ b b=1 := by rw [real_inner_self_eq_norm_sq,hb,one_pow]
    have heb : inner ℝ e b=0 := by rw [real_inner_comm];exact hbe
    rw [planarMatrix_action,hbb,heb]
    simp only [zero_mul,one_mul,add_zero,zero_add,zero_smul,one_smul]
    dsimp only [e,NormedSpace.normalize]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
end
end krylov.LinearAlgebra
