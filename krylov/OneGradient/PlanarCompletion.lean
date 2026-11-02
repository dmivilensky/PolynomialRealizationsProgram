import krylov.LinearAlgebra.PlanarWitness
import krylov.LinearAlgebra.CompletionWidth
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual planar spectral completions.
Use: construct original symmetric norm-budget hidden-entry scenarios in
arbitrary orthonormal physical planes, retaining every Schur boundary.
Source: true shifted positive-semidefinite norm test, planar quadratic
forms and the existing exact two-vector Bessel inequality.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Actual planar physical matrices have their exact scalar quadratic form.
Use: identify the real two endpoint Schur forms with the original matrix.
Article: main_krylov, thm:local(c), physical hidden-entry plane.
Proof: expand the actual planar operator action and commute the two real
inner products before collecting their true scalar coefficients. -/
theorem planarCompletion_quadratic (e h : EuclideanSpace ℝ (Fin n)) (y a g : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h y a g) v)=
      y*(inner ℝ e v)^2+2*a*inner ℝ e v*inner ℝ h v+g*(inner ℝ h v)^2 := by
  rw [planarMatrix_action]
  simp only [inner_add_right,real_inner_smul_right]
  rw [real_inner_comm e v,real_inner_comm h v]
  ring

/-- Genuine nonnegative shifted scalar forms on a physical orthonormal
plane give the original whole-matrix spectral norm bound, including
the orthogonal complement and singular endpoint blocks.
Use: actual hidden-entry witnesses obey the source symmetric spectral
budget, rather than only a sufficient coordinate certificate.
Article: main_krylov, thm:local(c), original physical Schur completions.
Proof: the genuine two-vector Bessel inequality bounds each planar
coordinate energy by the full physical energy. Both scalar endpoint
forms are therefore actual positive-semidefinite shifted whole matrices;
the proved true spectral norm equivalence gives the original budget. -/
theorem planarCompletion_norm_le (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (y a g : ℝ)
    (hminus : ∀ x z : ℝ,0≤(1-y)*x^2-2*a*x*z+(1-g)*z^2)
    (hplus : ∀ x z : ℝ,0≤(1+y)*x^2+2*a*x*z+(1+g)*z^2) :
    ‖planarMatrix e h y a g‖≤1 := by
  have hs : (planarMatrix e h y a g).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (planarMatrix_isSymm _ _ _ _ _)
  apply (spectral_norm_iff_shifted_posSemidef _ hs (by norm_num : (0 : ℝ)≤1)).mpr
  simp only [one_smul]
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((Matrix.isHermitian_one).sub hs)
    intro v
    rw [star_trivial,← Matrix.inner_toEuclideanCLM]
    simp only [map_sub,map_one,_root_.sub_apply,one_apply_eq_self,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [planarCompletion_quadratic]
    have hb := two_unit_bessel e h (WithLp.toLp 2 v) he hh heh
    have hm := hminus (inner ℝ e (WithLp.toLp 2 v)) (inner ℝ h (WithLp.toLp 2 v))
    nlinarith
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((Matrix.isHermitian_one).add hs)
    intro v
    rw [star_trivial,← Matrix.inner_toEuclideanCLM]
    simp only [map_add,map_one,_root_.add_apply,one_apply_eq_self,inner_add_right,real_inner_self_eq_norm_sq]
    rw [planarCompletion_quadratic]
    have hb := two_unit_bessel e h (WithLp.toLp 2 v) he hh heh
    have hm := hplus (inner ℝ e (WithLp.toLp 2 v)) (inner ℝ h (WithLp.toLp 2 v))
    nlinarith

/-- The true scalar Schur interval gives actual symmetric planar matrix
contractions on every physical orthonormal plane, for all its endpoints.
Use: the real two hidden endpoint adversaries and the centring algorithm
use genuine original spectral-budget matrices.
Article: main_krylov, thm:local(c), complete scalar hidden-entry interval.
Proof: complete both actual shifted scalar quadratic forms using the true
positive diagonal pivots 1±g. The genuine interval gives their remaining
nonnegative coefficients; the actual whole-matrix norm test applies. -/
theorem planarCompletion_schur_bound (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (y a g : ℝ)
    (hg : |g|<1) (hlo : -1+a^2/(1+g)≤ y) (hhi : y≤1-a^2/(1-g)) :
    ‖planarMatrix e h y a g‖≤1 := by
  have hgp : 0<1+g := by linarith [(abs_lt.mp hg).1]
  have hgm : 0<1-g := by linarith [(abs_lt.mp hg).2]
  apply planarCompletion_norm_le e h he hh heh y a g
  · intro x z
    have hc : 0≤1-y-a^2/(1-g) := by linarith
    have hp := add_nonneg (mul_nonneg hgm.le (sq_nonneg (z-a/(1-g)*x)))
      (mul_nonneg hc (sq_nonneg x))
    have heq : (1-y)*x^2-2*a*x*z+(1-g)*z^2=
        (1-g)*(z-a/(1-g)*x)^2+(1-y-a^2/(1-g))*x^2 := by field_simp;ring
    rw [heq]
    exact hp
  · intro x z
    have hc : 0≤1+y-a^2/(1+g) := by linarith
    have hp := add_nonneg (mul_nonneg hgp.le (sq_nonneg (z+a/(1+g)*x)))
      (mul_nonneg hc (sq_nonneg x))
    have heq : (1+y)*x^2+2*a*x*z+(1+g)*z^2=
        (1+g)*(z+a/(1+g)*x)^2+(1+y-a^2/(1+g))*x^2 := by field_simp;ring
    rw [heq]
    exact hp

end
end krylov.OneGradient
